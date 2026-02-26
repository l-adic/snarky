#!/usr/bin/env python3
"""
Extract sequential operations from OCaml and PureScript circuit code.

For OCaml (after PPX expansion):
  - Extracts top-level let bindings and statements in function bodies
  - Shows the sequence of operations that build the constraint system

For PureScript:
  - Extracts bind patterns (x <- ...) and bare statements from do blocks
  - Shows the sequence of monadic operations

Both produce a flat list of steps for side-by-side comparison.
"""

import sys
import json
import subprocess
import argparse
from dataclasses import dataclass, asdict
from typing import Optional
from tree_sitter_language_pack import get_parser

PPX_JANE = "/home/martyall/.opam/mina/lib/ppx_jane/ppx.exe"


@dataclass
class Step:
    """A single operation in a circuit function."""
    line: int
    variable: Optional[str]  # bound variable name, if any
    source: str              # raw source text (first line or truncated)


def get_text(node, source):
    return source[node.start_byte:node.end_byte].decode('utf-8', errors='replace')


def first_line(s, max_len=120):
    line = s.split('\n')[0].strip()
    return line[:max_len] + '...' if len(line) > max_len else line


# ============================================================
# OCaml: extract let-binding chain from a function body
# ============================================================

def expand_ppx(filepath):
    result = subprocess.run([PPX_JANE, filepath], capture_output=True, text=True)
    if result.returncode != 0:
        print(f"ppx_jane error: {result.stderr}", file=sys.stderr)
        sys.exit(1)
    return result.stdout


def find_ocaml_function(node, source, name):
    """Find a value_definition whose let_binding has the given name."""
    if node.type == 'value_definition':
        for child in node.children:
            if child.type == 'let_binding':
                for c in child.children:
                    if c.type in ('value_name', 'value_pattern') and get_text(c, source) == name:
                        return node
    for child in node.children:
        result = find_ocaml_function(child, source, name)
        if result:
            return result
    return None


def extract_ocaml_let_chain(node, source, depth=0):
    """
    Recursively extract the chain of let bindings from an OCaml expression.

    In circuit code, the body of a function is typically:
      let x1 = ... in
      let x2 = ... in
      ...
      final_expr

    We extract each let binding as a step, showing what variable is bound
    and the first line of its RHS.
    """
    steps = []

    if node.type == 'let_expression':
        # Structure: value_definition, in, <body_expression>
        # value_definition contains: 'let', let_binding
        for child in node.children:
            if child.type == 'value_definition':
                for binding in child.children:
                    if binding.type == 'let_binding':
                        var_name = None
                        rhs_text = None
                        saw_eq = False
                        for c in binding.children:
                            if not saw_eq:
                                if c.type in ('value_name', 'value_pattern'):
                                    var_name = get_text(c, source)
                                elif c.type in ('tuple_pattern', 'record_pattern', 'parenthesized_pattern'):
                                    var_name = get_text(c, source).replace('\n', ' ')
                                elif get_text(c, source).strip() == '=':
                                    saw_eq = True
                            elif rhs_text is None:
                                rhs_text = get_text(c, source)

                        if var_name:
                            steps.append(Step(
                                line=child.start_point[0] + 1,
                                variable=var_name,
                                source=first_line(rhs_text) if rhs_text else "?"
                            ))

        # Continue into the body (expression after 'in')
        found_in = False
        for child in node.children:
            if child.type == 'in':
                found_in = True
            elif found_in:
                steps.extend(extract_ocaml_let_chain(child, source, depth + 1))
                break

    elif node.type == 'sequence_expression':
        # Semicolon-separated statements
        for child in node.children:
            text = get_text(child, source).strip()
            if text == ';':
                continue
            if child.type == 'let_expression':
                steps.extend(extract_ocaml_let_chain(child, source, depth))
            elif child.type == 'parenthesized_expression':
                # Unwrap parens
                for c in child.children:
                    if c.type not in ('(', ')'):
                        steps.extend(extract_ocaml_let_chain(c, source, depth))
            else:
                steps.append(Step(
                    line=child.start_point[0] + 1,
                    variable=None,
                    source=first_line(get_text(child, source))
                ))

    elif node.type == 'parenthesized_expression':
        for child in node.children:
            if child.type not in ('(', ')'):
                steps.extend(extract_ocaml_let_chain(child, source, depth))

    elif node.type == 'let_open_expression':
        # let open Module in <body>
        found_in = False
        for child in node.children:
            if child.type == 'in':
                found_in = True
            elif found_in:
                steps.extend(extract_ocaml_let_chain(child, source, depth))
                break

    elif node.type == 'application_expression':
        text = get_text(node, source)
        # Check if this wraps a lambda (e.g. with_label "foo" (fun () -> body))
        # If so, descend into the lambda body
        lambda_body = find_lambda_body(node, source)
        if lambda_body:
            steps.append(Step(
                line=node.start_point[0] + 1,
                variable=None,
                source=first_line(text)
            ))
            steps.extend(extract_ocaml_let_chain(lambda_body, source, depth + 1))
        else:
            steps.append(Step(
                line=node.start_point[0] + 1,
                variable=None,
                source=first_line(text)
            ))

    elif node.type == 'fun_expression':
        # Lambda — extract its body
        body = get_lambda_body(node, source)
        if body:
            steps.extend(extract_ocaml_let_chain(body, source, depth))

    elif node.type in ('product_expression', 'match_expression', 'if_expression'):
        # Final expression - return value
        steps.append(Step(
            line=node.start_point[0] + 1,
            variable='[return]',
            source=first_line(get_text(node, source))
        ))

    return steps


def find_lambda_body(node, source):
    """If this application_expression contains a lambda as the last argument, return its body."""
    children = list(node.children)
    for child in reversed(children):
        if child.type == 'fun_expression':
            return get_lambda_body(child, source)
        elif child.type == 'parenthesized_expression':
            for c in child.children:
                if c.type == 'fun_expression':
                    return get_lambda_body(c, source)
    return None


def get_lambda_body(fun_node, source):
    """Get the body expression from a fun_expression (fun args -> body)."""
    saw_arrow = False
    for child in fun_node.children:
        if get_text(child, source).strip() == '->':
            saw_arrow = True
        elif saw_arrow:
            return child
    return None


def get_ocaml_function_body(func_node, source):
    """Get the body expression of an OCaml function (after the = sign)."""
    for child in func_node.children:
        if child.type == 'let_binding':
            saw_eq = False
            for c in child.children:
                if get_text(c, source).strip() == '=':
                    saw_eq = True
                elif saw_eq:
                    return c
    return None


# ============================================================
# PureScript: extract do-block statements
# ============================================================

def find_ps_function(node, source, name):
    """Find a function/value declaration by name."""
    if node.type == 'function':
        for child in node.children:
            if child.type == 'variable' and get_text(child, source) == name:
                return node
    for child in node.children:
        result = find_ps_function(child, source, name)
        if result:
            return result
    return None


def find_do_block(node, source):
    """Find the first exp_do node in a subtree."""
    if node.type == 'exp_do':
        return node
    for child in node.children:
        result = find_do_block(child, source)
        if result:
            return result
    return None


def extract_ps_do_steps(node, source):
    """Extract steps from a PureScript do block."""
    steps = []

    if node.type != 'exp_do':
        do_node = find_do_block(node, source)
        if not do_node:
            return steps
        node = do_node

    for child in node.children:
        if child.type == 'statement':
            step = extract_ps_statement(child, source)
            if step:
                steps.append(step)

    return steps


def extract_ps_statement(node, source):
    """Extract a single step from a do-block statement."""
    text = get_text(node, source)

    for child in node.children:
        if child.type == 'bind_pattern':
            # x <- action
            var_parts = []
            rhs_text = None
            found_arrow = False
            for c in child.children:
                t = get_text(c, source)
                if t == '<-':
                    found_arrow = True
                elif not found_arrow:
                    var_parts.append(t)
                else:
                    rhs_text = get_text(c, source)
                    break

            var_name = ' '.join(var_parts).strip()
            return Step(
                line=node.start_point[0] + 1,
                variable=var_name if var_name else None,
                source=first_line(rhs_text) if rhs_text else first_line(text)
            )

        elif child.type == 'let':
            # let x = ...
            inner_text = get_text(child, source)
            # Try to extract variable name
            var_name = None
            for c in child.children:
                if c.type in ('function', 'value_declaration'):
                    for cc in c.children:
                        if cc.type == 'variable':
                            var_name = get_text(cc, source)
                            break
                    break
            return Step(
                line=node.start_point[0] + 1,
                variable=var_name,
                source=first_line(inner_text)
            )

    # Bare expression
    return Step(
        line=node.start_point[0] + 1,
        variable=None,
        source=first_line(text)
    )


# ============================================================
# Output
# ============================================================

def print_steps(steps, label, as_json=False):
    if as_json:
        print(json.dumps([asdict(s) for s in steps], indent=2))
        return

    print(f"\n=== {label} ({len(steps)} steps) ===\n")
    for i, s in enumerate(steps):
        var = s.variable or '_'
        print(f"  {i:3d}  L{s.line:4d}  {var:30s}  {s.source}")


def print_side_by_side(ocaml_steps, ps_steps):
    """Print both sequences side by side for manual comparison."""
    print(f"\n{'='*120}")
    print(f"  OCaml ({len(ocaml_steps)} steps) vs PureScript ({len(ps_steps)} steps)")
    print(f"{'='*120}\n")

    max_len = max(len(ocaml_steps), len(ps_steps))

    for i in range(max_len):
        o = ocaml_steps[i] if i < len(ocaml_steps) else None
        p = ps_steps[i] if i < len(ps_steps) else None

        o_var = (o.variable or '_')[:20] if o else ''
        p_var = (p.variable or '_')[:20] if p else ''
        o_src = o.source[:50] if o else ''
        p_src = p.source[:50] if p else ''
        o_line = f"L{o.line}" if o else ''
        p_line = f"L{p.line}" if p else ''

        print(f"  {i:3d}  {o_line:>5s} {o_var:20s} {o_src:50s}  |  {p_line:>5s} {p_var:20s} {p_src}")


# ============================================================
# Main
# ============================================================

def main():
    p = argparse.ArgumentParser(description='Extract circuit operation sequences')
    sub = p.add_subparsers(dest='cmd')

    ocaml_p = sub.add_parser('ocaml', help='Extract from OCaml file')
    ocaml_p.add_argument('filepath')
    ocaml_p.add_argument('-f', '--function', required=True)
    ocaml_p.add_argument('--json', action='store_true')

    ps_p = sub.add_parser('ps', help='Extract from PureScript file')
    ps_p.add_argument('filepath')
    ps_p.add_argument('-f', '--function', required=True)
    ps_p.add_argument('--json', action='store_true')

    cmp_p = sub.add_parser('compare', help='Side-by-side comparison')
    cmp_p.add_argument('ocaml_file')
    cmp_p.add_argument('ocaml_function')
    cmp_p.add_argument('ps_file')
    cmp_p.add_argument('ps_function')

    args = p.parse_args()

    if args.cmd == 'ocaml':
        expanded = expand_ppx(args.filepath)
        source = expanded.encode('utf-8')
        parser = get_parser('ocaml')
        tree = parser.parse(source)
        func = find_ocaml_function(tree.root_node, source, args.function)
        if not func:
            print(f"Function '{args.function}' not found", file=sys.stderr)
            sys.exit(1)
        body = get_ocaml_function_body(func, source)
        if not body:
            print(f"Could not find body of '{args.function}'", file=sys.stderr)
            sys.exit(1)
        steps = extract_ocaml_let_chain(body, source)
        print_steps(steps, f"OCaml: {args.function}", args.json)

    elif args.cmd == 'ps':
        with open(args.filepath, 'rb') as f:
            source = f.read()
        parser = get_parser('purescript')
        tree = parser.parse(source)
        func = find_ps_function(tree.root_node, source, args.function)
        if not func:
            print(f"Function '{args.function}' not found", file=sys.stderr)
            sys.exit(1)
        steps = extract_ps_do_steps(func, source)
        print_steps(steps, f"PureScript: {args.function}", args.json)

    elif args.cmd == 'compare':
        # OCaml
        expanded = expand_ppx(args.ocaml_file)
        ocaml_source = expanded.encode('utf-8')
        ocaml_parser = get_parser('ocaml')
        ocaml_tree = ocaml_parser.parse(ocaml_source)
        ocaml_func = find_ocaml_function(ocaml_tree.root_node, ocaml_source, args.ocaml_function)
        if not ocaml_func:
            print(f"OCaml function '{args.ocaml_function}' not found", file=sys.stderr)
            sys.exit(1)
        body = get_ocaml_function_body(ocaml_func, ocaml_source)
        ocaml_steps = extract_ocaml_let_chain(body, ocaml_source) if body else []

        # PureScript
        with open(args.ps_file, 'rb') as f:
            ps_source = f.read()
        ps_parser = get_parser('purescript')
        ps_tree = ps_parser.parse(ps_source)
        ps_func = find_ps_function(ps_tree.root_node, ps_source, args.ps_function)
        if not ps_func:
            print(f"PureScript function '{args.ps_function}' not found", file=sys.stderr)
            sys.exit(1)
        ps_steps = extract_ps_do_steps(ps_func, ps_source)

        print_steps(ocaml_steps, f"OCaml: {args.ocaml_function}")
        print_steps(ps_steps, f"PureScript: {args.ps_function}")
        print_side_by_side(ocaml_steps, ps_steps)

    else:
        p.print_help()


if __name__ == '__main__':
    main()
