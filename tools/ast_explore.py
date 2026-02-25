#!/usr/bin/env python3
"""Explore tree-sitter AST structure for OCaml and PureScript files."""

import sys
import subprocess
from tree_sitter_language_pack import get_parser

PPX_JANE = "/home/martyall/.opam/mina/lib/ppx_jane/ppx.exe"

def expand_ppx(filepath):
    """Run ppx_jane to expand PPX extensions in OCaml source."""
    result = subprocess.run([PPX_JANE, filepath], capture_output=True, text=True)
    if result.returncode != 0:
        print(f"ppx_jane failed: {result.stderr}", file=sys.stderr)
        return None
    return result.stdout

def print_tree(node, indent=0, max_depth=6, source=None):
    """Print tree-sitter AST with optional source snippets."""
    if indent > max_depth:
        return
    prefix = "  " * indent
    text = ""
    if source and node.child_count == 0:
        snippet = source[node.start_byte:node.end_byte].decode('utf-8', errors='replace')
        if len(snippet) > 60:
            snippet = snippet[:57] + "..."
        text = f' "{snippet}"'
    elif source and node.type in ('value_name', 'variable', 'type_constructor_identifier',
                                   'constructor_name', 'label_name', 'module_name',
                                   'pat_name', 'exp_name', 'qualified_module'):
        snippet = source[node.start_byte:node.end_byte].decode('utf-8', errors='replace')
        if len(snippet) > 80:
            snippet = snippet[:77] + "..."
        text = f' "{snippet}"'

    line = node.start_point[0] + 1
    print(f"{prefix}{node.type} [L{line}]{text}")
    for child in node.children:
        print_tree(child, indent + 1, max_depth, source)

def explore_ocaml(filepath, function_name=None, max_depth=6):
    """Parse OCaml file (after PPX expansion) and show AST."""
    print(f"=== OCaml: {filepath} (PPX-expanded) ===")
    expanded = expand_ppx(filepath)
    if not expanded:
        return
    source = expanded.encode('utf-8')
    parser = get_parser('ocaml')
    tree = parser.parse(source)

    if tree.root_node.has_error:
        print("WARNING: Parse errors detected!")

    if function_name:
        # Find the specific function
        found = find_function_ocaml(tree.root_node, source, function_name)
        if found:
            print(f"\nFound function '{function_name}':")
            print_tree(found, max_depth=max_depth, source=source)
        else:
            print(f"Function '{function_name}' not found")
    else:
        print_tree(tree.root_node, max_depth=max_depth, source=source)

def find_function_ocaml(node, source, name):
    """Find a let binding by name in OCaml AST."""
    if node.type == 'value_definition':
        for child in node.children:
            if child.type == 'let_binding':
                for c in child.children:
                    if c.type in ('value_name', 'value_pattern'):
                        text = source[c.start_byte:c.end_byte].decode('utf-8')
                        if text == name:
                            return node
    for child in node.children:
        result = find_function_ocaml(child, source, name)
        if result:
            return result
    return None

def explore_purescript(filepath, function_name=None, max_depth=6):
    """Parse PureScript file and show AST."""
    print(f"=== PureScript: {filepath} ===")
    with open(filepath, 'rb') as f:
        source = f.read()
    parser = get_parser('purescript')
    tree = parser.parse(source)

    if tree.root_node.has_error:
        print("WARNING: Parse errors detected!")

    if function_name:
        found = find_function_purescript(tree.root_node, source, function_name)
        if found:
            print(f"\nFound function '{function_name}':")
            print_tree(found, max_depth=max_depth, source=source)
        else:
            print(f"Function '{function_name}' not found")
    else:
        print_tree(tree.root_node, max_depth=max_depth, source=source)

def find_function_purescript(node, source, name):
    """Find a function declaration by name in PureScript AST."""
    if node.type == 'function':
        for child in node.children:
            if child.type == 'variable':
                text = source[child.start_byte:child.end_byte].decode('utf-8')
                if text == name:
                    return node
    for child in node.children:
        result = find_function_purescript(child, source, name)
        if result:
            return result
    return None

if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument('lang', choices=['ocaml', 'purescript', 'ps'])
    p.add_argument('filepath')
    p.add_argument('--function', '-f', help='Find specific function')
    p.add_argument('--depth', '-d', type=int, default=6)
    args = p.parse_args()

    if args.lang == 'ocaml':
        explore_ocaml(args.filepath, args.function, args.depth)
    else:
        explore_purescript(args.filepath, args.function, args.depth)
