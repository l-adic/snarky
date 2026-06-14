#!/usr/bin/env bash
#
# A browser MERGE peer — the serverless replacement for merge-server.mjs. It
# loads the static P2P site in a browser, joins a session in merge mode, and
# helps the mesh prove merge slots (computing public merges over proofs it
# receives + verifies; it never sees private witnesses). Same static site as the
# UI, so it keeps the wasm worker + COOP/COEP + trustless verify-on-receive.
#
#   tools/run_p2p_merge_peer.sh <SESSION> [BASE_URL] [TRANSPORT] [--headless]
#
#   SESSION     the shared session code (matches the base prover's #session=CODE)
#   BASE_URL    where the site is served (default http://localhost:5173)
#   TRANSPORT   trystero (cross-machine, default) | bc (same browser) | manual
#   --headless  run a headless Chrome instead of opening a visible browser
#               (for unattended/server use; no UI)
#
# By default the page opens in a REAL browser (Safari; override with
# BROWSER_APP="Google Chrome"). Cross-machine use needs Trystero (WebRTC over
# public Nostr relays). NOTE the wasm threads need a SECURE CONTEXT — http works
# on localhost, but a remote host must be https (e.g. `tailscale serve`); plain
# http to a remote host is not cross-origin isolated and proving will not start.
set -e

HEADLESS=0
POS=()
for a in "$@"; do
  case "$a" in
    --headless) HEADLESS=1 ;;
    *) POS+=("$a") ;;
  esac
done

SESSION="${POS[0]:?usage: run_p2p_merge_peer.sh <SESSION> [BASE_URL] [TRANSPORT] [--headless]}"
URL="${POS[1]:-http://localhost:5173}"
TRANSPORT="${POS[2]:-trystero}"
PAGE="$URL/#mode=merge&session=$SESSION&t=$TRANSPORT"

if [ "$HEADLESS" = "1" ]; then
  CHROME="${CHROME:-/Applications/Google Chrome.app/Contents/MacOS/Google Chrome}"
  PROFILE="$(mktemp -d)"
  trap 'rm -rf "$PROFILE"' EXIT
  echo "headless merge peer (Chrome) joining '$SESSION' over $TRANSPORT at $URL"
  exec "$CHROME" --headless=new --disable-gpu --no-first-run --no-default-browser-check \
    --user-data-dir="$PROFILE" "$PAGE"
else
  BROWSER="${BROWSER_APP:-Safari}"
  echo "opening merge peer in $BROWSER — session '$SESSION' over $TRANSPORT"
  echo "  $PAGE"
  exec open -a "$BROWSER" "$PAGE"
fi
