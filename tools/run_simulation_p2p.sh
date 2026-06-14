#!/usr/bin/env bash
#
# Serverless P2P proving mesh for the example app. The site is fully static —
# browsers pointed at the same session collaborate over WebRTC to prove a block:
#
#   * BASE prover  (the data owner): generates a block and proves the per-tx
#     BASE proofs locally — private witnesses never leave the device — then
#     publishes the public proofs + statements to the mesh.
#   * MERGE prover (any helper, incl. a headless browser): proves ready merge
#     slots and publishes them. A headless merge peer replaces the old HTTP
#     merge server (see tools/run_p2p_merge_peer.sh).
#
# No coordinator: peers gossip a content-addressed job-board, self-assign the
# lowest ready slot, and verify every received proof before merging on it.
#
# Open http://localhost:5173/p2p.html and pick a role; share the session code
# (the #session=CODE hash) with the other browsers. Transports: BroadcastChannel
# (same browser, default for local demos), manual copy-paste SDP, or Trystero
# (cross-machine WebRTC over public Nostr relays) — choose via the `t=` hash
# (e.g. #mode=merge&session=demo&t=trystero).
set -e
cd "$(dirname "${BASH_SOURCE[0]}")/../packages/example/app"
npm run build:ps
echo "p2p mesh: open http://localhost:5173/p2p.html  (share #session=CODE across browsers)"
npx vite --config web/vite.config.mjs --host
