#!/usr/bin/env bash
#
# P2P star worker-pool launcher (web only). Three modes:
#
#   tools/run_p2p_pool.sh             # dev server (vite, COOP/COEP, --host)
#                                     # open /index.html, pick coordinator | peer
#   tools/run_p2p_pool.sh --build     # production bundle -> web/dist
#   tools/run_p2p_pool.sh --test [N]  # headless Milestone A: build, preview,
#                                     # and drive 1 coordinator + N peers (default
#                                     # 2) over BroadcastChannel to a verified root
#   tools/run_p2p_pool.sh --webrtc    # headless Milestone B: build, preview, and
#                                     # drive 1 coordinator + 1 peer over a REAL
#                                     # WebRTC data channel (manual SDP) to a
#                                     # verified root
#
# A coordinator (block producer) farms every base + merge job to the connected
# worker peers and verifies the root; each peer is a full-core wasm prover.
set -e
cd "$(dirname "${BASH_SOURCE[0]}")/.."
APP=packages/example/app

case "${1:-}" in
  --build)
    npm run bundle -w example-app
    ;;
  --test|--webrtc)
    npm run bundle -w example-app
    npx vite preview --config "$APP/web/vite.config.mjs" --port 4173 &
    PREVIEW=$!
    trap 'kill $PREVIEW 2>/dev/null || true' EXIT
    # wait for the preview server to answer
    until curl -sf -o /dev/null http://localhost:4173/index.html; do sleep 1; done
    if [ "$1" = "--webrtc" ]; then
      URL=http://localhost:4173 node tools/p2p_pool_webrtc_test.mjs
    else
      URL=http://localhost:4173 node tools/p2p_pool_test.mjs "${2:-2}"
    fi
    ;;
  *)
    cd "$APP" && npm run p2p
    ;;
esac
