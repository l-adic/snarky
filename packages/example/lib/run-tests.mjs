// Test launcher for the example lib. `spago test` cannot run under the
// purs-backend-es backend (spago re-invokes the backend as a runner,
// which purs-backend-es rejects), so we execute the compiled test main
// directly — same pattern as terminal/run.mjs. Run from the REPO ROOT
// (srs-cache/ and kimchi-napi resolve there) after building the
// workspace: cd packages/example && npx spago build.
import { main } from "../output-es/Test.Example.Main/index.js";
main();
