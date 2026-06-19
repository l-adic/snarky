import "./styles.css";
// P2P proving UI entry. The app is PureScript (Snarky.Example.Web.P2P.Main); the
// only JS→PS call is `main()` (its type is `Effect Unit`). Everything the app
// needs from JS — the worker factory, the transport, the URL hash — it pulls in
// itself through `foreign import`s (see src/P2P/Main.js).
import { main } from "../output-es/Snarky.Example.Web.P2P.Main/index.js";

main();
