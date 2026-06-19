import { tmpdir } from "node:os";
import { join } from "node:path";

export const resolveSrsCacheDir = () =>
  process.env.SNARK_SRS_CACHE_DIR || join(tmpdir(), "snarky-srs-cache");
