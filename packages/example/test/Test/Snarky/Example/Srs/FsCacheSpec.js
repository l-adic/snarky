import { mkdtempSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

export const mkTmpDir = () => mkdtempSync(join(tmpdir(), "srs-fscache-"));
