// Loads the platform-appropriate kimchi-napi .node native module.
// The .node file is produced by `npm run build` (build.sh in this
// directory), which invokes `cargo build -p kimchi-napi --release`
// inside the in-tree proof-systems submodule and copies the resulting
// cdylib here under the platform-suffixed name below.

const { platform, arch } = process;
let file = null;

switch (platform) {
  case "linux":
    if (arch === "x64") file = "./kimchi-napi.linux-x64-gnu.node";
    else if (arch === "arm64") file = "./kimchi-napi.linux-arm64-gnu.node";
    break;
  case "darwin":
    if (arch === "x64") file = "./kimchi-napi.darwin-x64.node";
    else if (arch === "arm64") file = "./kimchi-napi.darwin-arm64.node";
    break;
}

if (file === null) {
  throw new Error(
    `kimchi-napi: unsupported host ${platform}-${arch}. Add a case in index.js and build.sh for this platform.`,
  );
}

module.exports = require(file);
