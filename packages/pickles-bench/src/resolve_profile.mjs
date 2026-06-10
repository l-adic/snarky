
import fs from "fs";
import path from "path";

/**
 * Resolver to map JS stack frames back to PureScript source using corefn.json
 */
class CoreFnResolver {
  constructor() {
    this.moduleMap = new Map(); // jsPath -> corefnData
  }

  async loadAll(outputDir) {
    if (!fs.existsSync(outputDir)) {
        console.error(`Output directory not found: ${outputDir}`);
        return;
    }
    const modules = fs.readdirSync(outputDir);
    for (const mod of modules) {
      const corefnPath = path.join(outputDir, mod, "corefn.json");
      if (fs.existsSync(corefnPath)) {
        try {
            const data = JSON.parse(fs.readFileSync(corefnPath, "utf-8"));
            this.moduleMap.set(mod, data);
        } catch (e) {
            console.error(`Failed to parse ${corefnPath}: ${e.message}`);
        }
      }
    }
    console.log(`Loaded ${this.moduleMap.size} modules from ${outputDir}`);
  }

  resolveFrame(functionName, url) {
    if (!url) return { functionName, source: "native" };

    // Support both output/ and output-es/
    const match = url.match(/output(-es)?\/([^/]+)\/index\.js/);
    if (!match) return { functionName, source: url };

    const modName = match[2];
    const corefn = this.moduleMap.get(modName);
    if (!corefn) return { functionName: `${modName}.${functionName}`, source: url };

    return {
      functionName: `${corefn.moduleName.join(".")}.${functionName}`,
      source: corefn.modulePath
    };
  }
}

/**
 * Main Profile Processor
 */
export async function processProfile(cpuProfilePath, outputDir, threshold = 0) {
  if (!fs.existsSync(cpuProfilePath)) {
    console.error(`Profile not found: ${cpuProfilePath}`);
    return;
  }

  const profile = JSON.parse(fs.readFileSync(cpuProfilePath, "utf-8"));
  const resolver = new CoreFnResolver();
  await resolver.loadAll(outputDir);

  const nodes = profile.nodes;
  const summarized = new Map();
  let totalHits = 0;

  for (const node of nodes) {
    const frame = node.callFrame;
    const resolved = resolver.resolveFrame(frame.functionName, frame.url);
    const key = `${resolved.functionName} (${resolved.source})`;
    
    const hits = node.hitCount || 0;
    summarized.set(key, (summarized.get(key) || 0) + hits);
    totalHits += hits;
  }

  const results = [...summarized.entries()]
    .map(([name, hits]) => ({ name, hits, percent: (hits / totalHits * 100).toFixed(2) }))
    .filter(r => r.hits > 0 && r.percent >= threshold)
    .sort((a, b) => b.hits - a.hits);

  console.log("\n--- Top JS Functions (Source Resolved) ---");
  for (const { name, hits, percent } of results.slice(0, 30)) {
    console.log(`${hits.toString().padStart(8)} hits (${percent.padStart(5)}%) : ${name}`);
  }
}

// Simple flag parser
const args = process.argv.slice(2);
let profile = null;
let outputDir = "packages/pickles-bench/output";
let threshold = 0;

for (let i = 0; i < args.length; i++) {
    if (args[i] === "--profile") profile = args[++i];
    else if (args[i] === "--output-dir") outputDir = args[++i];
    else if (args[i] === "--threshold") threshold = parseFloat(args[++i]);
}

if (profile) {
    processProfile(profile, outputDir, threshold);
} else {
    console.log("Usage: node resolve_profile.js --profile <path> [--output-dir <path>] [--threshold <0-100>]");
}
