#!/usr/bin/env node

const assert = require("assert");
const fs = require("fs");
const os = require("os");
const path = require("path");

const repository = path.resolve(__dirname, "../..");
const toolRoot = path.join(repository, "tools/archview");

function filesBelow(directory, prefix = "") {
  return fs.readdirSync(directory, { withFileTypes: true }).flatMap((entry) => {
    const relative = path.join(prefix, entry.name);
    return entry.isDirectory() ? filesBelow(path.join(directory, entry.name), relative) : [relative];
  }).sort();
}

const assetFiles = filesBelow(path.join(toolRoot, "archview-assets"));
const websiteConfig = fs.readFileSync(path.join(repository, "website/eleventy.config.js"), "utf8");
assert.ok(websiteConfig.includes('"../tools/archview/archview.html": "archsig/archview/viewer/archview.html"'), "website must publish the tool ArchView entry directly");
assert.ok(websiteConfig.includes('"../tools/archview/archview-assets": "archsig/archview/viewer/archview-assets"'), "website must publish the tool ArchView assets directly");
assert.ok(!fs.existsSync(path.join(repository, "website/src/archsig/archview/viewer")), "website must not keep a second ArchView runtime copy");

const sourcePath = path.join(repository, "docs/reports/train_ticket_dogfooding/evidence/fullbuild/archmap.json");
const fixturePath = path.join(toolRoot, "archview-assets/fixtures/train-ticket.archmap.json");
const source = JSON.parse(fs.readFileSync(sourcePath, "utf8"));
const expected = structuredClone(source);
expected.schema = "archmap/v0.5.4";
for (const atom of expected.atoms) {
  if (atom.predicate === null) delete atom.predicate;
  if (atom.object === null) delete atom.object;
}
const fixture = JSON.parse(fs.readFileSync(fixturePath, "utf8"));
assert.deepStrictEqual(fixture, expected, "train-ticket fixture must remain a lossless v0.5.4 normalization of the committed fullbuild evidence");
assert.deepStrictEqual({ sources: Object.keys(fixture.sources).length, atoms: fixture.atoms.length, contexts: fixture.contexts.length, covers: fixture.covers.length }, { sources: 440, atoms: 2118, contexts: 43, covers: 3 });

const releaseWorkflow = fs.readFileSync(path.join(repository, ".github/workflows/archsig-release.yml"), "utf8");
for (const required of ["cp -R tools/archview/archview-assets package/archview/archview-assets", "package/archview/archview-assets/app.js", "package/archview/archview-assets/fixtures/train-ticket.archmap.json"]) assert.ok(releaseWorkflow.includes(required), `release bundle contract is missing ${required}`);

const releaseRoot = fs.mkdtempSync(path.join(os.tmpdir(), "archview-release-bundle-"));
fs.copyFileSync(path.join(toolRoot, "archview.html"), path.join(releaseRoot, "archview.html"));
fs.copyFileSync(path.join(toolRoot, "README.md"), path.join(releaseRoot, "README.md"));
fs.cpSync(path.join(toolRoot, "archview-assets"), path.join(releaseRoot, "archview-assets"), { recursive: true });
assert.ok(fs.statSync(path.join(releaseRoot, "archview.html")).size > 0);
assert.ok(fs.statSync(path.join(releaseRoot, "archview-assets/app.js")).size > 0);
assert.ok(fs.statSync(path.join(releaseRoot, "archview-assets/fixtures/train-ticket.archmap.json")).size > 0);

console.log(JSON.stringify({ publicFiles: assetFiles.length + 1, fixtureCounts: { sources: 440, atoms: 2118, contexts: 43, covers: 3 }, website: "source-of-truth passthrough", release: "complete" }));
