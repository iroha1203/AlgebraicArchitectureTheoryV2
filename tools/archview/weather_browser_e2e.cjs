#!/usr/bin/env node
// Headless-Chrome smoke test for the weather-lens ArchView.
// Usage: node tools/archview/weather_browser_e2e.cjs <dir-with-view-model> <mode>
// Modes:
//   weather        default full assertions on the weather scene
//   flat           the flat toggle changes projection, not claims
//   reject-schema  tampered schema is rejected visibly (no silent empty scene)
//   missing        absent view model shows the empty shell, not an error page
//   sky            section clouds and agreement bridges match the view model
//   staircase      dossier frames render with provenance badges and gate rows
//   staircase-silent  absent dossier leaves the staircase silent, not an error
//   decoration-off turning decoration off must not change any claim
//   profile-switch a second view model replaces the scene; never composited

const fs = require("fs");
const http = require("http");
const os = require("os");
const path = require("path");
const { spawn } = require("child_process");
const WebSocket = require("../../website/node_modules/ws");

const root = path.resolve(process.argv[2] || ".tmp/archview-preview");
const mode = process.argv[3] || "weather";
const chromeCandidates = [
  process.env.CHROME_BIN,
  "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
  "/usr/bin/google-chrome",
  "/usr/bin/chromium",
].filter(Boolean);
const chrome = chromeCandidates.find((candidate) => fs.existsSync(candidate));
if (!chrome) throw new Error("Chrome/Chromium executable not found; set CHROME_BIN");

function serve(directory) {
  const server = http.createServer((request, response) => {
    const relative = decodeURIComponent(new URL(request.url, "http://localhost").pathname);
    const file = path.resolve(directory, "." + relative);
    if (!file.startsWith(path.resolve(directory) + path.sep)) {
      response.writeHead(403); response.end(); return;
    }
    fs.readFile(file, (error, data) => {
      if (error) { response.writeHead(404); response.end(); return; }
      response.writeHead(200); response.end(data);
    });
  });
  return new Promise((resolve) => server.listen(0, "127.0.0.1", () => resolve(server)));
}

function cdp(endpoint) {
  const socket = new WebSocket(endpoint);
  let nextId = 0;
  const pending = new Map();
  socket.on("message", (raw) => {
    const message = JSON.parse(raw.toString());
    if (message.id && pending.has(message.id)) {
      const item = pending.get(message.id); pending.delete(message.id);
      if (message.error) item.reject(new Error(JSON.stringify(message.error)));
      else item.resolve(message.result);
    }
  });
  return new Promise((resolve, reject) => {
    socket.once("open", () => resolve({
      send(method, params = {}) {
        const id = ++nextId;
        return new Promise((resolveMessage, rejectMessage) => {
          pending.set(id, { resolve: resolveMessage, reject: rejectMessage });
          socket.send(JSON.stringify({ id, method, params }));
        });
      },
      close() { socket.close(); },
    }));
    socket.once("error", reject);
  });
}

async function main() {
  let serveRoot = root;
  if (mode === "reject-schema") {
    serveRoot = fs.mkdtempSync(path.join(os.tmpdir(), "archview-weather-reject-"));
    fs.cpSync(root, serveRoot, { recursive: true });
    const vmPath = path.join(serveRoot, "archsig-measurement-view-model.json");
    const vm = JSON.parse(fs.readFileSync(vmPath, "utf8"));
    vm.schema = "archsig-measurement-view-model/v0.0.1";
    fs.writeFileSync(vmPath, JSON.stringify(vm, null, 2));
  } else if (mode === "missing") {
    serveRoot = fs.mkdtempSync(path.join(os.tmpdir(), "archview-weather-missing-"));
    fs.copyFileSync(path.join(root, "archview.html"), path.join(serveRoot, "archview.html"));
  } else if (mode === "staircase-silent") {
    serveRoot = fs.mkdtempSync(path.join(os.tmpdir(), "archview-weather-nostair-"));
    fs.copyFileSync(path.join(root, "archview.html"), path.join(serveRoot, "archview.html"));
    fs.copyFileSync(
      path.join(root, "archsig-measurement-view-model.json"),
      path.join(serveRoot, "archsig-measurement-view-model.json"));
  }
  const needsExpected = ["weather", "flat", "sky", "decoration-off", "profile-switch"].includes(mode);
  const expected = needsExpected
    ? JSON.parse(fs.readFileSync(path.join(serveRoot, "archsig-measurement-view-model.json"), "utf8"))
    : null;
  const expectedDossier = mode === "staircase"
    ? JSON.parse(fs.readFileSync(path.join(serveRoot, "archsig-diagnosis-dossier.json"), "utf8"))
    : null;
  const secondViewModel = mode === "profile-switch"
    ? JSON.parse(fs.readFileSync(path.join(serveRoot, "second-view-model.json"), "utf8"))
    : null;

  const server = await serve(serveRoot);
  const port = server.address().port;
  const profile = fs.mkdtempSync(path.join(os.tmpdir(), "archview-weather-profile-"));
  const browser = spawn(chrome, [
    "--headless=new", "--use-gl=swiftshader", "--enable-unsafe-swiftshader", "--no-sandbox", "--remote-debugging-port=0",
    "--user-data-dir=" + profile, "about:blank",
  ], { stdio: ["ignore", "pipe", "pipe"] });
  let stderr = "";
  browser.stderr.on("data", (chunk) => { stderr += chunk.toString(); });
  const deadline = Date.now() + 15000;
  let wsEndpoint;
  while (!wsEndpoint && Date.now() < deadline) {
    const match = stderr.match(/DevTools listening on (ws:\/\/[^\s]+)/);
    if (match) wsEndpoint = match[1];
    else await new Promise((resolve) => setTimeout(resolve, 100));
  }
  if (!wsEndpoint) throw new Error("Chrome DevTools endpoint not found: " + stderr);
  const debugBase = "http://127.0.0.1:" + new URL(wsEndpoint).port;
  const targets = await (await fetch(debugBase + "/json/list")).json();
  const target = targets.find((item) => item.type === "page");
  if (!target) throw new Error("Chrome page target not found");
  const page = await cdp(target.webSocketDebuggerUrl);
  await page.send("Page.enable");
  await page.send("Runtime.enable");
  await page.send("Page.navigate", { url: "http://127.0.0.1:" + port + "/archview.html" });

  const actions = {
    weather: "document.getElementById('scene-weather').click();",
    flat: "document.getElementById('scene-weather').click(); document.getElementById('btn-flat').click();",
    "reject-schema": "",
    missing: "",
    sky: "document.getElementById('scene-sky').click();",
    staircase: "document.getElementById('scene-staircase').click();",
    "staircase-silent": "document.getElementById('scene-staircase').click();",
    "decoration-off": "document.getElementById('scene-weather').click(); document.getElementById('btn-deco').click();",
    "profile-switch": `window.__archviewLoadDocument(${JSON.stringify(secondViewModel)}, 'second-profile');`,
  }[mode];
  const expression = `(() => { ${actions} return JSON.parse(JSON.stringify(window.__ARCHVIEW_STATE__ || {})); })()`;
  let value;
  const pageDeadline = Date.now() + 20000;
  do {
    const result = await page.send("Runtime.evaluate", { returnByValue: true, expression });
    value = result.result.value;
    const initialized = value && "scene" in value;
    let settled = initialized && (
      typeof value.rejected === "string" || value.schema !== null
      || (mode === "missing" && value.districts === 0));
    if (settled && mode === "staircase" && !value.staircase) settled = false;
    if (settled && mode === "profile-switch" && value.loadedProfiles.length < 2) settled = false;
    if (settled) break;
    await new Promise((resolve) => setTimeout(resolve, 500));
  } while (Date.now() < pageDeadline);

  if (mode === "reject-schema") {
    if (!value.rejected || !String(value.rejected).includes("expected schema")) {
      throw new Error("schema tamper was not rejected visibly: " + JSON.stringify(value));
    }
  } else if (mode === "missing") {
    if (value.rejected || value.districts !== 0) {
      throw new Error("missing view model must show the empty shell: " + JSON.stringify(value));
    }
  } else if (mode === "sky") {
    if (value.rejected) throw new Error("viewer rejected valid input: " + value.rejected);
    if (value.scene !== "sky") throw new Error("sky scene not active: " + JSON.stringify(value));
    const expectedSections = (expected.sectionValues || []).length;
    const expectedDistinct = new Set((expected.sectionValues || []).map((row) => row.value)).size;
    const expectedBridges = expected.edgeMismatch.filter((row) => row.status === "agreement_observed").length;
    if (value.sections !== expectedSections) throw new Error("section cloud count mismatch: " + JSON.stringify(value));
    if (value.distinctSectionValues !== expectedDistinct) throw new Error("distinct section value mismatch: " + JSON.stringify(value));
    if (value.agreementBridges !== expectedBridges) throw new Error("agreement bridge count mismatch: " + JSON.stringify(value));
  } else if (mode === "staircase") {
    if (value.rejected) throw new Error("viewer rejected valid input: " + value.rejected);
    if (!value.staircase) throw new Error("dossier was not loaded: " + JSON.stringify(value));
    if (value.staircase.frames !== expectedDossier.frames.length) {
      throw new Error("staircase frame count mismatch: " + JSON.stringify(value));
    }
    const expectedProv = expectedDossier.frames.map((frame) => frame.stateProvenance);
    if (JSON.stringify(value.staircase.provenances) !== JSON.stringify(expectedProv)) {
      throw new Error("provenance badges do not match the dossier: " + JSON.stringify(value));
    }
    if (value.staircase.gateDecisions.length !== (expectedDossier.gateReports || []).length) {
      throw new Error("gate rows do not match the dossier: " + JSON.stringify(value));
    }
  } else if (mode === "staircase-silent") {
    if (value.rejected) throw new Error("absent dossier must stay silent, not error: " + JSON.stringify(value));
    if (value.staircase !== null) throw new Error("staircase must be silent without a dossier: " + JSON.stringify(value));
  } else if (mode === "decoration-off") {
    if (value.rejected) throw new Error("viewer rejected valid input: " + value.rejected);
    if (value.decoration !== false) throw new Error("decoration toggle did not disengage: " + JSON.stringify(value));
    const expectedFronts = expected.edgeMismatch.filter((row) => row.status === "mismatch_observed").length;
    if (value.fronts !== expectedFronts || value.districts !== expected.complex.vertices.length
      || !!(value.circulationWarning && value.circulationWarning.present) !== (expected.classSupport.classNonzero === true)) {
      throw new Error("decoration OFF changed a claim: " + JSON.stringify(value));
    }
  } else if (mode === "profile-switch") {
    if (value.rejected) throw new Error("viewer rejected valid input: " + value.rejected);
    if (value.loadedProfiles.length !== 2) throw new Error("two profiles must be registered: " + JSON.stringify(value));
    if (value.districts !== secondViewModel.complex.vertices.length) {
      throw new Error("second view model must replace (not composite) the scene: " + JSON.stringify(value));
    }
    if (!String(value.activeProfile).includes((secondViewModel.profiles[0] || {}).profileRef || "")) {
      throw new Error("active profile badge mismatch: " + JSON.stringify(value));
    }
  } else {
    if (value.rejected) throw new Error("viewer rejected valid input: " + value.rejected);
    if (value.schema !== "archsig-measurement-view-model/v0.5.4") {
      throw new Error("schema not accepted: " + JSON.stringify(value));
    }
    const expectedFronts = expected.edgeMismatch.filter((row) => row.status === "mismatch_observed").length;
    const expectedUnsupplied = expected.edgeMismatch.filter((row) => row.status === "witness_not_supplied").length;
    if (value.districts !== expected.complex.vertices.length) throw new Error("district count mismatch: " + JSON.stringify(value));
    if (value.roads !== expected.complex.edges.length) throw new Error("road count mismatch: " + JSON.stringify(value));
    if (value.triples !== (expected.complex.triples || []).length) throw new Error("triple count mismatch: " + JSON.stringify(value));
    if (value.fronts !== expectedFronts) throw new Error("front count mismatch: " + JSON.stringify(value));
    if (value.unsuppliedWitness !== expectedUnsupplied) throw new Error("unsupplied witness count mismatch: " + JSON.stringify(value));
    const expectNonzero = expected.classSupport && expected.classSupport.classNonzero === true;
    if (!!(value.circulationWarning && value.circulationWarning.present) !== expectNonzero) {
      throw new Error("circulation warning presence must equal measured classNonzero: " + JSON.stringify(value));
    }
    if (value.circulationWarning && (value.circulationWarning.undirected !== true || value.circulationWarning.rotationAnimated !== false)) {
      throw new Error("F2 circulation must stay undirected and never rotate: " + JSON.stringify(value));
    }
    if (value.stations !== expected.complex.vertices.length) {
      throw new Error("every complex vertex must have coverage rows in this fixture: " + JSON.stringify(value));
    }
    if (mode === "flat" && value.flat !== true) throw new Error("flat toggle did not engage: " + JSON.stringify(value));
    if (mode === "weather" && value.flat !== false) throw new Error("default must be the tilted 3D camera: " + JSON.stringify(value));
    if (value.scene !== "weather") throw new Error("weather scene not active: " + JSON.stringify(value));
  }
  console.log(JSON.stringify(value));
  page.close(); browser.kill(); server.close();
}

main().catch((error) => { console.error(error.message || error); process.exit(1); });
