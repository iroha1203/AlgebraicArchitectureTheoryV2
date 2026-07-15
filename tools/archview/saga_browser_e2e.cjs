#!/usr/bin/env node

const fs = require("fs");
const http = require("http");
const os = require("os");
const path = require("path");
const { spawn } = require("child_process");
const WebSocket = require("../../website/node_modules/ws");

const root = path.resolve(process.argv[2] || ".tmp/archview-preview");
const mode = process.argv[3] || "saga";
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
  if (mode === "mismatch") {
    serveRoot = fs.mkdtempSync(path.join(os.tmpdir(), "archview-saga-mismatch-"));
    fs.cpSync(root, serveRoot, { recursive: true });
    const gatePath = path.join(serveRoot, "archsig-gate-report.json");
    const gate = JSON.parse(fs.readFileSync(gatePath, "utf8"));
    gate.inputDigests.measurementPacket.sha256 = "0".repeat(64);
    fs.writeFileSync(gatePath, JSON.stringify(gate, null, 2));
  } else if (mode === "malformed" || mode === "missing-boundary") {
    serveRoot = fs.mkdtempSync(path.join(os.tmpdir(), `archview-saga-${mode}-`));
    fs.cpSync(root, serveRoot, { recursive: true });
    const gatePath = path.join(serveRoot, "archsig-gate-report.json");
    if (mode === "malformed") {
      fs.writeFileSync(gatePath, "{ malformed gate report");
    } else {
      const gate = JSON.parse(fs.readFileSync(gatePath, "utf8"));
      const row = gate.ruleOutcomes.find((outcome) => outcome.appliedMapping?.length)?.appliedMapping[0];
      delete row.boundaryOverrideApplied;
      fs.writeFileSync(gatePath, JSON.stringify(gate, null, 2));
    }
  }
  const server = await serve(serveRoot);
  const port = server.address().port;
  const profile = fs.mkdtempSync(path.join(os.tmpdir(), "archview-saga-"));
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
  const expression = "(() => {" +
    "[...document.querySelectorAll('#scene-buttons .scene-btn')].find((button) => button.textContent.includes('SAGA diagnostic staircase'))?.click();" +
    "return {saga: window.__archviewSagaState,gate: window.__archviewGateState," +
    "hud: document.querySelector('#saga-degree-hud')?.textContent || ''," +
    "whatNext: document.querySelector('#saga-what-next')?.textContent || ''," +
    "status: document.querySelector('#st-boundary')?.textContent || ''," +
    "question: document.querySelector('#q-title')?.textContent || ''," +
    "buttons: [...document.querySelectorAll('#scene-buttons .scene-btn')].map((button) => button.textContent)};" +
    "})()";
  let result;
  const pageDeadline = Date.now() + 20000;
  do {
    result = await page.send("Runtime.evaluate", { returnByValue: true, expression });
    if (result.result.value?.saga) break;
    await new Promise((resolve) => setTimeout(resolve, 500));
  } while (Date.now() < pageDeadline);
  const value = result.result.value;
  if (!value.saga?.valid || value.saga.stageCount !== 4 || value.saga.renderedStageCount !== 4) {
    throw new Error("SAGA scene did not render four stages: " + JSON.stringify(value));
  }
  if (value.hud !== "SAGA height: H⁰ → H¹ → H² · this scene only") {
    throw new Error("SAGA HUD mismatch: " + value.hud);
  }
  if ((mode === "saga" && !value.whatNext) || !value.question.includes("SAGA diagnostic staircase")) {
    throw new Error("SAGA silence/scene labels missing: " + JSON.stringify(value));
  }
  if (mode === "absent" && (value.gate?.supplied || value.gate?.error)) {
    throw new Error("gate absence is not silent: " + JSON.stringify(value));
  }
  const firstGateAction = value.gate?.actions?.[0];
  const expectedActionLabel = firstGateAction
    ? firstGateAction.action + (firstGateAction.boundaryOverrideApplied ? "*" : "") : "";
  if (mode === "supplied" && (!value.gate?.supplied || !value.gate.decision || !firstGateAction ||
    !value.gate.label.includes(value.gate.decision) || !value.gate.label.includes(firstGateAction.rowRef) ||
    !value.gate.label.includes(expectedActionLabel))) {
    throw new Error("gate report was not rendered: " + JSON.stringify(value));
  }
  if (mode === "mismatch" && (!value.gate?.error || value.gate.supplied || !value.status.includes("Gate report rejected"))) {
    throw new Error("gate mismatch was not rejected: " + JSON.stringify(value));
  }
  if (mode === "malformed" && (!value.gate?.error?.includes("JSON parse failed") || value.gate.supplied ||
    !value.status.includes("Gate report rejected"))) {
    throw new Error("malformed gate report was not rejected: " + JSON.stringify(value));
  }
  if (mode === "missing-boundary" && (!value.gate?.error?.includes("boundary override shape mismatch") ||
    value.gate.supplied || !value.status.includes("Gate report rejected"))) {
    throw new Error("missing boundary override was not rejected: " + JSON.stringify(value));
  }
  console.log(JSON.stringify(value));
  page.close(); browser.kill(); server.close();
}

main().catch((error) => { console.error(error.stack || error); process.exitCode = 1; });
