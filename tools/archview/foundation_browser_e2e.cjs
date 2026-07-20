#!/usr/bin/env node

const fs = require("fs");
const http = require("http");
const os = require("os");
const path = require("path");
const { spawn } = require("child_process");

const root = path.resolve(process.argv[2] || "tools/archview/rebuild");
const screenshotPath = process.argv[3] ? path.resolve(process.argv[3]) : null;
const chromeCandidates = [
  process.env.CHROME_BIN,
  "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
  "/usr/bin/google-chrome",
  "/usr/bin/chromium",
].filter(Boolean);
const chrome = chromeCandidates.find((candidate) => fs.existsSync(candidate));
if (!chrome) throw new Error("Chrome/Chromium executable not found; set CHROME_BIN");

function serve(directory) {
  const base = path.resolve(directory);
  const server = http.createServer((request, response) => {
    const relative = decodeURIComponent(new URL(request.url, "http://localhost").pathname);
    const file = path.resolve(base, `.${relative === "/" ? "/index.html" : relative}`);
    if (file !== base && !file.startsWith(`${base}${path.sep}`)) {
      response.writeHead(403); response.end(); return;
    }
    fs.readFile(file, (error, data) => {
      if (error) { response.writeHead(404); response.end(); return; }
      const extension = path.extname(file);
      const contentType = extension === ".js" ? "text/javascript" : extension === ".css" ? "text/css" : "text/html";
      response.writeHead(200, { "Content-Type": `${contentType}; charset=utf-8` });
      response.end(data);
    });
  });
  return new Promise((resolve) => server.listen(0, "127.0.0.1", () => resolve(server)));
}

function connectPipe(browser, onEvent) {
  const input = browser.stdio[3];
  const output = browser.stdio[4];
  let nextId = 0;
  let buffer = "";
  const pending = new Map();
  output.on("data", (chunk) => {
    buffer += chunk.toString();
    const messages = buffer.split("\0");
    buffer = messages.pop();
    for (const raw of messages) {
      if (!raw) continue;
      const message = JSON.parse(raw);
      if (message.id && pending.has(message.id)) {
        const item = pending.get(message.id); pending.delete(message.id);
        if (message.error) item.reject(new Error(JSON.stringify(message.error)));
        else item.resolve(message.result);
      } else if (message.method) onEvent(message);
    }
  });
  browser.once("exit", (code) => {
    for (const item of pending.values()) item.reject(new Error(`Chrome exited before CDP completed: ${code}`));
    pending.clear();
  });
  return Object.freeze({
    send(method, params = {}, sessionId = null) {
      const id = ++nextId;
      const message = sessionId ? { id, method, params, sessionId } : { id, method, params };
      return new Promise((resolveMessage, rejectMessage) => {
        pending.set(id, { resolve: resolveMessage, reject: rejectMessage });
        input.write(`${JSON.stringify(message)}\0`);
      });
    },
    close() { input.end(); },
  });
}

async function waitFor(page, expression, timeoutMs = 20000) {
  const deadline = Date.now() + timeoutMs;
  let result;
  do {
    result = await page.send("Runtime.evaluate", { returnByValue: true, expression });
    if (result.result.value) return result.result.value;
    await new Promise((resolve) => setTimeout(resolve, 250));
  } while (Date.now() < deadline);
  throw new Error(`Timed out waiting for: ${expression}`);
}

async function main() {
  const server = await serve(root);
  const port = server.address().port;
  const profile = fs.mkdtempSync(path.join(os.tmpdir(), "archview-foundation-"));
  const browser = spawn(chrome, [
    "--headless=new",
    "--use-gl=swiftshader",
    "--enable-unsafe-swiftshader",
    "--no-sandbox",
    "--ignore-certificate-errors",
    "--remote-debugging-pipe",
    `--user-data-dir=${profile}`,
  ], { stdio: ["ignore", "ignore", "pipe", "pipe", "pipe"] });

  let stderr = "";
  browser.stderr.on("data", (chunk) => { stderr += chunk.toString(); });

  const runtimeErrors = [];
  const consoleErrors = [];
  const cdp = connectPipe(browser, (event) => {
    if (event.method === "Runtime.exceptionThrown") runtimeErrors.push(event.params.exceptionDetails.text);
    if (event.method === "Runtime.consoleAPICalled" && event.params.type === "error") {
      consoleErrors.push(event.params.args.map((argument) => argument.value || argument.description || "error").join(" "));
    }
    if (event.method === "Log.entryAdded" && event.params.entry.level === "error") {
      consoleErrors.push(event.params.entry.text);
    }
  });
  const target = await cdp.send("Target.createTarget", { url: "about:blank" });
  const attached = await cdp.send("Target.attachToTarget", { targetId: target.targetId, flatten: true });
  const sessionId = attached.sessionId;
  const page = Object.freeze({
    send(method, params = {}) { return cdp.send(method, params, sessionId); },
  });

  try {
    await page.send("Page.enable");
    await page.send("Runtime.enable");
    await page.send("Log.enable");
    await page.send("Emulation.setDeviceMetricsOverride", { width: 1366, height: 768, deviceScaleFactor: 1, mobile: false });
    await page.send("Page.navigate", { url: `http://127.0.0.1:${port}/index.html` });
    await waitFor(page, "window.__archviewFoundationState?.phase === 'ready' || document.querySelector('#archview-app')?.dataset.phase === 'error'");

    const bootPhase = await page.send("Runtime.evaluate", {
      returnByValue: true,
      expression: `({
        state: window.__archviewFoundationState?.phase || null,
        shell: document.querySelector('#archview-app')?.dataset.phase || null,
        message: document.querySelector('#webgl-error-message')?.textContent || null,
      })`,
    });
    if (bootPhase.result.value.state !== "ready") {
      throw new Error(`Foundation boot failed: ${JSON.stringify({ boot: bootPhase.result.value, runtimeErrors, consoleErrors, stderr })}`);
    }

    const normal = await page.send("Runtime.evaluate", {
      returnByValue: true,
      expression: `(() => {
        const root = document.querySelector('#archview-app');
        const workspace = document.querySelector('.workspace').getBoundingClientRect();
        const scope = document.querySelector('.scope-explorer').getBoundingClientRect();
        const atlas = document.querySelector('.atlas-panel').getBoundingClientRect();
        const inspector = document.querySelector('.inspector').getBoundingClientRect();
        const drawer = document.querySelector('.source-drawer').getBoundingClientRect();
        document.querySelector('[data-mode-button="analysis"]').click();
        const analysis = window.__archviewFoundationState.mode;
        document.querySelector('[data-mode-button="improve"]').click();
        const improve = window.__archviewFoundationState.mode;
        document.querySelector('[data-mode-button="architecture"]').click();
        document.querySelector('[data-view="top"]').click();
        const topView = window.__archviewFoundationState.view;
        document.querySelector('[data-view="front"]').click();
        const frontView = window.__archviewFoundationState.view;
        document.querySelector('[data-view="reset"]').click();
        return {
          phase: root.dataset.phase,
          canvasCount: document.querySelectorAll('#atlas-canvas-host canvas').length,
          modeCount: document.querySelectorAll('[data-mode-button]').length,
          analysis,
          improve,
          finalMode: window.__archviewFoundationState.mode,
          topView,
          frontView,
          finalView: window.__archviewFoundationState.view,
          viewport: { width: innerWidth, height: innerHeight },
          layout: { workspace: workspace.width, scope: scope.width, atlas: atlas.width, inspector: inspector.width, drawer: drawer.height },
          emptyTitle: document.querySelector('#empty-state-title').textContent,
          renderer: document.querySelector('#renderer-status').textContent,
          errorHidden: document.querySelector('#webgl-error').hidden,
        };
      })()`,
    });

    const value = normal.result.value;
    if (value.phase !== "ready" || value.canvasCount !== 1 || value.modeCount !== 3) {
      throw new Error(`Foundation did not initialize: ${JSON.stringify(value)}`);
    }
    if (value.analysis !== "analysis" || value.improve !== "improve" || value.finalMode !== "architecture") {
      throw new Error(`Shared mode state failed: ${JSON.stringify(value)}`);
    }
    if (value.topView !== "top" || value.frontView !== "front" || value.finalView !== "isometric") {
      throw new Error(`Camera view state failed: ${JSON.stringify(value)}`);
    }
    if (value.viewport.width < 1366 || value.layout.scope <= 0 || value.layout.atlas <= 0 || value.layout.inspector <= 0 || value.layout.drawer <= 0) {
      throw new Error(`Desktop layout is not simultaneously readable: ${JSON.stringify(value)}`);
    }
    if (!value.errorHidden || value.renderer !== "ready" || runtimeErrors.length || consoleErrors.length) {
      throw new Error(`Unexpected renderer error: ${JSON.stringify({ value, runtimeErrors, consoleErrors })}`);
    }

    if (screenshotPath) {
      const screenshot = await page.send("Page.captureScreenshot", { format: "png", captureBeyondViewport: false });
      fs.mkdirSync(path.dirname(screenshotPath), { recursive: true });
      fs.writeFileSync(screenshotPath, Buffer.from(screenshot.data, "base64"));
    }

    await page.send("Page.addScriptToEvaluateOnNewDocument", {
      source: `(() => {
        const original = HTMLCanvasElement.prototype.getContext;
        HTMLCanvasElement.prototype.getContext = function(type, ...args) {
          if (type === 'webgl' || type === 'webgl2' || type === 'experimental-webgl') return null;
          return original.call(this, type, ...args);
        };
      })();`,
    });
    await page.send("Page.navigate", { url: `http://127.0.0.1:${port}/index.html?webgl-unavailable=1` });
    await waitFor(page, "window.__archviewFoundationState?.phase === 'error'");
    const failure = await page.send("Runtime.evaluate", {
      returnByValue: true,
      expression: `(() => ({
        phase: document.querySelector('#archview-app').dataset.phase,
        errorVisible: !document.querySelector('#webgl-error').hidden,
        message: document.querySelector('#webgl-error-message').textContent,
        shellVisible: document.querySelector('.scope-explorer').getBoundingClientRect().width > 0,
      }))()`,
    });
    if (failure.result.value.phase !== "error" || !failure.result.value.errorVisible || !failure.result.value.shellVisible) {
      throw new Error(`WebGL failure was not shown in the shell: ${JSON.stringify(failure.result.value)}`);
    }

    console.log(JSON.stringify({ normal: value, webglFailure: failure.result.value }));
  } finally {
    await cdp.send("Target.closeTarget", { targetId: target.targetId }).catch(() => {});
    cdp.close();
    browser.kill();
    server.close();
  }
}

main().catch((error) => { console.error(error.stack || error); process.exit(1); });
