#!/usr/bin/env node

const fs = require("fs");
const http = require("http");
const os = require("os");
const path = require("path");
const { spawn } = require("child_process");

const root = path.resolve(process.argv[2] || "tools/archview");
const screenshotPath = path.resolve(process.argv[3] || ".tmp/archview-train-ticket.png");
const chrome = [process.env.CHROME_BIN, "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome", "/usr/bin/google-chrome", "/usr/bin/chromium"].filter(Boolean).find(fs.existsSync);
if (!chrome) throw new Error("Chrome/Chromium executable not found; set CHROME_BIN");

function serve(directory) {
  const base = path.resolve(directory);
  const server = http.createServer((request, response) => {
    const pathname = decodeURIComponent(new URL(request.url, "http://localhost").pathname);
    const file = path.resolve(base, `.${pathname === "/" ? "/archview.html" : pathname}`);
    if (file !== base && !file.startsWith(`${base}${path.sep}`)) return response.writeHead(403).end();
    fs.readFile(file, (error, data) => {
      if (error) return response.writeHead(404).end();
      const extension = path.extname(file);
      const contentType = extension === ".js" ? "text/javascript" : extension === ".css" ? "text/css" : extension === ".json" ? "application/json" : extension === ".png" ? "image/png" : "text/html";
      response.writeHead(200, { "Content-Type": `${contentType}; charset=utf-8` });
      response.end(data);
    });
  });
  return new Promise((resolve) => server.listen(0, "127.0.0.1", () => resolve(server)));
}

function connectPipe(browser, onEvent) {
  const input = browser.stdio[3], output = browser.stdio[4], pending = new Map();
  let nextId = 0, buffer = "";
  output.on("data", (chunk) => {
    buffer += chunk.toString();
    const messages = buffer.split("\0");
    buffer = messages.pop();
    for (const raw of messages) {
      if (!raw) continue;
      const message = JSON.parse(raw);
      if (message.id && pending.has(message.id)) {
        const item = pending.get(message.id); pending.delete(message.id);
        message.error ? item.reject(new Error(JSON.stringify(message.error))) : item.resolve(message.result);
      } else if (message.method) onEvent(message);
    }
  });
  browser.once("exit", (code) => { for (const item of pending.values()) item.reject(new Error(`Chrome exited: ${code}`)); });
  return {
    send(method, params = {}, sessionId = null) {
      const id = ++nextId;
      return new Promise((resolve, reject) => {
        pending.set(id, { resolve, reject });
        input.write(`${JSON.stringify(sessionId ? { id, method, params, sessionId } : { id, method, params })}\0`);
      });
    },
    close() { input.end(); },
  };
}

async function waitFor(page, expression, timeoutMs = 30000) {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    const value = await page.send("Runtime.evaluate", { returnByValue: true, expression });
    if (value.result.value) return value.result.value;
    await new Promise((resolve) => setTimeout(resolve, 100));
  }
  throw new Error(`Timed out waiting for ${expression}`);
}

async function main() {
  const server = await serve(root);
  const profile = fs.mkdtempSync(path.join(os.tmpdir(), "archview-scale-"));
  const browser = spawn(chrome, ["--headless=new", "--use-gl=swiftshader", "--enable-unsafe-swiftshader", "--no-sandbox", "--ignore-certificate-errors", "--disable-background-timer-throttling", "--disable-renderer-backgrounding", "--remote-debugging-pipe", `--user-data-dir=${profile}`], { stdio: ["ignore", "ignore", "pipe", "pipe", "pipe"] });
  const errors = [];
  const cdp = connectPipe(browser, (event) => {
    if (event.method === "Runtime.exceptionThrown") errors.push(event.params.exceptionDetails.text);
    if (event.method === "Runtime.consoleAPICalled" && event.params.type === "error") errors.push(event.params.args.map((arg) => arg.value || arg.description).join(" "));
  });
  const target = await cdp.send("Target.createTarget", { url: "about:blank" });
  const attached = await cdp.send("Target.attachToTarget", { targetId: target.targetId, flatten: true });
  const page = { send(method, params = {}) { return cdp.send(method, params, attached.sessionId); } };
  try {
    await page.send("Page.enable"); await page.send("Page.bringToFront"); await page.send("Runtime.enable"); await page.send("Emulation.setDeviceMetricsOverride", { width: 1440, height: 900, deviceScaleFactor: 1, mobile: false });
    await page.send("Page.navigate", { url: `http://127.0.0.1:${server.address().port}/archview.html` });
    await waitFor(page, "window.__archviewState?.architecture?.status === 'loaded'");
    await page.send("Runtime.evaluate", { expression: `document.querySelector('[data-cover-id="cover:train-ticket-global-surface"]').click()` });
    await waitFor(page, "window.__archviewRenderStats?.complete === true");
    const result = await page.send("Runtime.evaluate", { returnByValue: true, awaitPromise: true, expression: `(async () => {
      document.querySelector('[data-context-id]')?.click();
      const contextKind = window.__archviewState.selection?.kind;
      document.querySelector('[data-subject]')?.click();
      const subjectKind = window.__archviewState.selection?.kind;
      document.querySelector('[data-atom-id]')?.click();
      const atomKind = window.__archviewState.selection?.kind;
      document.querySelector('#source-targets [data-source-id]')?.click();
      const sourceKind = window.__archviewState.selection?.kind;
      const sourcePath = document.querySelector('#source-path').textContent;
      document.querySelector('#overview-button').click();
      const search = document.querySelector('#architecture-search');
      search.value = 'ts-order-service'; search.dispatchEvent(new Event('input', { bubbles: true }));
      const searchText = document.querySelector('#search-results').textContent;
      const stats = window.__archviewRenderStats;
      const started = performance.now(); let frames = 0;
      await new Promise((resolve) => { const tick = (now) => { frames += 1; now - started >= 1000 ? resolve() : requestAnimationFrame(tick); }; requestAnimationFrame(tick); });
      return { counts: window.__archviewState.architecture.index.counts, cover: window.__archviewState.cover, layoutAtoms: window.__archviewLayout.atoms.length, stats: { atomGlyphs: stats.atomGlyphs, totalAtoms: stats.totalAtoms, progressive: stats.progressive, complete: stats.complete, batches: stats.batches, subjectLabelLod: stats.subjectLabelLod, atomLod: stats.atomLod, skeletonMs: stats.skeletonReadyAt - stats.startedAt, completionMs: stats.completedAt - stats.startedAt }, fps: frames, searchText, interaction: { contextKind, subjectKind, atomKind, sourceKind, sourcePath }, subjectButtons: document.querySelectorAll('[data-subject]').length, atomButtons: document.querySelectorAll('[data-atom-id]').length, errors: document.querySelectorAll('[role="alert"]:not([hidden])').length };
    })()` });
    const value = result.result.value;
    const expected = { sources: 440, atoms: 2118, contexts: 43, covers: 3 };
    if (JSON.stringify(value.counts) !== JSON.stringify(expected)) throw new Error(`Scale counts changed: ${JSON.stringify(value)}`);
    if (value.cover !== "cover:train-ticket-global-surface" || value.layoutAtoms < 2118 || !value.stats.progressive || !value.stats.complete || value.stats.batches < 2 || value.stats.atomGlyphs !== value.layoutAtoms || value.stats.subjectLabelLod !== "context" || value.stats.atomLod !== "points" || value.stats.skeletonMs >= 100) throw new Error(`Progressive unsampled rendering failed: ${JSON.stringify(value)}`);
    if (value.fps < 30 || !value.searchText.toLowerCase().includes("order") || JSON.stringify([value.interaction.contextKind, value.interaction.subjectKind, value.interaction.atomKind, value.interaction.sourceKind]) !== JSON.stringify(["context", "subject", "atom", "source"]) || value.interaction.sourcePath === "—" || value.subjectButtons < 1 || value.atomButtons !== 0 || value.errors) throw new Error(`Scale interaction, LOD, source landing, or frame target failed: ${JSON.stringify(value)}`);
    await page.send("Runtime.evaluate", { awaitPromise: true, expression: `(async () => { const search = document.querySelector('#architecture-search'); search.value = ''; search.dispatchEvent(new Event('input', { bubbles: true })); await new Promise((resolve) => requestAnimationFrame(() => requestAnimationFrame(resolve))); })()` });
    fs.mkdirSync(path.dirname(screenshotPath), { recursive: true });
    const shot = await page.send("Page.captureScreenshot", { format: "png", fromSurface: true });
    const repeatedShot = await page.send("Page.captureScreenshot", { format: "png", fromSurface: true });
    if (shot.data !== repeatedShot.data) throw new Error("Stable Paper Atlas produced non-deterministic consecutive screenshots");
    fs.writeFileSync(screenshotPath, Buffer.from(shot.data, "base64"));
    console.log(JSON.stringify({ counts: value.counts, cover: value.cover, layoutAtoms: value.layoutAtoms, stats: value.stats, fps: value.fps, interaction: value.interaction, searchMatched: value.searchText.toLowerCase().includes("order"), screenshot: screenshotPath }));
  } finally {
    await cdp.send("Target.closeTarget", { targetId: target.targetId }).catch(() => {}); cdp.close(); browser.kill(); server.close();
  }
  if (errors.length) throw new Error(`Browser errors: ${errors.join(" | ")}`);
}

main().catch((error) => { console.error(error.stack || error); process.exit(1); });
