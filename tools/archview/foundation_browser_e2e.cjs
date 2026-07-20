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
    const requestUrl = new URL(request.url, "http://localhost");
    const relative = decodeURIComponent(requestUrl.pathname);
    if (relative === "/app.js" && requestUrl.searchParams.has("bootstrap-unavailable")) {
      response.writeHead(503); response.end(); return;
    }
    if (relative.startsWith("/redirect-run/")) {
      response.writeHead(302, { Location: "/index.html" }); response.end(); return;
    }
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
    await waitFor(page, "window.__archviewState?.architecture?.status === 'loaded' || document.querySelector('#archview-app')?.dataset.phase === 'error'");

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
        document.querySelector('[data-atom-id="atom:checkout"]').click();
        const checkoutSelection = window.__archviewState.selection;
        const checkoutSource = {
          path: document.querySelector('#source-path').textContent,
          symbol: document.querySelector('#source-symbol').textContent,
          line: document.querySelector('#source-line').textContent,
          resolution: document.querySelector('#source-resolution').textContent,
        };
        const index = window.__archviewState.architecture.index;
        const architectureLayout = window.__archviewLayout;
        const fidelity = {
          contexts: architectureLayout.contexts.every((entry) => index.contextsById.has(entry.id)),
          atoms: architectureLayout.atoms.every((entry) => index.atomsById.has(entry.atomId) && index.contextsById.get(entry.contextId)?.atoms.includes(entry.atomId)),
          restrictions: architectureLayout.restrictions.every((entry) => index.contextsById.get(entry.sourceId)?.restrictsTo.includes(entry.targetId)),
          sharedSupports: architectureLayout.sharedSupports.every((entry) => new Set(entry.contextIds).size > 1 && entry.contextIds.every((contextId) => index.contextsById.get(contextId)?.atoms.includes(entry.atomId))),
          contextArea: architectureLayout.contexts.every((entry) => Math.abs(entry.width * entry.height - (34 + entry.atomCount * 8)) < 1e-9),
        };
        const coverQuestion = document.querySelector('[data-cover-id="cover:payment-lifecycle"]');
        coverQuestion.click();
        const q1 = ['ctx:checkout', 'ctx:ledger', 'ctx:refund'].every((id) => document.querySelector('#architecture-facts').textContent.includes(id));
        document.querySelector('[data-subject="CheckoutService"][data-context-id="ctx:checkout"]').click();
        const checkoutFacts = document.querySelector('#architecture-facts').textContent;
        const q2 = checkoutFacts.includes('capability') && checkoutFacts.includes('accepts Payment');
        const q4 = checkoutFacts.includes('effect') && checkoutFacts.includes('captures Payment');
        document.querySelector('[data-subject="RefundService"][data-context-id="ctx:refund"]').click();
        const refundFacts = document.querySelector('#architecture-facts').textContent;
        const q3 = refundFacts.includes('state') && refundFacts.includes('transitionsTo Refunded');
        document.querySelector('[data-atom-id="atom:settlement-contract"][data-context-id="ctx:checkout"]').click();
        const q5 = document.querySelector('#source-targets').textContent.includes('contracts/payment-lifecycle.md');
        document.querySelector('[data-source-id="src:contract"]').click();
        const sourceBreadcrumb = [...document.querySelectorAll('[data-zoom-level]')].map((button) => button.dataset.zoomLevel);
        const sourceSelection = window.__archviewState.selection;
        const restrictionButton = document.querySelector('[data-restriction-id="ctx:checkout->ctx:ledger"]');
        restrictionButton.dispatchEvent(new MouseEvent('mouseenter'));
        const restrictionHover = document.querySelector('#atlas-hover-label').textContent;
        restrictionButton.click();
        const restrictionFacts = document.querySelector('#architecture-facts').textContent;
        document.querySelector('[data-shared-support-id="shared::atom:settlement-contract"]').click();
        const sharedSupportFacts = document.querySelector('#architecture-facts').textContent;
        const search = document.querySelector('#architecture-search');
        search.value = 'RefundService';
        search.dispatchEvent(new Event('input', { bubbles: true }));
        const searchKinds = [...document.querySelectorAll('[data-search-kind]')].map((button) => button.dataset.searchKind);
        document.querySelector('#overview-button').click();
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
          inputStatus: root.dataset.inputStatus,
          analysisInputStatus: root.dataset.analysisStatus,
          counts: window.__archviewState.architecture.index.counts,
          atomButtons: document.querySelectorAll('[data-atom-id]').length,
          renderStats: window.__archviewRenderStats,
          selection: checkoutSelection,
          source: checkoutSource,
          fidelity,
          derivedGeometry: {
            restriction: restrictionFacts.includes('ctx:checkout') && restrictionFacts.includes('ctx:ledger') && restrictionFacts.includes('contexts.ctx:checkout.restrictsTo'),
            restrictionHover: restrictionHover.includes('ctx:checkout') && restrictionHover.includes('ctx:ledger') && restrictionHover.includes('Rendered from'),
            sharedSupport: sharedSupportFacts.includes('atom:settlement-contract') && ['ctx:checkout', 'ctx:ledger', 'ctx:refund'].every((id) => sharedSupportFacts.includes(id)),
          },
          sourceBreadcrumb,
          sourceSelection,
          layoutSignature: architectureLayout.signature,
          semanticZoom: window.__archviewState.zoom,
          searchKinds,
          taskTest: { answers: [q1, q2, q3, q4, q5], correct: [q1, q2, q3, q4, q5].filter(Boolean).length, total: 5 },
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
    if (value.inputStatus !== "loaded" || JSON.stringify(value.counts) !== JSON.stringify({ sources: 5, atoms: 10, contexts: 3, covers: 1 })) {
      throw new Error(`Valid ArchMap did not load exact fixture facts: ${JSON.stringify(value)}`);
    }
    if (value.analysisInputStatus !== "absent") {
      throw new Error(`Analysis absence was not an explicit normal state: ${JSON.stringify(value)}`);
    }
    if (value.renderStats?.contextPlates !== 3 || value.renderStats?.atomGlyphs !== 12) {
      throw new Error(`Three.js geometry did not match explicit Context memberships: ${JSON.stringify(value)}`);
    }
    const geometryTypes = Object.values(value.renderStats.atomGeometryTypes || {});
    if (geometryTypes.length !== 9 || new Set(geometryTypes).size !== 9 || value.renderStats.restrictionRecords?.length !== 2 || value.renderStats.sharedSupportRecords?.length !== 1) {
      throw new Error(`Atom shapes or derived geometry provenance were incomplete: ${JSON.stringify(value)}`);
    }
    if (value.selection?.id !== "atom:checkout" || value.source.path !== "services/checkout/CheckoutService.ts" || value.source.symbol !== "CheckoutService.capture" || value.source.line !== "48" || value.source.resolution !== "DIRECT EVIDENCE") {
      throw new Error(`Atom source landing did not preserve source metadata: ${JSON.stringify(value)}`);
    }
    if (!Object.values(value.fidelity).every(Boolean)) {
      throw new Error(`Rendered Architecture contains facts not supplied by ArchMap: ${JSON.stringify(value)}`);
    }
    if (!Object.values(value.derivedGeometry).every(Boolean) || JSON.stringify(value.sourceBreadcrumb) !== JSON.stringify(["cover", "context", "subject", "atom", "source"]) || value.sourceSelection?.contextId !== "ctx:checkout") {
      throw new Error(`Derived geometry provenance or Source semantic zoom failed: ${JSON.stringify(value)}`);
    }
    if (value.semanticZoom !== "cover" || !value.searchKinds.includes("subject") || !value.searchKinds.includes("atom")) {
      throw new Error(`Semantic zoom or structured search failed: ${JSON.stringify(value)}`);
    }
    if (value.taskTest.correct / value.taskTest.total < 0.8) {
      throw new Error(`Architecture understanding task score was below 80%: ${JSON.stringify(value)}`);
    }

    const repeated = await page.send("Runtime.evaluate", {
      awaitPromise: true,
      returnByValue: true,
      expression: `(async () => {
        const read = async () => {
          await window.__archview.loadUrl('./fixtures/vertical-slice.archmap.json');
          document.querySelector('[data-atom-id="atom:settlement-contract"][data-context-id="ctx:checkout"]').click();
          return {
            signature: window.__archviewLayout.signature,
            sources: [...document.querySelectorAll('#source-targets li')].map((item) => item.textContent),
          };
        };
        return [await read(), await read()];
      })()`,
    });
    const [firstLayout, secondLayout] = repeated.result.value;
    if (firstLayout.signature !== value.layoutSignature || firstLayout.signature !== secondLayout.signature || JSON.stringify(firstLayout.sources) !== JSON.stringify(secondLayout.sources)) {
      throw new Error(`Architecture layout or source order was not deterministic: ${JSON.stringify({ firstLayout, secondLayout })}`);
    }

    const adversarial = await page.send("Runtime.evaluate", {
      awaitPromise: true,
      returnByValue: true,
      expression: `(async () => {
        const base = {
          schema: 'archmap/v0.5.4', id: 'adversarial', sources: { s: { kind: 'test', path: 'src/a.ts' } },
          atoms: [
            { id: 'a', kind: 'component', subject: 'A', axis: 'static', refs: ['s'] },
            { id: 'b', kind: 'state', subject: 'B', axis: 'state', refs: ['s'] },
          ],
          contexts: [
            { id: 'c', atoms: ['a', 'a'], restrictsTo: ['c2', 'c2'] },
            { id: 'c2', atoms: ['b'] },
          ], covers: [],
        };
        window.__archview.loadObject(base, 'no-cover probe');
        const noCover = { contexts: window.__archviewLayout.contexts.length, atoms: window.__archviewLayout.atoms.length };
        const singleDocument = { ...base, contexts: [{ id: 'c', atoms: ['a'], restrictsTo: ['c2'] }, { id: 'c2', atoms: ['b'] }], covers: [{ id: 'cover:c', contexts: ['c', 'c2'] }] };
        window.__archview.loadObject(singleDocument, 'single membership probe');
        const singleContext = window.__archviewLayout.contexts.find((entry) => entry.id === 'c');
        window.__archview.loadObject({ ...base, covers: [{ id: 'cover:c', contexts: ['c', 'c2'] }] }, 'duplicate membership probe');
        const duplicateContext = window.__archviewLayout.contexts.find((entry) => entry.id === 'c');
        const duplicate = {
          atoms: window.__archviewLayout.atoms.filter((entry) => entry.contextId === 'c').length,
          sharedSupports: window.__archviewLayout.sharedSupports.length,
          restrictions: window.__archviewLayout.restrictions.length,
          atomButtons: document.querySelectorAll('[data-atom-id="a"][data-context-id="c"]').length,
          subjectCount: document.querySelector('[data-subject="A"][data-context-id="c"] .item-count')?.textContent,
          singleArea: singleContext.width * singleContext.height,
          duplicateArea: duplicateContext.width * duplicateContext.height,
        };
        window.__archview.loadObject({
          schema: 'archmap/v0.5.4', id: 'source-cycle',
          sources: { s: { kind: 'test', source: 't' }, t: { kind: 'test', source: 's' } },
          atoms: [{ id: 'a', kind: 'component', subject: 'A', axis: 'static', refs: ['s'] }],
          contexts: [{ id: 'c', atoms: ['a'] }], covers: [{ id: 'cover:c', contexts: ['c'] }],
        }, 'source cycle probe');
        const sourceCycle = { status: window.__archviewState.architecture.status, issues: [...document.querySelectorAll('#archmap-issues li')].map((item) => item.textContent) };
        await window.__archview.loadUrl('https://example.invalid/archmap.json');
        const crossOrigin = { status: window.__archviewState.architecture.status, issues: [...document.querySelectorAll('#archmap-issues li')].map((item) => item.textContent) };
        return { noCover, duplicate, sourceCycle, crossOrigin };
      })()`,
    });
    const probes = adversarial.result.value;
    if (probes.noCover.contexts !== 0 || probes.noCover.atoms !== 0 || probes.duplicate.atoms !== 1 || probes.duplicate.sharedSupports !== 0 || probes.duplicate.restrictions !== 1 || probes.duplicate.atomButtons !== 1 || probes.duplicate.subjectCount !== "1" || Math.abs(probes.duplicate.singleArea - probes.duplicate.duplicateArea) > 1e-9) {
      throw new Error(`Implicit Cover scope or duplicate membership generated geometry: ${JSON.stringify(adversarial.result.value)}`);
    }
    if (probes.sourceCycle.status !== "unresolved" || !probes.sourceCycle.issues.some((entry) => entry.includes("cycle")) || probes.crossOrigin.status !== "error" || !probes.crossOrigin.issues.some((entry) => entry.includes("current origin"))) {
      throw new Error(`Source cycle or cross-origin ArchMap URL was not visibly rejected: ${JSON.stringify(probes)}`);
    }
    await page.send("Runtime.evaluate", { awaitPromise: true, expression: `window.__archview.loadUrl('./fixtures/vertical-slice.archmap.json')` });
    await page.send("Runtime.evaluate", { expression: `document.querySelector('[data-atom-id="atom:settlement-contract"][data-context-id="ctx:checkout"]').click()` });

    const analysisCases = await page.send("Runtime.evaluate", {
      awaitPromise: true,
      returnByValue: true,
      expression: `(async () => {
        const { canonicalJson, documentsFromFiles, sha256Hex, validateAnalysisBundle } = await import('./analysis.js');
        const index = window.__archviewState.architecture.index;
        const archmapDigest = await sha256Hex(index.canonicalJson);
        const inputDigests = {
          archmap: { path: 'input:vertical-slice.archmap.json', sha256: archmapDigest },
          lawPolicy: { path: 'input:law-policy.json', sha256: '1'.repeat(64) },
          lawSurface: { path: 'input:law-surface.json', sha256: '5'.repeat(64) },
          measurementProfile: { path: 'input:profile.json', sha256: '2'.repeat(64) },
          measurementProfiles: [{ path: 'input:profile.json', sha256: '2'.repeat(64) }],
          profileFingerprint: { basis: 'test projection of existing contract', sha256: '3'.repeat(64) },
          siteCoverDigest: { basis: 'normalized contexts + covers + derived finite cover nerve', sha256: '4'.repeat(64), status: 'computed' },
        };
        const runSeed = [inputDigests.archmap.sha256, inputDigests.lawPolicy.sha256, inputDigests.lawSurface.sha256, ...inputDigests.measurementProfiles.map((entry) => entry.sha256), '0.5.4'].join('|');
        const runId = 'run:' + (await sha256Hex(runSeed)).slice(0, 12);
        const componentFingerprints = { lawPolicy: 'sha256:' + inputDigests.lawPolicy.sha256, lawSurface: 'sha256:' + inputDigests.lawSurface.sha256, measurementProfile: 'sha256:' + inputDigests.measurementProfile.sha256 };
        const contract = { toolVersion: '0.5.4', runId, inputDigests, componentFingerprints };
        const prefixed = (prefix, id) => id.startsWith(prefix + ':') ? id : prefix + ':' + id;
        const normalizedAtomId = (id) => prefixed('atom', id);
        const normalizedContextId = (id) => prefixed('ctx', id);
        const normalizedCoverId = (id) => prefixed('cover', id);
        const sortedUnique = (values) => [...new Set(values || [])].sort();
        const normalized = {
          schema: 'normalized-archmap/v0.5.4', ...contract,
          normalizerId: 'archmap-schema052-finite-poset-site@1', sourceArchmapRef: 'input:vertical-slice.archmap.json', sourceArchmapId: index.id,
          extractionDoctrineRef: {},
          atoms: index.atoms.map((atom) => ({ sourceAtomId: atom.id, normalizedAtomId: normalizedAtomId(atom.id), atomKind: atom.kind, subject: atom.subject, axis: atom.axis, predicate: atom.predicate || atom.kind, ...(atom.object === undefined ? {} : { object: atom.object }), sourceRefs: sortedUnique(atom.refs), contextMemberships: sortedUnique((index.contextIdsByAtom.get(atom.id) || []).map(normalizedContextId)), normalizationStatus: 'normalized' })).sort((a, b) => a.normalizedAtomId.localeCompare(b.normalizedAtomId)),
          contexts: index.contexts.map((context) => ({ sourceContextId: context.id, normalizedContextId: normalizedContextId(context.id), atomIds: sortedUnique((context.atoms || []).map(normalizedAtomId)), restrictsTo: sortedUnique((context.restrictsTo || []).map(normalizedContextId)), sourceRefs: sortedUnique(context.refs), posetStatus: 'finiteObserved' })).sort((a, b) => a.normalizedContextId.localeCompare(b.normalizedContextId)),
          covers: index.covers.map((cover) => ({ sourceCoverId: cover.id, normalizedCoverId: normalizedCoverId(cover.id), contextIds: sortedUnique((cover.contexts || []).map(normalizedContextId)), sourceRefs: sortedUnique(cover.refs), coverageStatus: 'selectedCandidate' })).sort((a, b) => a.normalizedCoverId.localeCompare(b.normalizedCoverId)),
          summary: { atomCount: index.atoms.length, normalizedAtomCount: index.atoms.length, contextCount: index.contexts.length, coverCount: index.covers.length, doctrineFingerprint: 'sha256:aat-canonical-doctrine-schema052' }, nonConclusions: [],
        };
        const packet = {
          schema: 'archsig-measurement-packet/v0.5.4', ...contract, packetId: 'packet:browser',
          profile: { schema: 'measurement-profile/v0.5.4', profileId: 'profile:browser@1', siteRef: 'archmap:/contexts', coverRef: index.covers[0].id, coefficient: 'F2', effCoeff: 'finite-linear-algebra@1', resolutionSelector: 'taylor@1', domain: 'finite-poset-site', zeroPredicate: 'rank-zero@1', nonZeroPredicate: 'rank-positive@1', certSelector: 'finite-certificate@1', verdictDiscipline: 'five-valued-structural-verdict@1', finiteBounds: { maxSquareFreeWitnessVariables: 12, maxCoherenceContexts: 12, maxTorWitnessVariables: 12, maxBoundaryResidueVariables: 16, maxLaplacianCells: 16, maxPeriodCycles: 16, maxTransferTargets: 16 } }, profiles: [],
          structuralVerdict: [], computedInvariants: [], analyticReadings: [], assumptions: [], suppliedData: [], boundaryStatements: [], nonConclusions: [],
        };
        const summary = {
          schema: 'archsig-analysis-summary/v0.5.4', ...contract, measurementPacketSchema: packet.schema,
          profileRef: packet.profile.profileId, structuralVerdictSummary: { rowCount: 0, measuredNonzeroCount: 0, unmeasuredCount: 0, nonTerminalCount: 0 },
          conclusion: 'AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE', assumptionSummary: {}, insightArtifacts: {}, readThisFirst: { conclusion: 'AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE' }, translationRule: {}, translationRuleTable: [], nonConclusions: [],
        };
        const insight = {
          schema: 'archsig-insight-report/v0.5.4', ...contract, reportId: 'insight:browser', sourcePacketRef: 'archsig-measurement-packet.json',
          insightCards: [{ id: 'insight:browser:001', kind: 'orientation', title: 'Inspect support', oneLine: 'Inspect declared support.', evidence: { atomRefs: [normalizedAtomId(index.atoms[0].id)], contextRefs: [normalizedContextId(index.contexts[0].id)], coverRefs: [normalizedCoverId(index.covers[0].id)], sourceRefs: [index.sources[0][0]] }, unsupportedScalar: 42 }],
          actionQueue: [{ id: 'action:browser:001', kind: 'next_inspection', title: 'Inspect support', reason: 'Declared support is available.', targetRefs: [normalizedAtomId(index.atoms[0].id)] }], generatedAt: '2026-01-01T00:00:00Z', boundaryDigest: {}, claimValidation: {}, copyBlocks: {}, gluingGeometry: {}, guidedTours: [], headline: { conclusionCode: 'AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE' }, omittedDetailCounts: {}, outputArtifacts: {}, rankingBasis: [], readThisFirst: { conclusion: 'AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE' }, viewerVisualScenes: [], nonConclusions: [],
        };
        const manifest = {
          schema: 'archsig-run-manifest/v0.5.4', ...contract, commandName: 'analyze', mode: 'measurement', conclusionCode: null,
          archmapInputPath: 'input:vertical-slice.archmap.json', lawPolicyInputPath: 'input:law-policy.json', lawSurfaceInputPath: 'input:law-surface.json', measurementProfileInputPath: 'input:profile.json', measurementProfileInputPaths: ['input:profile.json'], rawArtifactRetention: 'omitted',
          generatedArtifacts: ['normalized-archmap.json', 'archsig-measurement-packet.json', 'archsig-analysis-summary.json', 'archsig-insight-report.json', 'archsig-run-manifest.json'], omittedArtifacts: [],
          artifactLinks: { measurementPacket: 'archsig-measurement-packet.json', summary: 'archsig-analysis-summary.json', insightReport: 'archsig-insight-report.json' },
          validationReports: { archmap: 'archmap-validation.json', lawPolicy: 'law-policy-validation.json', lawSurface: 'law-surface-validation.json', analysis: 'archsig-analysis-validation.json' }, validationResultSummary: { archmap: { result: 'pass', failedCheckCount: 0, warningCheckCount: 0 }, lawPolicy: { result: 'pass', failedCheckCount: 0, warningCheckCount: 0 }, analysis: { result: 'pass', failedCheckCount: 0, warningCheckCount: 0 } }, nonConclusions: [],
        };
        const packetDigest = await sha256Hex(packet);
        const comparisonRun = { path: 'head-run/archsig-run-manifest.json', runId: contract.runId, toolVersion: contract.toolVersion, archmap: inputDigests.archmap, lawPolicy: inputDigests.lawPolicy, profileFingerprint: inputDigests.profileFingerprint, componentFingerprints, siteCoverDigest: inputDigests.siteCoverDigest, measurementPacket: { path: 'head-run/archsig-measurement-packet.json', sha256: packetDigest } };
        const comparison = { schema: 'archsig-comparison-report/v0.5.4', toolVersion: '0.5.4', conclusionCode: null, comparability: {}, discipline: 'record-level comparison', inputDigests: { baseRun: { ...comparisonRun, path: 'base-run/archsig-run-manifest.json' }, headRun: comparisonRun }, artifactRefs: {}, independentConclusions: {}, verdictTransitions: [], boundaryStatements: [], classTransport: {}, nonConclusions: [] };
        const comparisonDigest = await sha256Hex(comparison);
        const gate = { schema: 'archsig-gate-report/v0.5.4', decision: 'PASS_WITHIN_GATE_POLICY', toolVersion: '0.5.4', inputDigests: { measurementPacket: { path: 'input:archsig-measurement-packet.json', sha256: packetDigest }, gatePolicy: { path: 'input:gate-policy.json', sha256: '6'.repeat(64) }, comparisonReport: { path: 'input:archsig-comparison-report.json', sha256: comparisonDigest } }, policyValidation: [], ruleOutcomes: [], nonConclusions: [] };
        const bundle = { manifest, normalized, packet, summary, insight, gate, comparison };
        const renderBefore = JSON.stringify(window.__archviewRenderStats);
        const layoutBefore = window.__archviewLayout.signature;
        const runFiles = {
          'archsig-run-manifest.json': manifest, 'normalized-archmap.json': normalized,
          'archsig-measurement-packet.json': packet, 'archsig-analysis-summary.json': summary,
          'archsig-insight-report.json': insight, 'archsig-gate-report.json': gate,
          'archsig-comparison-report.json': comparison,
        };
        const transfer = new DataTransfer();
        for (const [name, document] of Object.entries(runFiles)) transfer.items.add(new File([JSON.stringify(document)], name, { type: 'application/json' }));
        const directoryInput = document.querySelector('#analysis-directory');
        directoryInput.files = transfer.files;
        directoryInput.dispatchEvent(new Event('change', { bubbles: true }));
        for (let attempt = 0; attempt < 100 && window.__archviewState.analysis.status === 'loading'; attempt += 1) await new Promise((resolve) => setTimeout(resolve, 10));
        const acceptedState = window.__archviewState.analysis;
        const accepted = {
          status: acceptedState.status,
          shellStatus: document.querySelector('#archview-app').dataset.analysisStatus,
          label: document.querySelector('#analysis-input-status').textContent,
          runId: document.querySelector('#analysis-run-id').textContent,
          profile: document.querySelector('#analysis-profile-ref').textContent,
          packetDigest: document.querySelector('#analysis-packet-digest').textContent,
          findings: document.querySelector('#findings-list').textContent,
          architectureStable: renderBefore === JSON.stringify(window.__archviewRenderStats) && layoutBefore === window.__archviewLayout.signature,
          unsupportedScalarRendered: document.querySelector('#findings-list').textContent.includes('42'),
          candidateRendered: document.querySelector('#findings-list').textContent.toLowerCase().includes('candidate'),
        };
        const malformedJsonState = await window.__archview.loadAnalysisFiles([new File(['{'], 'archsig-run-manifest.json', { type: 'application/json' })], 'malformed JSON directory');
        const malformedJson = { status: malformedJsonState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const duplicateKeyState = await window.__archview.loadAnalysisFiles([new File(['{"schema":"invalid","schema":"archsig-run-manifest/v0.5.4"}'], 'archsig-run-manifest.json', { type: 'application/json' })], 'duplicate key directory');
        const duplicateKey = { status: duplicateKeyState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const schemaMismatchState = await window.__archview.loadAnalysisObject({ ...bundle, summary: { ...summary, schema: 'unsupported-summary/v9' } }, 'schema mismatch browser bundle');
        const schemaMismatch = { status: schemaMismatchState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const invalidProfileState = await window.__archview.loadAnalysisObject({ ...bundle, packet: { ...packet, profile: { schema: packet.profile.schema, profileId: packet.profile.profileId } } }, 'invalid profile bundle');
        const invalidProfile = { status: invalidProfileState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const incompleteDigestsState = await window.__archview.loadAnalysisObject({ ...bundle, manifest: { ...manifest, inputDigests: { archmap: inputDigests.archmap } } }, 'incomplete digest bundle');
        const incompleteDigests = { status: incompleteDigestsState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const componentMismatchState = await window.__archview.loadAnalysisObject({ ...bundle, manifest: { ...manifest, componentFingerprints: { ...componentFingerprints, lawPolicy: 'sha256:' + 'f'.repeat(64) } } }, 'component fingerprint mismatch bundle');
        const componentMismatch = { status: componentMismatchState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const foreignRunId = 'run:not-derived';
        const runIdMismatchState = await window.__archview.loadAnalysisObject({ ...bundle, ...Object.fromEntries(['manifest', 'normalized', 'packet', 'summary', 'insight'].map((name) => [name, { ...bundle[name], runId: foreignRunId }])) }, 'run id mismatch bundle');
        const runIdMismatch = { status: runIdMismatchState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const mismatchState = await window.__archview.loadAnalysisObject({ ...bundle, manifest: { ...manifest, inputDigests: { ...inputDigests, archmap: { ...inputDigests.archmap, sha256: '0'.repeat(64) } } } }, 'mismatch browser bundle');
        const mismatch = { status: mismatchState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const unresolvedInsight = { ...insight, actionQueue: [{ ...insight.actionQueue[0], targetRefs: ['atom:missing-from-archmap'] }] };
        const unresolvedState = await window.__archview.loadAnalysisObject({ ...bundle, insight: unresolvedInsight }, 'unresolved browser bundle');
        const unresolved = { status: unresolvedState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const invalidNormalized = { ...normalized, contexts: normalized.contexts.map((row, position) => position ? row : { ...row, atomIds: ['atom:missing-from-archmap'] }) };
        const normalizedState = await window.__archview.loadAnalysisObject({ ...bundle, normalized: invalidNormalized }, 'invalid normalized bridge bundle');
        const normalizedInternal = { status: normalizedState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const swappedAtoms = normalized.atoms.map((row) => ({ ...row }));
        [swappedAtoms[0].normalizedAtomId, swappedAtoms[1].normalizedAtomId] = [swappedAtoms[1].normalizedAtomId, swappedAtoms[0].normalizedAtomId];
        const swappedState = await window.__archview.loadAnalysisObject({ ...bundle, normalized: { ...normalized, atoms: swappedAtoms } }, 'swapped normalized ids');
        const swappedNormalized = { status: swappedState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const invalidRowState = await window.__archview.loadAnalysisObject({ ...bundle, packet: { ...packet, structuralVerdict: [42] } }, 'invalid packet row');
        const invalidRow = { status: invalidRowState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const invalidCardState = await window.__archview.loadAnalysisObject({ ...bundle, insight: { ...insight, insightCards: [42] } }, 'invalid insight card');
        const invalidCard = { status: invalidCardState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const forgedConclusionState = await window.__archview.loadAnalysisObject({ ...bundle, summary: { ...summary, conclusion: 'FORGED_CONCLUSION' } }, 'forged conclusion');
        const forgedConclusion = { status: forgedConclusionState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const edgePacket = { ...packet, computedInvariants: [{ invariantId: 'edge-probe', kind: 'measurement-invariant', edgeRefs: ['ctx:missing->ctx:checkout'] }] };
        const edgeState = await window.__archview.loadAnalysisObject({ ...bundle, packet: edgePacket }, 'unresolved edge');
        const unresolvedEdge = { status: edgeState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const malformedGateState = await window.__archview.loadAnalysisObject({ ...bundle, gate: { schema: gate.schema } }, 'malformed gate bundle');
        const malformedGate = { status: malformedGateState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const malformedComparisonState = await window.__archview.loadAnalysisObject({ ...bundle, comparison: { schema: comparison.schema, toolVersion: comparison.toolVersion, inputDigests: { baseRun: {}, headRun: {} }, nonConclusions: [] } }, 'malformed comparison bundle');
        const malformedComparison = { status: malformedComparisonState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const gateMismatchState = await window.__archview.loadAnalysisObject({ ...bundle, gate: { ...gate, inputDigests: { ...gate.inputDigests, measurementPacket: { path: 'input:archsig-measurement-packet.json', sha256: 'f'.repeat(64) } } } }, 'gate mismatch browser bundle');
        const gateMismatch = { status: gateMismatchState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const comparisonMismatchState = await window.__archview.loadAnalysisObject({ ...bundle, gate: { ...gate, inputDigests: { ...gate.inputDigests, comparisonReport: { path: 'input:archsig-comparison-report.json', sha256: 'e'.repeat(64) } } } }, 'comparison digest mismatch bundle');
        const comparisonMismatch = { status: comparisonMismatchState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const mutable = structuredClone(bundle);
        await window.__archview.loadAnalysisObject(mutable, 'mutation isolation');
        mutable.packet.structuralVerdict.push(42);
        const mutationIsolation = { status: window.__archviewState.analysis.status, rows: window.__archviewState.analysis.bundle.artifacts.packet.structuralVerdict.length };
        const numericPacket = { ...packet, computedInvariants: [{ invariantId: 'numeric-probe', kind: 'measurement-invariant', value: { epsilon: 0.000001, large: 100000000000000000000 } }] };
        const rustPacketCanonical = canonicalJson(numericPacket).replace('0.000001', '1e-6').replace('100000000000000000000', '1e+20');
        const numericPacketDigest = await sha256Hex(rustPacketCanonical);
        const numericComparison = { ...comparison, inputDigests: { ...comparison.inputDigests, headRun: { ...comparison.inputDigests.headRun, measurementPacket: { ...comparison.inputDigests.headRun.measurementPacket, sha256: numericPacketDigest } } } };
        const numericComparisonDigest = await sha256Hex(numericComparison);
        const numericGate = { ...gate, inputDigests: { ...gate.inputDigests, measurementPacket: { ...gate.inputDigests.measurementPacket, sha256: numericPacketDigest }, comparisonReport: { ...gate.inputDigests.comparisonReport, sha256: numericComparisonDigest } } };
        const numericFiles = Object.entries({ ...runFiles, 'archsig-measurement-packet.json': numericPacket, 'archsig-comparison-report.json': numericComparison, 'archsig-gate-report.json': numericGate }).map(([name, value]) => {
          let contents = JSON.stringify(value);
          if (name === 'archsig-measurement-packet.json') contents = contents.replace('0.000001', '1e-6').replace('100000000000000000000', '1e+20');
          return new File([contents], name, { type: 'application/json' });
        });
        let numericCanonical;
        try {
          const numericDocuments = await documentsFromFiles(numericFiles);
          const numericResult = await validateAnalysisBundle(numericDocuments, index);
          numericCanonical = { status: 'accepted', packetDigest: numericResult.packetDigest };
        } catch (error) { numericCanonical = { status: error.status, issues: error.issues?.map((entry) => entry.message) || [error.message] }; }
        const mixedFiles = Object.entries(runFiles).map(([name, value], position) => {
          const file = new File([JSON.stringify(value)], name, { type: 'application/json' });
          Object.defineProperty(file, 'webkitRelativePath', { value: (position ? 'run-b/' : 'run-a/') + name });
          return file;
        });
        const mixedState = await window.__archview.loadAnalysisFiles(mixedFiles, 'mixed directories');
        const mixedDirectory = { status: mixedState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        await window.__archview.loadAnalysisObject(bundle, 'accepted before malformed url');
        const malformedUrlState = await window.__archview.loadAnalysisUrl('http://[');
        const malformedUrl = { status: malformedUrlState.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        const stalePromise = window.__archview.loadAnalysisObject(bundle, 'stale analysis probe');
        window.__archview.loadObject({ schema: 'archmap/v0.5.4', id: 'race-replacement', sources: {}, atoms: [], contexts: [], covers: [] }, 'race replacement ArchMap');
        await stalePromise;
        const staleRace = { status: window.__archviewState.analysis.status, repository: window.__archviewState.repository };
        await window.__archview.loadUrl('./fixtures/vertical-slice.archmap.json');
        await window.__archview.loadAnalysisUrl('./redirect-run');
        const redirected = { status: window.__archviewState.analysis.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        await window.__archview.loadAnalysisUrl('https://example.invalid/run');
        const crossOrigin = { status: window.__archviewState.analysis.status, issues: [...document.querySelectorAll('#analysis-issues li')].map((item) => item.textContent) };
        await window.__archview.loadUrl('./fixtures/vertical-slice.archmap.json');
        const absent = { status: window.__archviewState.analysis.status, label: document.querySelector('#analysis-input-status').textContent };
        return {
          accepted, malformedJson, duplicateKey, schemaMismatch, invalidProfile, incompleteDigests, componentMismatch, runIdMismatch, mismatch, unresolved, normalizedInternal, swappedNormalized, invalidRow, invalidCard, forgedConclusion, unresolvedEdge, malformedGate, malformedComparison, gateMismatch, comparisonMismatch, mutationIsolation, numericCanonical, mixedDirectory, malformedUrl, staleRace, redirected, crossOrigin, absent,
        };
      })()`,
    });
    const analysisValue = analysisCases.result.value;
    if (analysisValue.accepted.status !== "accepted" || analysisValue.accepted.shellStatus !== "accepted" || analysisValue.accepted.label !== "Analysis accepted" || !/^run:[0-9a-f]{12}$/.test(analysisValue.accepted.runId) || analysisValue.accepted.profile !== "profile:browser@1" || !/^[0-9a-f]{64}$/.test(analysisValue.accepted.packetDigest)) {
      throw new Error(`Compatible ArchSig run was not accepted with visible identity: ${JSON.stringify(analysisValue)}`);
    }
    if (analysisValue.malformedJson.status !== "malformed" || !analysisValue.malformedJson.issues.some((entry) => entry.includes("not valid JSON")) || analysisValue.schemaMismatch.status !== "malformed" || !analysisValue.schemaMismatch.issues.some((entry) => entry.includes("must use archsig-analysis-summary/v0.5.4"))) {
      throw new Error(`Malformed JSON or ArchSig schema was not rejected fail-closed: ${JSON.stringify(analysisValue)}`);
    }
    if (analysisValue.duplicateKey.status !== "malformed" || !analysisValue.duplicateKey.issues.some((entry) => entry.includes("Duplicate object key")) || analysisValue.invalidRow.status !== "malformed" || analysisValue.invalidCard.status !== "malformed" || analysisValue.forgedConclusion.status !== "malformed") {
      throw new Error(`Duplicate keys, invalid rows, or forged conclusions were accepted: ${JSON.stringify(analysisValue)}`);
    }
    if (analysisValue.invalidProfile.status !== "malformed" || !analysisValue.invalidProfile.issues.some((entry) => entry.includes("profile.siteRef")) || analysisValue.incompleteDigests.status !== "malformed" || !analysisValue.incompleteDigests.issues.some((entry) => entry.includes("lawPolicy"))) {
      throw new Error(`Partial ArchSig profile or input digest contract was accepted: ${JSON.stringify(analysisValue)}`);
    }
    if (analysisValue.componentMismatch.status !== "mismatch" || !analysisValue.componentMismatch.issues.some((entry) => entry.includes("component fingerprints")) || analysisValue.runIdMismatch.status !== "mismatch" || !analysisValue.runIdMismatch.issues.some((entry) => entry.includes("not derived"))) {
      throw new Error(`Component fingerprints or derived run id mismatch was accepted: ${JSON.stringify(analysisValue)}`);
    }
    if (analysisValue.mismatch.status !== "mismatch" || !analysisValue.mismatch.issues.some((entry) => entry.includes("different run") || entry.includes("input digests"))) {
      throw new Error(`ArchMap digest mismatch was not rejected fail-closed: ${JSON.stringify(analysisValue)}`);
    }
    if (analysisValue.unresolved.status !== "unresolved" || !analysisValue.unresolved.issues.some((entry) => entry.includes("atom:missing-from-archmap")) || analysisValue.normalizedInternal.status !== "unresolved" || !analysisValue.normalizedInternal.issues.some((entry) => entry.includes("atom:missing-from-archmap"))) {
      throw new Error(`Unresolved normalized ID was not rejected fail-closed: ${JSON.stringify(analysisValue)}`);
    }
    if (analysisValue.swappedNormalized.status !== "unresolved" || !analysisValue.swappedNormalized.issues.some((entry) => entry.includes("deterministic ArchSig projection")) || analysisValue.unresolvedEdge.status !== "unresolved" || !analysisValue.unresolvedEdge.issues.some((entry) => entry.includes("explicit ArchMap Context relation"))) {
      throw new Error(`Swapped normalized identity or unresolved edge was accepted: ${JSON.stringify(analysisValue)}`);
    }
    if (analysisValue.malformedGate.status !== "malformed" || !analysisValue.malformedGate.issues.some((entry) => entry.includes("archsig-gate-report.json")) || analysisValue.malformedComparison.status !== "malformed" || !analysisValue.malformedComparison.issues.some((entry) => entry.includes("archsig-comparison-report.json"))) {
      throw new Error(`Malformed optional gate artifact was not rejected fail-closed: ${JSON.stringify(analysisValue)}`);
    }
    if (analysisValue.gateMismatch.status !== "mismatch" || !analysisValue.gateMismatch.issues.some((entry) => entry.includes("packet digest"))) {
      throw new Error(`Measurement packet digest mismatch was not rejected fail-closed: ${JSON.stringify(analysisValue)}`);
    }
    if (analysisValue.comparisonMismatch.status !== "mismatch" || !analysisValue.comparisonMismatch.issues.some((entry) => entry.includes("comparison digest"))) {
      throw new Error(`Gate comparison digest mismatch was not rejected fail-closed: ${JSON.stringify(analysisValue)}`);
    }
    if (analysisValue.mutationIsolation.status !== "accepted" || analysisValue.mutationIsolation.rows !== 0 || analysisValue.numericCanonical.status !== "accepted" || analysisValue.mixedDirectory.status !== "malformed" || !analysisValue.mixedDirectory.issues.some((entry) => entry.includes("one run directory")) || analysisValue.malformedUrl.status === "accepted") {
      throw new Error(`Accepted artifacts remained mutable, mixed directories passed, or malformed URL kept accepted state: ${JSON.stringify(analysisValue)}`);
    }
    if (analysisValue.staleRace.status !== "absent" || analysisValue.staleRace.repository !== "race-replacement" || analysisValue.redirected.status !== "mismatch" || !analysisValue.redirected.issues.some((entry) => entry.includes("must not redirect")) || analysisValue.crossOrigin.status !== "mismatch" || !analysisValue.crossOrigin.issues.some((entry) => entry.includes("current origin")) || analysisValue.absent.status !== "absent" || analysisValue.absent.label !== "No analysis loaded") {
      throw new Error(`Cross-origin or absent analysis state was not explicit: ${JSON.stringify(analysisValue)}`);
    }
    if (!analysisValue.accepted.architectureStable || analysisValue.accepted.unsupportedScalarRendered || analysisValue.accepted.candidateRendered) {
      throw new Error(`Rejected or unsupported analysis changed Architecture or rendered unsupported data: ${JSON.stringify(analysisValue)}`);
    }

    if (screenshotPath) {
      const screenshot = await page.send("Page.captureScreenshot", { format: "png", captureBeyondViewport: false });
      fs.mkdirSync(path.dirname(screenshotPath), { recursive: true });
      fs.writeFileSync(screenshotPath, Buffer.from(screenshot.data, "base64"));
    }

    await page.send("Page.navigate", { url: `http://127.0.0.1:${port}/index.html?archmap=./fixtures/empty.archmap.json` });
    await waitFor(page, "window.__archviewState?.architecture?.status === 'empty'");
    const empty = await page.send("Runtime.evaluate", {
      returnByValue: true,
      expression: `(() => ({
        status: document.querySelector('#archview-app').dataset.inputStatus,
        title: document.querySelector('#empty-state-title').textContent,
        visible: !document.querySelector('#atlas-empty-state').hidden,
        counts: window.__archviewState.architecture.index.counts,
      }))()`,
    });
    if (empty.result.value.status !== "empty" || empty.result.value.title !== "Empty ArchMap" || !empty.result.value.visible) {
      throw new Error(`Empty ArchMap state is not explicit: ${JSON.stringify(empty.result.value)}`);
    }

    await page.send("Page.navigate", { url: `http://127.0.0.1:${port}/index.html?archmap=./fixtures/malformed.archmap.json` });
    await waitFor(page, "window.__archviewState?.architecture?.status === 'error'");
    const malformed = await page.send("Runtime.evaluate", {
      returnByValue: true,
      expression: `(() => ({
        status: document.querySelector('#archview-app').dataset.inputStatus,
        title: document.querySelector('#empty-state-title').textContent,
        issues: [...document.querySelectorAll('#archmap-issues li')].map((item) => item.textContent),
        shellVisible: document.querySelector('.scope-explorer').getBoundingClientRect().width > 0,
      }))()`,
    });
    if (malformed.result.value.status !== "error" || malformed.result.value.title !== "ArchMap rejected" || !malformed.result.value.issues.length || !malformed.result.value.shellVisible) {
      throw new Error(`Malformed ArchMap was not visibly rejected: ${JSON.stringify(malformed.result.value)}`);
    }

    await page.send("Page.navigate", { url: `http://127.0.0.1:${port}/index.html?archmap=./fixtures/unresolved.archmap.json` });
    await waitFor(page, "window.__archviewState?.architecture?.status === 'unresolved'");
    const unresolved = await page.send("Runtime.evaluate", {
      returnByValue: true,
      expression: `(() => {
        document.querySelector('[data-atom-id="atom:unresolved"]').click();
        return {
          status: document.querySelector('#archview-app').dataset.inputStatus,
          issues: [...document.querySelectorAll('#archmap-issues li')].map((item) => item.textContent),
          selection: window.__archviewState.selection,
          resolution: document.querySelector('#source-resolution').textContent,
          sourceTarget: document.querySelector('#source-targets').textContent,
        };
      })()`,
    });
    if (unresolved.result.value.status !== "unresolved" || !unresolved.result.value.issues.some((entry) => entry.includes("src:missing")) || unresolved.result.value.selection?.id !== "atom:unresolved" || unresolved.result.value.resolution !== "UNRESOLVED" || !unresolved.result.value.sourceTarget.includes("unresolved source ref")) {
      throw new Error(`Unresolved source ref was silently discarded: ${JSON.stringify(unresolved.result.value)}`);
    }
    if (runtimeErrors.length || consoleErrors.length) {
      throw new Error(`Input cases emitted runtime or console errors: ${JSON.stringify({ runtimeErrors, consoleErrors })}`);
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
    await page.send("Page.navigate", { url: `http://127.0.0.1:${port}/index.html?webgl-unavailable=1&archmap=none` });
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

    await page.send("Page.navigate", { url: `http://127.0.0.1:${port}/index.html?bootstrap-unavailable=1&archmap=none` });
    await waitFor(page, "document.querySelector('#archview-app')?.dataset.phase === 'error'");
    const bootstrapFailure = await page.send("Runtime.evaluate", {
      returnByValue: true,
      expression: `(() => ({
        phase: document.querySelector('#archview-app').dataset.phase,
        errorVisible: !document.querySelector('#webgl-error').hidden,
        message: document.querySelector('#webgl-error-message').textContent,
        shellVisible: document.querySelector('.scope-explorer').getBoundingClientRect().width > 0,
      }))()`,
    });
    if (bootstrapFailure.result.value.phase !== "error" || !bootstrapFailure.result.value.errorVisible || !bootstrapFailure.result.value.shellVisible) {
      throw new Error(`Bootstrap failure was not shown in the shell: ${JSON.stringify(bootstrapFailure.result.value)}`);
    }

    console.log(JSON.stringify({ normal: value, analysis: analysisValue, empty: empty.result.value, malformed: malformed.result.value, unresolved: unresolved.result.value, webglFailure: failure.result.value, bootstrapFailure: bootstrapFailure.result.value }));
  } finally {
    await cdp.send("Target.closeTarget", { targetId: target.targetId }).catch(() => {});
    cdp.close();
    browser.kill();
    server.close();
  }
}

main().catch((error) => { console.error(error.stack || error); process.exit(1); });
