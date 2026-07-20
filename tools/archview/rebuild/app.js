import { buildArchMapIndex, loadArchMapFromUrl, parseArchMap } from "./archmap.js";
import { createArchViewState, MODES } from "./state.js";

const DEFAULT_ARCHMAP_URL = "./fixtures/vertical-slice.archmap.json";
const MODE_COPY = Object.freeze({
  architecture: {
    heading: "Architecture inspector",
    title: "No architecture loaded",
    copy: "Load an ArchMap to compose Contexts and Atoms.",
    summary: "Select a Context or Atom after loading an ArchMap.",
    analysis: "No analysis loaded",
  },
  analysis: {
    heading: "Analysis inspector",
    title: "No analysis loaded",
    copy: "Architecture remains available when compatible ArchSig artifacts are loaded in a later stage.",
    summary: "Select a finding after loading compatible analysis artifacts.",
    analysis: "No analysis loaded",
  },
  improve: {
    heading: "Improve inspector",
    title: "No improvement target selected",
    copy: "Explicit evidence and repair targets will appear here after analysis is loaded.",
    summary: "Select an explicit repair target after loading compatible analysis artifacts.",
    analysis: "No analysis loaded",
  },
});

function requireElement(selector) {
  const element = document.querySelector(selector);
  if (!element) throw new Error(`Required ArchView element is missing: ${selector}`);
  return element;
}

function replaceWithEmpty(container, text) {
  const paragraph = document.createElement("p");
  paragraph.className = "empty-list";
  paragraph.textContent = text;
  container.replaceChildren(paragraph);
}

function displayName(value) {
  return value.label || value.id;
}

function renderSimpleIndex(container, values, emptyText, countFor = null) {
  if (!values.length) {
    replaceWithEmpty(container, emptyText);
    return;
  }
  const list = document.createElement("ul");
  list.className = "index-list";
  for (const value of values) {
    const item = document.createElement("li");
    const row = document.createElement("div");
    row.className = "index-item";
    row.textContent = displayName(value);
    if (countFor) {
      const count = document.createElement("span");
      count.className = "item-count";
      count.textContent = String(countFor(value));
      row.append(count);
    }
    item.append(row);
    list.append(item);
  }
  container.replaceChildren(list);
}

function renderContextIndex(container, index, selectAtom, selectedId) {
  if (!index.contexts.length) {
    replaceWithEmpty(container, "No contexts loaded");
    return;
  }
  const list = document.createElement("ul");
  list.className = "index-list context-index";
  for (const context of index.contexts) {
    const item = document.createElement("li");
    const row = document.createElement("div");
    row.className = "index-item context-row";
    row.textContent = displayName(context);
    const count = document.createElement("span");
    count.className = "item-count";
    count.textContent = String((context.atoms || []).filter((atomId) => index.atomsById.has(atomId)).length);
    row.append(count);
    item.append(row);
    for (const atomId of context.atoms || []) {
      const atom = index.atomsById.get(atomId);
      if (!atom) continue;
      const button = document.createElement("button");
      button.type = "button";
      button.dataset.atomId = atom.id;
      button.setAttribute("aria-current", String(selectedId === atom.id));
      button.textContent = displayName(atom);
      button.addEventListener("click", () => selectAtom(atom.id));
      item.append(button);
    }
    list.append(item);
  }
  container.replaceChildren(list);
}

function renderSubjects(container, index, selectAtom, selectedId) {
  const bySubject = new Map();
  for (const atom of index.atoms) {
    const members = bySubject.get(atom.subject) || [];
    members.push(atom);
    bySubject.set(atom.subject, members);
  }
  const subjects = [...bySubject].sort(([left], [right]) => left.localeCompare(right));
  if (!subjects.length) {
    replaceWithEmpty(container, "No subjects loaded");
    return;
  }
  const list = document.createElement("ul");
  list.className = "index-list";
  for (const [subject, atoms] of subjects) {
    const item = document.createElement("li");
    const button = document.createElement("button");
    button.type = "button";
    button.dataset.subject = subject;
    button.setAttribute("aria-current", String(atoms.some((atom) => atom.id === selectedId)));
    button.textContent = subject;
    const count = document.createElement("span");
    count.className = "item-count";
    count.textContent = String(atoms.length);
    button.append(count);
    button.addEventListener("click", () => selectAtom(atoms[0].id));
    item.append(button);
    list.append(item);
  }
  container.replaceChildren(list);
}

function factRow(term, value) {
  const row = document.createElement("div");
  const name = document.createElement("dt");
  const content = document.createElement("dd");
  name.textContent = term;
  content.textContent = value || "—";
  row.append(name, content);
  return row;
}

function sourceLanding(index, atom) {
  return (atom.refs || []).map((ref) => ({ ref, source: index.sourcesById.get(ref) || null }));
}

function renderSelection(snapshot) {
  const facts = requireElement("#architecture-facts");
  const targets = requireElement("#source-targets");
  const index = snapshot.architecture.index;
  const atom = snapshot.selection?.kind === "atom" ? index?.atomsById.get(snapshot.selection.id) : null;
  if (!atom || !index) {
    replaceWithEmpty(facts, "No selection");
    replaceWithEmpty(targets, "No source selected");
    requireElement("#source-path").textContent = "—";
    requireElement("#source-symbol").textContent = "—";
    requireElement("#source-line").textContent = "—";
    requireElement("#source-resolution").textContent = "UNRESOLVED";
    return;
  }

  const description = document.createElement("dl");
  description.className = "fact-list";
  const contexts = index.contextIdsByAtom.get(atom.id) || [];
  description.append(
    factRow("Atom", atom.id),
    factRow("Fact", [atom.subject, atom.predicate, atom.object].filter(Boolean).join(" ")),
    factRow("Kind", atom.kind),
    factRow("Axis", atom.axis),
    factRow("Contexts", contexts.join(", "))
  );
  facts.replaceChildren(description);

  const landings = sourceLanding(index, atom);
  if (!landings.length) replaceWithEmpty(targets, "Atom has no source refs");
  else {
    const list = document.createElement("ul");
    list.className = "source-list";
    for (const landing of landings) {
      const item = document.createElement("li");
      item.dataset.resolution = landing.source ? "direct" : "unresolved";
      item.textContent = landing.source
        ? `${landing.ref} · ${landing.source.path || "path unavailable"} · ${landing.source.symbol || landing.source.section || "symbol unavailable"} · ${landing.source.line ?? "line unavailable"}`
        : `${landing.ref} · unresolved source ref`;
      list.append(item);
    }
    targets.replaceChildren(list);
  }

  const primary = landings.find((landing) => landing.source) || landings[0] || null;
  requireElement("#source-path").textContent = primary?.source?.path || "—";
  requireElement("#source-symbol").textContent = primary?.source?.symbol || "—";
  requireElement("#source-line").textContent = primary?.source?.line === undefined ? "—" : String(primary.source.line);
  requireElement("#source-resolution").textContent = primary?.source ? "DIRECT EVIDENCE" : "UNRESOLVED";
}

function renderArchitecture(snapshot, selectAtom) {
  const architecture = snapshot.architecture;
  const statusSection = requireElement(".input-status");
  statusSection.dataset.status = architecture.status;
  const status = requireElement("#archmap-status");
  const issues = requireElement("#archmap-issues");
  status.textContent = {
    idle: "No ArchMap loaded",
    loading: "Validating ArchMap…",
    loaded: "ArchMap loaded",
    empty: "Empty ArchMap loaded",
    unresolved: "ArchMap loaded with unresolved refs",
    error: "ArchMap rejected",
  }[architecture.status] || architecture.status;
  issues.replaceChildren(...architecture.issues.slice(0, 8).map((entry) => {
    const item = document.createElement("li");
    item.textContent = `${entry.path}: ${entry.message}`;
    return item;
  }));

  const index = architecture.index;
  if (!index) {
    replaceWithEmpty(requireElement("#cover-list"), "No covers loaded");
    replaceWithEmpty(requireElement("#context-list"), "No contexts loaded");
    replaceWithEmpty(requireElement("#subject-list"), "No subjects loaded");
    renderSelection(snapshot);
    return;
  }
  renderSimpleIndex(requireElement("#cover-list"), index.covers, "No covers loaded", (cover) => (cover.contexts || []).filter((id) => index.contextsById.has(id)).length);
  renderContextIndex(requireElement("#context-list"), index, selectAtom, snapshot.selection?.id);
  renderSubjects(requireElement("#subject-list"), index, selectAtom, snapshot.selection?.id);
  renderSelection(snapshot);
}

export async function startArchView() {
  const root = requireElement("#archview-app");
  const host = requireElement("#atlas-canvas-host");
  const emptyPanel = requireElement("#atlas-empty-state");
  const errorPanel = requireElement("#webgl-error");
  const errorMessage = requireElement("#webgl-error-message");
  const rendererStatus = requireElement("#renderer-status");
  const modeButtons = [...document.querySelectorAll("[data-mode-button]")];
  const viewButtons = [...document.querySelectorAll("[data-view]")];
  const state = createArchViewState();
  let atlasRenderer = null;

  const selectAtom = (atomId) => {
    state.selectAtom(atomId);
    atlasRenderer?.selectAtom(atomId);
  };

  const publishTestState = (snapshot) => {
    const publicState = { ...snapshot, modeCount: MODES.length, canvasCount: host.querySelectorAll("canvas").length };
    window.__archviewFoundationState = publicState;
    window.__archviewState = publicState;
  };

  state.subscribe((snapshot) => {
    const copy = MODE_COPY[snapshot.mode];
    root.dataset.mode = snapshot.mode;
    root.dataset.phase = snapshot.phase;
    root.dataset.inputStatus = snapshot.architecture.status;
    requireElement("#repository-name").textContent = snapshot.repository || "No repository loaded";
    requireElement("#revision-name").textContent = snapshot.revision || "—";
    requireElement("#cover-name").textContent = snapshot.cover || "No cover selected";
    requireElement("#inspector-heading").textContent = copy.heading;
    requireElement("#inspector-summary").textContent = snapshot.selection ? `Selected ${snapshot.selection.id}` : copy.summary;
    requireElement("#analysis-status").textContent = copy.analysis;
    requireElement("#technical-mode").textContent = snapshot.mode;
    rendererStatus.textContent = snapshot.renderer;
    modeButtons.forEach((button) => button.setAttribute("aria-pressed", String(button.dataset.modeButton === snapshot.mode)));
    viewButtons.forEach((button) => {
      if (button.dataset.view !== "reset") button.setAttribute("aria-pressed", String(button.dataset.view === snapshot.view));
    });

    const architecture = snapshot.architecture;
    emptyPanel.hidden = architecture.status === "loaded" || architecture.status === "unresolved";
    requireElement("#empty-state-title").textContent = architecture.status === "empty" ? "Empty ArchMap" : architecture.status === "error" ? "ArchMap rejected" : copy.title;
    requireElement("#empty-state-copy").textContent = architecture.status === "empty" ? "The supplied ArchMap contains no sources, Atoms, Contexts, or Covers." : architecture.status === "error" ? "Review the visible validation findings in Scope Explorer." : copy.copy;
    renderArchitecture(snapshot, selectAtom);
    publishTestState(snapshot);
  });

  modeButtons.forEach((button) => button.addEventListener("click", () => state.selectMode(button.dataset.modeButton)));

  try {
    const { createAtlasRenderer } = await import("./renderer.js");
    atlasRenderer = createAtlasRenderer(host);
    errorPanel.hidden = true;
    state.rendererReady();
  } catch (error) {
    errorMessage.textContent = error instanceof Error ? error.message : String(error);
    errorPanel.hidden = false;
    state.rendererFailed(error);
  }

  viewButtons.forEach((button) => button.addEventListener("click", () => {
    if (!atlasRenderer) return;
    const view = button.dataset.view;
    if (view === "reset") {
      atlasRenderer.reset();
      state.selectView("isometric");
    } else {
      atlasRenderer.setView(view);
      state.selectView(view);
    }
  }));

  const applyIndex = (index, source) => {
    window.__archviewRenderStats = atlasRenderer?.setArchitecture(index, selectAtom) || { contextPlates: 0, atomGlyphs: 0 };
    state.architectureLoaded(index, source);
  };
  const rejectInput = (error, source) => {
    window.__archviewRenderStats = atlasRenderer?.setArchitecture(null, selectAtom) || { contextPlates: 0, atomGlyphs: 0 };
    state.architectureFailed(error, source);
  };
  const loadUrl = async (url) => {
    state.architectureLoading(url);
    try { applyIndex(await loadArchMapFromUrl(url), url); }
    catch (error) { rejectInput(error, url); }
  };
  const loadText = (text, source = "local file") => {
    state.architectureLoading(source);
    try { applyIndex(parseArchMap(text), source); }
    catch (error) { rejectInput(error, source); }
  };
  const loadObject = (document, source = "runtime object") => {
    state.architectureLoading(source);
    try { applyIndex(buildArchMapIndex(document), source); }
    catch (error) { rejectInput(error, source); }
  };

  requireElement("#archmap-file").addEventListener("change", async (event) => {
    const file = event.target.files?.[0];
    if (file) loadText(await file.text(), file.name);
    event.target.value = "";
  });

  const parameters = new URLSearchParams(location.search);
  const requestedArchMap = parameters.get("archmap");
  if (requestedArchMap !== "none") await loadUrl(requestedArchMap || DEFAULT_ARCHMAP_URL);

  const dispose = () => atlasRenderer?.dispose();
  window.addEventListener("pagehide", dispose, { once: true });
  window.__archview = Object.freeze({ state, loadUrl, loadText, loadObject, dispose });
  return state.read();
}
