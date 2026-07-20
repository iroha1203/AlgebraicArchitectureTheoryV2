import { buildArchMapIndex, loadArchMapFromUrl, parseArchMap } from "./archmap.js";
import { buildArchitectureLayout } from "./layout.js";
import { createArchViewState, MODES } from "./state.js";

const DEFAULT_ARCHMAP_URL = "./fixtures/vertical-slice.archmap.json";
const MODE_COPY = Object.freeze({
  architecture: { heading: "Architecture inspector", title: "No architecture loaded", copy: "Load an ArchMap to compose Contexts and Atoms.", summary: "Select a Cover, Context, Subject, Atom, or Source.", analysis: "No analysis loaded" },
  analysis: { heading: "Analysis inspector", title: "No analysis loaded", copy: "Architecture remains available when compatible ArchSig artifacts are loaded in a later stage.", summary: "Select a finding after loading compatible analysis artifacts.", analysis: "No analysis loaded" },
  improve: { heading: "Improve inspector", title: "No improvement target selected", copy: "Explicit evidence and repair targets will appear here after analysis is loaded.", summary: "Select an explicit repair target after loading compatible analysis artifacts.", analysis: "No analysis loaded" },
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
  return value?.label || value?.id || "—";
}

function selectionButton(label, data, current, onClick, count = null) {
  const button = document.createElement("button");
  button.type = "button";
  Object.assign(button.dataset, data);
  button.setAttribute("aria-current", String(current));
  button.append(document.createTextNode(label));
  if (count !== null) {
    const badge = document.createElement("span");
    badge.className = "item-count";
    badge.textContent = String(count);
    button.append(badge);
  }
  button.addEventListener("click", onClick);
  return button;
}

function visibleContexts(index, coverId) {
  const cover = index.coversById.get(coverId);
  const ids = new Set((cover?.contexts || index.contexts.map((context) => context.id)).filter((id) => index.contextsById.has(id)));
  return index.contexts.filter((context) => ids.has(context.id));
}

function renderCoverIndex(container, snapshot, actions) {
  const index = snapshot.architecture.index;
  if (!index?.covers.length) return replaceWithEmpty(container, "No covers loaded");
  const list = document.createElement("ul");
  list.className = "index-list";
  for (const cover of index.covers) {
    const item = document.createElement("li");
    item.append(selectionButton(displayName(cover), { coverId: cover.id }, snapshot.cover === cover.id, () => actions.cover(cover.id), (cover.contexts || []).filter((id) => index.contextsById.has(id)).length));
    list.append(item);
  }
  container.replaceChildren(list);
}

function renderContextIndex(container, snapshot, actions) {
  const index = snapshot.architecture.index;
  const contexts = index ? visibleContexts(index, snapshot.cover) : [];
  if (!contexts.length) return replaceWithEmpty(container, "No contexts in selected Cover");
  const list = document.createElement("ul");
  list.className = "index-list context-index";
  for (const context of contexts) {
    const item = document.createElement("li");
    item.append(selectionButton(displayName(context), { contextId: context.id }, snapshot.selection?.kind === "context" && snapshot.selection.id === context.id, () => actions.context(context.id), (context.atoms || []).filter((id) => index.atomsById.has(id)).length));
    list.append(item);
  }
  container.replaceChildren(list);
}

function subjectsFor(index, contexts) {
  const values = [];
  for (const context of contexts) {
    const groups = new Map();
    for (const atomId of context.atoms || []) {
      const atom = index.atomsById.get(atomId);
      if (!atom) continue;
      const atoms = groups.get(atom.subject) || [];
      atoms.push(atom);
      groups.set(atom.subject, atoms);
    }
    for (const [subject, atoms] of groups) values.push({ id: `${context.id}::${subject}`, context, subject, atoms: atoms.sort((left, right) => left.id.localeCompare(right.id)) });
  }
  return values.sort((left, right) => left.id.localeCompare(right.id));
}

function renderSubjects(container, snapshot, actions) {
  const index = snapshot.architecture.index;
  const contexts = index ? visibleContexts(index, snapshot.cover) : [];
  const subjects = index ? subjectsFor(index, contexts) : [];
  if (!subjects.length) return replaceWithEmpty(container, "No subjects in selected Cover");
  const list = document.createElement("ul");
  list.className = "index-list subject-index";
  for (const group of subjects) {
    const item = document.createElement("li");
    const label = `${group.subject} · ${displayName(group.context)}`;
    const selected = snapshot.selection?.kind === "subject" && snapshot.selection.id === group.subject && snapshot.selection.contextId === group.context.id;
    item.append(selectionButton(label, { subject: group.subject, contextId: group.context.id }, selected, () => actions.subject(group.context.id, group.subject), group.atoms.length));
    for (const atom of group.atoms) {
      const atomSelected = snapshot.selection?.kind === "atom" && snapshot.selection.id === atom.id && (!snapshot.selection.contextId || snapshot.selection.contextId === group.context.id);
      item.append(selectionButton(`${displayName(atom)} · ${atom.kind}`, { atomId: atom.id, contextId: group.context.id }, atomSelected, () => actions.atom(atom.id, group.context.id)));
    }
    list.append(item);
  }
  container.replaceChildren(list);
}

function factRow(term, value) {
  const row = document.createElement("div");
  const name = document.createElement("dt");
  const content = document.createElement("dd");
  name.textContent = term;
  content.textContent = value === undefined || value === null || value === "" ? "—" : String(value);
  row.append(name, content);
  return row;
}

function refsForSelection(index, selection) {
  if (!selection) return [];
  if (selection.kind === "source") return [selection.id];
  if (selection.kind === "atom") return index.atomsById.get(selection.id)?.refs || [];
  if (selection.kind === "context") return index.contextsById.get(selection.id)?.refs || [];
  if (selection.kind === "cover") return index.coversById.get(selection.id)?.refs || [];
  if (selection.kind === "subject") {
    const context = index.contextsById.get(selection.contextId);
    return [...new Set((context?.atoms || []).map((id) => index.atomsById.get(id)).filter((atom) => atom?.subject === selection.id).flatMap((atom) => atom.refs || []))].sort();
  }
  return [];
}

function renderSourceTargets(container, index, refs, selection, actions) {
  if (!refs.length) return replaceWithEmpty(container, "No source refs supplied");
  const list = document.createElement("ul");
  list.className = "source-list";
  for (const ref of refs) {
    const source = index.sourcesById.get(ref) || null;
    const item = document.createElement("li");
    item.dataset.resolution = source ? "direct" : "unresolved";
    if (source) {
      const atomId = selection?.kind === "atom" ? selection.id : selection?.atomId || null;
      const button = selectionButton(`${ref} · ${source.path || "path unavailable"} · ${source.symbol || source.section || "symbol unavailable"} · ${source.line ?? "line unavailable"}`, { sourceId: ref }, selection?.kind === "source" && selection.id === ref, () => actions.source(ref, atomId));
      item.append(button);
    } else item.textContent = `${ref} · unresolved source ref`;
    list.append(item);
  }
  container.replaceChildren(list);
}

function selectedFacts(snapshot, layout) {
  const index = snapshot.architecture.index;
  const selection = snapshot.selection;
  if (!index || !selection) return null;
  if (selection.kind === "cover") {
    const cover = index.coversById.get(selection.id);
    if (!cover) return null;
    return { summary: `Cover · ${displayName(cover)}`, rows: [["Cover", cover.id], ["Contexts", (cover.contexts || []).filter((id) => index.contextsById.has(id)).join(", ")], ["Source refs", (cover.refs || []).length]] };
  }
  if (selection.kind === "context") {
    const context = index.contextsById.get(selection.id);
    const contextLayout = layout.contexts.find((value) => value.id === selection.id);
    if (!context) return null;
    return { summary: `Context · ${displayName(context)}`, rows: [["Context", context.id], ["Atoms", (context.atoms || []).filter((id) => index.atomsById.has(id)).length], ["Restricts to", (context.restrictsTo || []).join(", ")], ["Source refs", (context.refs || []).length], ["Restriction depth", contextLayout?.depth ?? 0]] };
  }
  if (selection.kind === "subject") {
    const context = index.contextsById.get(selection.contextId);
    const atoms = (context?.atoms || []).map((id) => index.atomsById.get(id)).filter((atom) => atom?.subject === selection.id).sort((left, right) => left.id.localeCompare(right.id));
    return { summary: `Subject group · ${selection.id}`, rows: [["Context", selection.contextId], ["Exact subject", selection.id], ["Atom kinds", atoms.map((atom) => atom.kind).join(", ")], ["Facts", atoms.map((atom) => [atom.predicate, atom.object].filter(Boolean).join(" ")).join("; ")], ["Layout grouping", "Atoms grouped by exact subject equality. This grouping does not create a new architectural fact."]] };
  }
  if (selection.kind === "atom") {
    const atom = index.atomsById.get(selection.id);
    if (!atom) return null;
    return { summary: `Atom · ${displayName(atom)}`, rows: [["Atom", atom.id], ["Fact", [atom.subject, atom.predicate, atom.object].filter(Boolean).join(" ")], ["Kind", atom.kind], ["Axis", atom.axis], ["Contexts", (index.contextIdsByAtom.get(atom.id) || []).join(", ")]] };
  }
  if (selection.kind === "source") {
    const source = index.sourcesById.get(selection.id);
    if (!source) return null;
    return { summary: `Source · ${selection.id}`, rows: [["Source", selection.id], ["Kind", source.kind], ["Path", source.path || source.source], ["Symbol", source.symbol || source.section], ["Line", source.line]] };
  }
  return null;
}

function renderSelection(snapshot, layout, actions) {
  const facts = requireElement("#architecture-facts");
  const targets = requireElement("#source-targets");
  const index = snapshot.architecture.index;
  const record = selectedFacts(snapshot, layout);
  requireElement("#inspector-summary").textContent = record?.summary || MODE_COPY[snapshot.mode].summary;
  if (!record || !index) {
    replaceWithEmpty(facts, "No selection");
    replaceWithEmpty(targets, "No source selected");
  } else {
    const description = document.createElement("dl");
    description.className = "fact-list";
    description.append(...record.rows.map(([term, value]) => factRow(term, value)));
    facts.replaceChildren(description);
    renderSourceTargets(targets, index, refsForSelection(index, snapshot.selection), snapshot.selection, actions);
  }

  const refs = index ? refsForSelection(index, snapshot.selection) : [];
  const selectedSource = snapshot.selection?.kind === "source" ? index?.sourcesById.get(snapshot.selection.id) : refs.map((ref) => index?.sourcesById.get(ref)).find(Boolean);
  requireElement("#source-path").textContent = selectedSource?.path || selectedSource?.source || "—";
  requireElement("#source-symbol").textContent = selectedSource?.symbol || selectedSource?.section || "—";
  requireElement("#source-line").textContent = selectedSource?.line === undefined ? "—" : String(selectedSource.line);
  requireElement("#source-resolution").textContent = selectedSource ? "DIRECT EVIDENCE" : "UNRESOLVED";
}

function renderBreadcrumb(snapshot, actions) {
  const index = snapshot.architecture.index;
  const selection = snapshot.selection;
  const items = [];
  if (snapshot.cover) items.push({ level: "cover", label: displayName(index?.coversById.get(snapshot.cover)), action: () => actions.cover(snapshot.cover) });
  const contextId = selection?.contextId || (selection?.kind === "context" ? selection.id : selection?.kind === "atom" ? index?.contextIdsByAtom.get(selection.id)?.[0] : null);
  if (contextId) items.push({ level: "context", label: displayName(index?.contextsById.get(contextId)), action: () => actions.context(contextId) });
  const subject = selection?.kind === "subject" ? selection.id : selection?.kind === "atom" ? index?.atomsById.get(selection.id)?.subject : null;
  if (subject && contextId) items.push({ level: "subject", label: subject, action: () => actions.subject(contextId, subject) });
  const atomId = selection?.kind === "atom" ? selection.id : selection?.atomId;
  if (atomId) items.push({ level: "atom", label: displayName(index?.atomsById.get(atomId)), action: () => actions.atom(atomId, contextId) });
  if (selection?.kind === "source") items.push({ level: "source", label: selection.id, action: () => actions.source(selection.id, selection.atomId) });
  const breadcrumb = requireElement("#semantic-breadcrumb");
  if (!items.length) return replaceWithEmpty(breadcrumb, "Cover → Context → Subject → Atom → Source");
  const nodes = [];
  items.forEach((item, position) => {
    if (position) {
      const separator = document.createElement("span");
      separator.setAttribute("aria-hidden", "true");
      separator.textContent = "›";
      nodes.push(separator);
    }
    const button = selectionButton(item.label, { zoomLevel: item.level }, snapshot.zoom === item.level, item.action);
    nodes.push(button);
  });
  breadcrumb.replaceChildren(...nodes);
}

function searchRecords(index, coverId, query) {
  const needle = query.trim().toLocaleLowerCase();
  if (!needle) return [];
  const contexts = visibleContexts(index, coverId);
  const contextIds = new Set(contexts.map((context) => context.id));
  const includes = (...values) => values.filter(Boolean).join(" ").toLocaleLowerCase().includes(needle);
  const results = [];
  for (const cover of index.covers) if (includes(cover.id, cover.label)) results.push({ kind: "cover", id: cover.id, label: `Cover · ${displayName(cover)}` });
  for (const context of contexts) if (includes(context.id, context.label)) results.push({ kind: "context", id: context.id, label: `Context · ${displayName(context)}` });
  for (const group of subjectsFor(index, contexts)) if (includes(group.subject)) results.push({ kind: "subject", id: group.subject, contextId: group.context.id, label: `Subject · ${group.subject} · ${displayName(group.context)}` });
  for (const atom of index.atoms) {
    const contextId = (index.contextIdsByAtom.get(atom.id) || []).find((id) => contextIds.has(id));
    if (contextId && includes(atom.id, atom.label, atom.kind, atom.subject, atom.axis, atom.predicate, atom.object)) results.push({ kind: "atom", id: atom.id, contextId, label: `Atom · ${displayName(atom)} · ${atom.kind}` });
  }
  for (const [id, source] of index.sources) if (includes(id, source.kind, source.path, source.source, source.symbol, source.section, source.line)) results.push({ kind: "source", id, label: `Source · ${source.path || source.source || id}` });
  return results.slice(0, 30);
}

function renderSearch(snapshot, actions) {
  const results = requireElement("#search-results");
  const query = requireElement("#architecture-search").value;
  const index = snapshot.architecture.index;
  const records = index ? searchRecords(index, snapshot.cover, query) : [];
  if (!query.trim()) return replaceWithEmpty(results, "Search explicit ids, facts, kinds, and source metadata");
  if (!records.length) return replaceWithEmpty(results, "No supplied fact matches");
  const list = document.createElement("ul");
  list.className = "index-list search-results";
  for (const record of records) {
    const item = document.createElement("li");
    const selectRecord = () => {
      if (record.kind === "cover") actions.cover(record.id);
      else if (record.kind === "context") actions.context(record.id);
      else if (record.kind === "subject") actions.subject(record.contextId, record.id);
      else if (record.kind === "atom") actions.atom(record.id, record.contextId);
      else if (record.kind === "source") actions.source(record.id);
    };
    item.append(selectionButton(record.label, { searchKind: record.kind, searchId: record.id }, false, selectRecord));
    list.append(item);
  }
  results.replaceChildren(list);
}

function renderArchitecture(snapshot, layout, actions) {
  const architecture = snapshot.architecture;
  const statusSection = requireElement(".input-status");
  statusSection.dataset.status = architecture.status;
  requireElement("#archmap-status").textContent = ({ idle: "No ArchMap loaded", loading: "Validating ArchMap…", loaded: "ArchMap loaded", empty: "Empty ArchMap loaded", unresolved: "ArchMap loaded with unresolved refs", error: "ArchMap rejected" })[architecture.status] || architecture.status;
  requireElement("#archmap-issues").replaceChildren(...architecture.issues.slice(0, 8).map((entry) => {
    const item = document.createElement("li");
    item.textContent = `${entry.path}: ${entry.message}`;
    return item;
  }));
  renderCoverIndex(requireElement("#cover-list"), snapshot, actions);
  renderContextIndex(requireElement("#context-list"), snapshot, actions);
  renderSubjects(requireElement("#subject-list"), snapshot, actions);
  renderSelection(snapshot, layout, actions);
  renderBreadcrumb(snapshot, actions);
  renderSearch(snapshot, actions);
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
  let renderedSignature = null;

  const actions = Object.freeze({
    cover(id) { state.selectCover(id); },
    context(id) { state.selectContext(id); },
    subject(contextId, subject) { state.selectSubject(contextId, subject); },
    atom(id, contextId = null) { state.selectAtom(id, contextId); atlasRenderer?.selectAtom(id); },
    source(id, atomId = null) { state.selectSource(id, atomId); },
  });
  const handleSceneSelection = (kind, id, contextId) => {
    if (kind === "context") actions.context(id);
    if (kind === "subject") actions.subject(contextId, id);
    if (kind === "atom") actions.atom(id, contextId);
  };
  const publishTestState = (snapshot) => {
    const publicState = { ...snapshot, modeCount: MODES.length, canvasCount: host.querySelectorAll("canvas").length };
    window.__archviewFoundationState = publicState;
    window.__archviewState = publicState;
  };

  state.subscribe((snapshot) => {
    const copy = MODE_COPY[snapshot.mode];
    const layout = buildArchitectureLayout(snapshot.architecture.index, snapshot.cover);
    window.__archviewLayout = layout;
    if (atlasRenderer && renderedSignature !== layout.signature) {
      window.__archviewRenderStats = atlasRenderer.setArchitecture(snapshot.architecture.index, layout, handleSceneSelection);
      renderedSignature = layout.signature;
    }
    root.dataset.mode = snapshot.mode;
    root.dataset.phase = snapshot.phase;
    root.dataset.inputStatus = snapshot.architecture.status;
    root.dataset.zoom = snapshot.zoom;
    requireElement("#repository-name").textContent = snapshot.repository || "No repository loaded";
    requireElement("#revision-name").textContent = snapshot.revision || "—";
    requireElement("#cover-name").textContent = snapshot.cover || "No cover selected";
    requireElement("#inspector-heading").textContent = copy.heading;
    requireElement("#analysis-status").textContent = copy.analysis;
    requireElement("#technical-mode").textContent = snapshot.mode;
    requireElement("#technical-zoom").textContent = snapshot.zoom;
    requireElement("#layout-signature").textContent = layout.signature === "empty" ? "empty" : `${layout.signature.length} deterministic bytes`;
    rendererStatus.textContent = snapshot.renderer;
    modeButtons.forEach((button) => button.setAttribute("aria-pressed", String(button.dataset.modeButton === snapshot.mode)));
    viewButtons.forEach((button) => { if (button.dataset.view !== "reset") button.setAttribute("aria-pressed", String(button.dataset.view === snapshot.view)); });
    emptyPanel.hidden = snapshot.architecture.status === "loaded" || snapshot.architecture.status === "unresolved";
    requireElement("#empty-state-title").textContent = snapshot.architecture.status === "empty" ? "Empty ArchMap" : snapshot.architecture.status === "error" ? "ArchMap rejected" : copy.title;
    requireElement("#empty-state-copy").textContent = snapshot.architecture.status === "empty" ? "The supplied ArchMap contains no sources, Atoms, Contexts, or Covers." : snapshot.architecture.status === "error" ? "Review the visible validation findings in Scope Explorer." : copy.copy;
    renderArchitecture(snapshot, layout, actions);
    publishTestState(snapshot);
  });

  modeButtons.forEach((button) => button.addEventListener("click", () => state.selectMode(button.dataset.modeButton)));
  requireElement("#architecture-search").addEventListener("input", () => renderSearch(state.read(), actions));
  requireElement("#overview-button").addEventListener("click", () => { state.overview(); atlasRenderer?.reset(); state.selectView("isometric"); });

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
    if (view === "reset") { atlasRenderer.reset(); state.selectView("isometric"); }
    else { atlasRenderer.setView(view); state.selectView(view); }
  }));

  const applyIndex = (index, source) => state.architectureLoaded(index, source);
  const rejectInput = (error, source) => {
    window.__archviewRenderStats = atlasRenderer?.setArchitecture(null, null, handleSceneSelection) || { contextPlates: 0, subjectGroups: 0, atomGlyphs: 0, restrictions: 0, sharedSupports: 0 };
    renderedSignature = null;
    state.architectureFailed(error, source);
  };
  const loadUrl = async (url) => { state.architectureLoading(url); try { applyIndex(await loadArchMapFromUrl(url), url); } catch (error) { rejectInput(error, url); } };
  const loadText = (text, source = "local file") => { state.architectureLoading(source); try { applyIndex(parseArchMap(text), source); } catch (error) { rejectInput(error, source); } };
  const loadObject = (document, source = "runtime object") => { state.architectureLoading(source); try { applyIndex(buildArchMapIndex(document), source); } catch (error) { rejectInput(error, source); } };
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
