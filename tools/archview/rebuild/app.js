import { buildArchMapIndex, loadArchMapFromUrl, parseArchMap } from "./archmap.js";
import { documentsFromFiles, documentsFromUrl, validateAnalysisBundle } from "./analysis.js";
import { buildAnalysisView } from "./analysis-view.js";
import { buildArchitectureLayout } from "./layout.js";
import { createArchViewState, MODES } from "./state.js";

const DEFAULT_ARCHMAP_URL = "./fixtures/vertical-slice.archmap.json";
const MODE_COPY = Object.freeze({
  architecture: { heading: "Architecture inspector", title: "No architecture loaded", copy: "Load an ArchMap to compose Contexts and Atoms.", summary: "Select a Cover, Context, Subject, Atom, or Source." },
  analysis: { heading: "Analysis inspector", title: "No analysis loaded", copy: "Load compatible ArchSig artifacts to inspect the current Architecture.", summary: "Select a finding after loading compatible analysis artifacts." },
  improve: { heading: "Improve inspector", title: "No improvement target selected", copy: "Explicit evidence and repair targets will appear here after analysis is loaded.", summary: "Select an explicit repair target after loading compatible analysis artifacts." },
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
  if (!cover) return [];
  const ids = new Set((cover.contexts || []).filter((id) => index.contextsById.has(id)));
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
    item.append(selectionButton(displayName(context), { contextId: context.id }, snapshot.selection?.kind === "context" && snapshot.selection.id === context.id, () => actions.context(context.id), new Set((context.atoms || []).filter((id) => index.atomsById.has(id))).size));
    list.append(item);
  }
  container.replaceChildren(list);
}

function subjectsFor(index, contexts) {
  const values = [];
  for (const context of contexts) {
    const groups = new Map();
    for (const atomId of new Set(context.atoms || [])) {
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

function renderGeometryIndex(container, snapshot, layout, actions) {
  if (!layout.restrictions.length && !layout.sharedSupports.length) return replaceWithEmpty(container, "No derived geometry in selected Cover");
  const list = document.createElement("ul");
  list.className = "index-list geometry-index";
  for (const restriction of layout.restrictions) {
    const item = document.createElement("li");
    const label = `Restriction · ${restriction.sourceId} → ${restriction.targetId}`;
    const button = selectionButton(label, { restrictionId: restriction.id }, snapshot.selection?.kind === "restriction" && snapshot.selection.id === restriction.id, () => actions.restriction(restriction.sourceId, restriction.targetId));
    button.addEventListener("mouseenter", () => actions.hover(`${label} · Rendered from contexts.${restriction.sourceId}.restrictsTo`));
    button.addEventListener("mouseleave", () => actions.hover(null));
    item.append(button);
    list.append(item);
  }
  for (const support of layout.sharedSupports) {
    const item = document.createElement("li");
    const label = `Shared support · ${displayName(snapshot.architecture.index.atomsById.get(support.atomId))}`;
    const button = selectionButton(label, { sharedSupportId: support.id }, snapshot.selection?.kind === "shared-support" && snapshot.selection.atomId === support.atomId, () => actions.sharedSupport(support.atomId, support.contextIds), support.contextIds.length);
    button.addEventListener("mouseenter", () => actions.hover(`${label} · ${support.contextIds.join(", ")}`));
    button.addEventListener("mouseleave", () => actions.hover(null));
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
  if (selection.kind === "restriction") {
    const source = index.contextsById.get(selection.sourceId);
    const target = index.contextsById.get(selection.targetId);
    return [...new Set([...(source?.refs || []), ...(target?.refs || [])])].sort();
  }
  if (selection.kind === "shared-support") return index.atomsById.get(selection.atomId)?.refs || [];
  return [];
}

function resolveSource(index, sourceId) {
  const origin = index.sourcesById.get(sourceId);
  if (!origin) return Object.freeze({ id: sourceId, source: null, path: null, symbol: null, section: null, line: null, resolved: false });
  let current = origin;
  let path = current.path || null;
  const seen = new Set([sourceId]);
  while (!path && current.source && index.sourcesById.has(current.source) && !seen.has(current.source)) {
    seen.add(current.source);
    current = index.sourcesById.get(current.source);
    path = current.path || null;
  }
  return Object.freeze({
    id: sourceId,
    source: origin,
    path,
    symbol: origin.symbol || current.symbol || null,
    section: origin.section || current.section || null,
    line: origin.line ?? current.line ?? null,
    resolved: Boolean(path),
    chain: Object.freeze([...seen]),
  });
}

function renderSourceTargets(container, index, refs, selection, actions) {
  if (!refs.length) return replaceWithEmpty(container, "No source refs supplied");
  const list = document.createElement("ul");
  list.className = "source-list";
  for (const ref of refs) {
    const landing = resolveSource(index, ref);
    const item = document.createElement("li");
    item.dataset.resolution = landing.resolved ? "direct" : "unresolved";
    if (landing.source) {
      const atomId = selection?.kind === "atom" ? selection.id : selection?.atomId || null;
      const contextId = selection?.contextId || null;
      const button = selectionButton(`${ref} · ${landing.path || "path unavailable"} · ${landing.symbol || landing.section || "symbol unavailable"} · ${landing.line ?? "line unavailable"}`, { sourceId: ref }, selection?.kind === "source" && selection.id === ref, () => actions.source(ref, atomId, contextId));
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
    return { summary: `Context · ${displayName(context)}`, rows: [["Context", context.id], ["Atoms", new Set((context.atoms || []).filter((id) => index.atomsById.has(id))).size], ["Restricts to", [...new Set(context.restrictsTo || [])].join(", ")], ["Source refs", (context.refs || []).length], ["Restriction depth", contextLayout?.depth ?? 0]] };
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
    const landing = resolveSource(index, selection.id);
    if (!landing.source) return null;
    return { summary: `Source · ${selection.id}`, rows: [["Source", selection.id], ["Kind", landing.source.kind], ["Path", landing.path], ["Symbol", landing.symbol || landing.section], ["Line", landing.line], ["Source chain", landing.chain.join(" → ")]] };
  }
  if (selection.kind === "restriction") {
    const source = index.contextsById.get(selection.sourceId);
    const target = index.contextsById.get(selection.targetId);
    if (!source || !target || !(source.restrictsTo || []).includes(target.id)) return null;
    return { summary: `Restriction · ${displayName(source)} → ${displayName(target)}`, channel: "derived", rows: [["Source Context", source.id], ["Target Context", target.id], ["Rendered from", `contexts.${source.id}.restrictsTo`], ["Visual channel", "derived"]] };
  }
  if (selection.kind === "shared-support") {
    const atom = index.atomsById.get(selection.atomId);
    if (!atom) return null;
    return { summary: `Shared support · ${displayName(atom)}`, channel: "derived", rows: [["Atom", atom.id], ["Contexts", selection.contextIds.join(", ")], ["Rendered from", "explicit Context Atom memberships"], ["Visual channel", "derived"]] };
  }
  return null;
}

function renderSelection(snapshot, layout, actions) {
  const facts = requireElement("#architecture-facts");
  const targets = requireElement("#source-targets");
  const index = snapshot.architecture.index;
  const record = selectedFacts(snapshot, layout);
  requireElement("#inspector-summary").textContent = record?.summary || MODE_COPY[snapshot.mode].summary;
  requireElement("#technical-channel").textContent = record?.channel || (snapshot.selection ? "supplied / derived" : "decoration");
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
  const selectedSource = index ? resolveSource(index, snapshot.selection?.kind === "source" ? snapshot.selection.id : refs[0]) : null;
  requireElement("#source-path").textContent = selectedSource?.path || "—";
  requireElement("#source-symbol").textContent = selectedSource?.symbol || selectedSource?.section || "—";
  requireElement("#source-line").textContent = selectedSource?.line === null || selectedSource?.line === undefined ? "—" : String(selectedSource.line);
  requireElement("#source-resolution").textContent = selectedSource?.resolved ? "DIRECT EVIDENCE" : "UNRESOLVED";
}

function renderBreadcrumb(snapshot, actions) {
  const index = snapshot.architecture.index;
  const selection = snapshot.selection;
  const items = [];
  if (snapshot.cover) items.push({ level: "cover", label: displayName(index?.coversById.get(snapshot.cover)), action: () => actions.cover(snapshot.cover) });
  const ownedAtomId = selection?.kind === "atom" ? selection.id : selection?.atomId;
  const contextId = selection?.contextId || (selection?.kind === "context" ? selection.id : ownedAtomId ? index?.contextIdsByAtom.get(ownedAtomId)?.[0] : null);
  if (contextId) items.push({ level: "context", label: displayName(index?.contextsById.get(contextId)), action: () => actions.context(contextId) });
  const subject = selection?.kind === "subject" ? selection.id : ownedAtomId ? index?.atomsById.get(ownedAtomId)?.subject : null;
  if (subject && contextId) items.push({ level: "subject", label: subject, action: () => actions.subject(contextId, subject) });
  const atomId = ownedAtomId;
  if (atomId) items.push({ level: "atom", label: displayName(index?.atomsById.get(atomId)), action: () => actions.atom(atomId, contextId) });
  if (selection?.kind === "source") items.push({ level: "source", label: selection.id, action: () => actions.source(selection.id, selection.atomId, selection.contextId, selection.sourceTargetKey) });
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

function searchRecords(index, coverId, query, analysisModel) {
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
  for (const finding of analysisModel.findings) if (includes(finding.id, finding.title, finding.summary, finding.conclusionCode, finding.state)) results.push({ kind: "finding", id: finding.id, label: `Finding · ${finding.title} · ${finding.stateLabel}` });
  return results.slice(0, 30);
}

function renderSearch(snapshot, actions) {
  const results = requireElement("#search-results");
  const query = requireElement("#architecture-search").value;
  const index = snapshot.architecture.index;
  const records = index ? searchRecords(index, snapshot.cover, query, buildAnalysisView(snapshot.analysis.bundle, index)) : [];
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
      else if (record.kind === "finding") actions.finding(record.id);
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
  renderGeometryIndex(requireElement("#geometry-list"), snapshot, layout, actions);
  renderSelection(snapshot, layout, actions);
  renderBreadcrumb(snapshot, actions);
  renderSearch(snapshot, actions);
}

function findingById(model, id) {
  return model.findings.find((finding) => finding.id === id) || null;
}

function renderFindingList(container, snapshot, model, actions) {
  if (snapshot.analysis.status !== "accepted") return replaceWithEmpty(container, "No analysis loaded");
  if (!model.findings.length) return replaceWithEmpty(container, "No insight findings supplied");
  const list = document.createElement("ul");
  list.className = "finding-list";
  model.findings.forEach((finding) => {
    const item = document.createElement("li");
    item.dataset.findingState = finding.state;
    const button = selectionButton(finding.title, { findingId: finding.id, findingState: finding.state }, snapshot.finding === finding.id, () => actions.finding(finding.id));
    const state = document.createElement("span");
    state.className = "finding-state";
    state.textContent = finding.stateLabel;
    const counts = document.createElement("span");
    counts.className = "finding-counts";
    counts.textContent = `${finding.supportContextIds.length} contexts · ${finding.relationRefs.length} boundaries · ${finding.supportAtomIds.length} supporting atoms`;
    button.append(state, counts);
    item.append(button);
    list.append(item);
  });
  container.replaceChildren(list);
}

function analysisSection(title, content, state = null) {
  const section = document.createElement("section");
  section.className = "analysis-step";
  if (state) section.dataset.analysisState = state;
  const heading = document.createElement("h4");
  heading.textContent = title;
  const body = document.createElement("div");
  if (Array.isArray(content)) {
    const list = document.createElement("ul");
    content.forEach((entry) => { const item = document.createElement("li"); item.textContent = entry; list.append(item); });
    body.append(list);
  } else body.textContent = content;
  section.append(heading, body);
  return section;
}

function renderFindingExplanation(container, finding, model, mode) {
  if (!finding) return replaceWithEmpty(container, "Select a finding to inspect local facts, shared relations, global result, and source evidence.");
  const local = finding.localFacts.length ? finding.localFacts.map((fact) => `${fact.atomId} · ${fact.fact} · ${fact.contexts.join(", ")}`) : ["No local Atom support was supplied."];
  const classifiedRelations = new Set([...finding.agreementEdgeRefs, ...finding.mismatchEdgeRefs, ...finding.unobservedEdgeRefs]);
  const shared = [
    ...finding.agreementEdgeRefs.map((edge) => `Agreement · ${edge}`),
    ...finding.mismatchEdgeRefs.map((edge) => `Mismatch · ${edge}`),
    ...finding.edgeRefs.filter((edge) => !classifiedRelations.has(edge)).map((edge) => `Relation participant · ${edge} · status not supplied`),
    ...(!finding.edgeRefs.length ? ["No measured relation support was supplied."] : []),
    ...(finding.unobservedEdgeRefs.length ? finding.unobservedEdgeRefs.map((edge) => `Unmeasured relation · ${edge}`) : ["Unmeasured relations · none supplied for this finding."]),
  ];
  const global = `${finding.stateLabel}. ${finding.summary}`;
  const source = finding.sourceTargets.length ? finding.sourceTargets.map((target) => `${target.classification} · ${target.path || target.sourceId} · ${target.symbol || "symbol unavailable"}`) : ["No source target resolved from the supplied evidence."];
  const steps = [
    analysisSection("1. Local facts", local),
    analysisSection("2. Shared relations", shared, finding.unobservedEdgeRefs.length ? "unmeasured" : finding.state),
    analysisSection("3. Global result", global, finding.state),
    analysisSection("4. Source evidence", source),
  ];
  if (finding.unmeasuredRows.length) steps.push(analysisSection("Unmeasured", finding.unmeasuredRows.map((row) => `${row.evaluator} · ${row.law} · ${row.verdict}`), "unmeasured"));
  if (model.comparison) steps.push(analysisSection("Run comparison", model.comparison.conclusionCode || "Comparison artifact supplied"));
  if (model.gate) steps.push(analysisSection("Gate decision", model.gate.decision, model.gate.blocked ? "blocked" : model.gate.evaluable ? "informational" : "unmeasured"));
  if (mode === "improve") steps.push(analysisSection("Evidence and change status", [
    "Direct evidence identifies an observed inspection location.",
    finding.repairAtomIds.length ? "Candidate change points are supplied explicitly by ArchSig repair_candidate data." : "No explicit repair target was supplied; evidence is not promoted to a change recommendation.",
    "A validated hypothetical repair requires an explicit checked target-to-obstruction contract; none is supplied by the current artifact contract.",
    model.comparison ? "The comparison is shown as a run-local recorded result and is not promoted to repair validation." : "No run comparison artifact is supplied for this finding.",
    "No actual repository change is asserted by this analysis view.",
  ]));
  container.replaceChildren(...steps);
}

function renderFindingSources(container, snapshot, finding, actions) {
  if (!finding) return replaceWithEmpty(container, "Select a finding to resolve source targets");
  if (!finding.sourceTargets.length) return replaceWithEmpty(container, finding.repairAtomIds.length ? "Explicit repair targets have no resolved source metadata." : "No explicit repair target was supplied. Evidence locations are inspection points, not validated change recommendations.");
  const list = document.createElement("ul");
  list.className = "source-list classified-source-list source-tree";
  const paths = new Map();
  finding.sourceTargets.forEach((target) => {
    const path = target.path || "UNRESOLVED";
    const symbol = target.symbol || "symbol unavailable";
    const line = target.line ?? "line unavailable";
    const symbols = paths.get(path) || new Map();
    const lines = symbols.get(symbol) || new Map();
    lines.set(line, [...(lines.get(line) || []), target]);
    symbols.set(symbol, lines);
    paths.set(path, symbols);
  });
  [...paths].sort(([left], [right]) => left.localeCompare(right)).forEach(([path, symbols]) => {
    const pathItem = document.createElement("li");
    pathItem.className = "source-path-group";
    const pathLabel = document.createElement("strong");
    pathLabel.textContent = path;
    const symbolList = document.createElement("ul");
    [...symbols].sort(([left], [right]) => left.localeCompare(right)).forEach(([symbol, lines]) => {
      const symbolItem = document.createElement("li");
      const symbolLabel = document.createElement("span");
      symbolLabel.className = "source-symbol-group";
      symbolLabel.textContent = symbol;
      const lineList = document.createElement("ul");
      [...lines].sort(([left], [right]) => String(left).localeCompare(String(right), undefined, { numeric: true })).forEach(([line, targets]) => {
        const lineItem = document.createElement("li");
        const lineLabel = document.createElement("span");
        lineLabel.className = "source-line-group";
        lineLabel.textContent = `line ${line}`;
        lineItem.append(lineLabel);
        targets.forEach((target) => {
          const badge = document.createElement("span");
          badge.className = "source-classification-badge";
          badge.textContent = target.classification;
          const button = selectionButton(`${target.sourceId} · ${target.resolution} · Supporting Atom ${target.atomId || "not directly supplied"}`, { sourceId: target.sourceId, sourceClassification: target.classification, sourceSupportingAtom: target.atomId || "" }, snapshot.selection?.kind === "source" && snapshot.selection.sourceTargetKey === target.key, () => actions.source(target.sourceId, target.atomId, target.contextId, target.key));
          button.dataset.classification = target.classification;
          lineItem.append(badge, button);
        });
        lineList.append(lineItem);
      });
      symbolItem.append(symbolLabel, lineList);
      symbolList.append(symbolItem);
    });
    pathItem.append(pathLabel, symbolList);
    list.append(pathItem);
  });
  container.replaceChildren(list);
}

function renderAnalysisStatus(snapshot, model, actions) {
  const analysis = snapshot.analysis;
  const labels = {
    absent: "No analysis loaded",
    loading: "Validating ArchSig run…",
    accepted: "Analysis accepted",
    malformed: "Analysis rejected · malformed artifacts",
    mismatch: "Analysis rejected · identity mismatch",
    unresolved: "Analysis rejected · unresolved references",
  };
  const section = requireElement(".analysis-input-status");
  section.dataset.status = analysis.status;
  requireElement("#analysis-input-status").textContent = labels[analysis.status] || analysis.status;
  requireElement("#analysis-status").textContent = labels[analysis.status] || analysis.status;
  requireElement("#analysis-run-id").textContent = analysis.bundle?.runId || "—";
  requireElement("#analysis-profile-ref").textContent = analysis.bundle?.profileRef || "—";
  requireElement("#analysis-packet-digest").textContent = analysis.bundle?.packetDigest || "—";
  requireElement("#analysis-issues").replaceChildren(...analysis.issues.slice(0, 12).map((entry) => {
    const item = document.createElement("li");
    const values = entry.expected && entry.received ? ` Expected ${entry.expected}; received ${entry.received}.` : "";
    item.textContent = `${entry.path}: ${entry.message}${values}`;
    return item;
  }));
  renderFindingList(requireElement("#findings-list"), snapshot, model, actions);
  const selected = findingById(model, snapshot.finding);
  if (selected && snapshot.mode !== "architecture") requireElement("#inspector-summary").textContent = `${selected.title} · ${selected.stateLabel}`;
  renderFindingExplanation(requireElement("#analysis-explanation"), selected, model, snapshot.mode);
  requireElement("#technical-conclusion").textContent = selected?.conclusionCode || "—";
  requireElement("#technical-gate").textContent = model.gate?.decision || "—";
  if (snapshot.mode === "analysis" || snapshot.mode === "improve") renderFindingSources(requireElement("#source-targets"), snapshot, selected, actions);
  const selectedTarget = snapshot.mode === "architecture" ? null : selected?.sourceTargets.find((target) => snapshot.selection?.sourceTargetKey ? target.key === snapshot.selection.sourceTargetKey : target.sourceId === snapshot.selection?.id && (!snapshot.selection?.atomId || target.atomId === snapshot.selection.atomId));
  const sourceClassification = requireElement("#source-classification");
  if (selectedTarget) {
    sourceClassification.textContent = selectedTarget.classification;
    sourceClassification.dataset.classification = selectedTarget.classification;
    requireElement("#source-supporting-atom").textContent = `Supporting Atom ${selectedTarget.atomId || "not directly supplied"}`;
    requireElement("#source-resolution").textContent = selectedTarget.resolution;
  } else if (snapshot.mode === "architecture") {
    sourceClassification.textContent = snapshot.selection?.kind === "source" ? "ARCHMAP SOURCE" : "NO SOURCE CLASSIFICATION";
    delete sourceClassification.dataset.classification;
    requireElement("#source-supporting-atom").textContent = `Supporting Atom ${snapshot.selection?.atomId || "—"}`;
  } else {
    sourceClassification.textContent = snapshot.mode === "improve" && selected && !selected.repairAtomIds.length ? "NO EXPLICIT REPAIR TARGET" : "NO SOURCE CLASSIFICATION";
    delete sourceClassification.dataset.classification;
    requireElement("#source-supporting-atom").textContent = "Supporting Atom —";
    requireElement("#source-path").textContent = "—";
    requireElement("#source-symbol").textContent = "—";
    requireElement("#source-line").textContent = "—";
    requireElement("#source-resolution").textContent = "UNRESOLVED";
  }
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
  let analysisRequest = 0;

  const actions = Object.freeze({
    cover(id) { state.selectCover(id); },
    context(id) { state.selectContext(id); },
    subject(contextId, subject) { state.selectSubject(contextId, subject); },
    atom(id, contextId = null) { state.selectAtom(id, contextId); atlasRenderer?.selectAtom(id); },
    source(id, atomId = null, contextId = null, sourceTargetKey = null) { state.selectSource(id, atomId, contextId, sourceTargetKey); },
    restriction(sourceId, targetId) { state.selectRestriction(sourceId, targetId); },
    sharedSupport(atomId, contextIds) { state.selectSharedSupport(atomId, contextIds); },
    finding(id) { state.selectFinding(id); },
    hover(label) {
      const hover = requireElement("#atlas-hover-label");
      hover.hidden = !label;
      hover.textContent = label || "";
    },
  });
  const handleSceneSelection = (kind, id, contextId) => {
    if (kind === "context") actions.context(id);
    if (kind === "subject") actions.subject(contextId, id);
    if (kind === "atom") actions.atom(id, contextId);
    if (kind === "restriction") actions.restriction(id, contextId);
    if (kind === "shared-support") actions.sharedSupport(id, contextId);
  };
  const handleSceneHover = actions.hover;
  const publishTestState = (snapshot) => {
    const publicState = { ...snapshot, modeCount: MODES.length, canvasCount: host.querySelectorAll("canvas").length };
    window.__archviewFoundationState = publicState;
    window.__archviewState = publicState;
  };

  state.subscribe((snapshot) => {
    const copy = MODE_COPY[snapshot.mode];
    const layout = buildArchitectureLayout(snapshot.architecture.index, snapshot.cover);
    const analysisModel = buildAnalysisView(snapshot.analysis.bundle, snapshot.architecture.index);
    const selectedFinding = findingById(analysisModel, snapshot.finding);
    window.__archviewLayout = layout;
    window.__archviewAnalysisView = analysisModel;
    if (atlasRenderer && renderedSignature !== layout.signature) {
      window.__archviewRenderStats = atlasRenderer.setArchitecture(snapshot.architecture.index, layout, handleSceneSelection, handleSceneHover);
      renderedSignature = layout.signature;
    }
    if (atlasRenderer) {
      const support = snapshot.mode === "architecture" || !selectedFinding ? null : {
        atomIds: selectedFinding.supportAtomIds,
        contextIds: [...new Set([...selectedFinding.supportContextIds, ...selectedFinding.boundaryContextIds])],
        edgeIds: selectedFinding.relationRefs,
        agreementEdgeIds: selectedFinding.agreementEdgeRefs,
        mismatchEdgeIds: selectedFinding.mismatchEdgeRefs,
        unmeasuredEdgeIds: selectedFinding.unobservedEdgeRefs,
        sharedAtomIds: selectedFinding.supportAtomIds.filter((atomId) => (snapshot.architecture.index?.contextIdsByAtom.get(atomId) || []).length > 1),
        state: selectedFinding.state,
      };
      window.__archviewAnalysisSupport = atlasRenderer.setAnalysisSupport(support);
    }
    root.dataset.mode = snapshot.mode;
    root.dataset.phase = snapshot.phase;
    root.dataset.inputStatus = snapshot.architecture.status;
    root.dataset.analysisStatus = snapshot.analysis.status;
    root.dataset.zoom = snapshot.zoom;
    requireElement("#repository-name").textContent = snapshot.repository || "No repository loaded";
    requireElement("#revision-name").textContent = snapshot.revision || "—";
    requireElement("#cover-name").textContent = snapshot.cover || "No cover selected";
    requireElement("#inspector-heading").textContent = copy.heading;
    if (selectedFinding && snapshot.mode !== "architecture") requireElement("#inspector-summary").textContent = `${selectedFinding.title} · ${selectedFinding.stateLabel}`;
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
    renderAnalysisStatus(snapshot, analysisModel, actions);
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
    window.__archviewRenderStats = atlasRenderer?.setArchitecture(null, null, handleSceneSelection, handleSceneHover) || { contextPlates: 0, subjectGroups: 0, atomGlyphs: 0, restrictions: 0, sharedSupports: 0 };
    renderedSignature = null;
    state.architectureFailed(error, source);
  };
  const loadUrl = async (url) => {
    analysisRequest += 1;
    state.architectureLoading(url);
    try {
      const resolved = new URL(url, location.href);
      if (resolved.origin !== location.origin) throw new Error("ArchMap URL must use the current origin.");
      applyIndex(await loadArchMapFromUrl(resolved.href), resolved.href);
    } catch (error) { rejectInput(error, url); }
  };
  const loadText = (text, source = "local file") => { analysisRequest += 1; state.architectureLoading(source); try { applyIndex(parseArchMap(text), source); } catch (error) { rejectInput(error, source); } };
  const loadObject = (document, source = "runtime object") => { analysisRequest += 1; state.architectureLoading(source); try { applyIndex(buildArchMapIndex(document), source); } catch (error) { rejectInput(error, source); } };
  requireElement("#archmap-file").addEventListener("change", async (event) => {
    const file = event.target.files?.[0];
    if (file) { analysisRequest += 1; loadText(await file.text(), file.name); }
    event.target.value = "";
  });

  const rejectAnalysis = (error, source, requestId = analysisRequest) => {
    if (requestId === analysisRequest) state.analysisRejected(error, source);
  };
  const acceptAnalysis = async (documents, source, requestId = ++analysisRequest) => {
    if (requestId !== analysisRequest) return state.read().analysis;
    const architectureIndex = state.read().architecture.index;
    state.analysisLoading(source);
    try {
      const bundle = await validateAnalysisBundle(documents, architectureIndex);
      if (requestId === analysisRequest && state.read().architecture.index === architectureIndex) state.analysisAccepted(bundle, source);
    } catch (error) { rejectAnalysis(error, source, requestId); }
    return state.read().analysis;
  };
  const loadAnalysisFiles = async (files, source = "local run directory") => {
    const requestId = ++analysisRequest;
    state.analysisLoading(source);
    try { return await acceptAnalysis(await documentsFromFiles(files), source, requestId); }
    catch (error) { rejectAnalysis(error, source, requestId); return state.read().analysis; }
  };
  const loadAnalysisUrl = async (directory) => {
    const requestId = ++analysisRequest;
    state.analysisLoading(directory);
    try {
      const resolved = new URL(directory.endsWith("/") ? directory : `${directory}/`, location.href);
      if (resolved.origin !== location.origin) throw Object.assign(new Error("ArchSig run URL must use the current origin."), { status: "mismatch" });
      return await acceptAnalysis(await documentsFromUrl(resolved.href), resolved.href, requestId);
    } catch (error) { rejectAnalysis(error, directory, requestId); return state.read().analysis; }
  };
  requireElement("#analysis-directory").addEventListener("change", async (event) => {
    const files = event.target.files;
    if (files?.length) await loadAnalysisFiles(files, files[0].webkitRelativePath?.split("/")[0] || "local run directory");
    event.target.value = "";
  });

  const parameters = new URLSearchParams(location.search);
  const requestedArchMap = parameters.get("archmap");
  if (requestedArchMap !== "none") await loadUrl(requestedArchMap || DEFAULT_ARCHMAP_URL);
  const requestedAnalysis = parameters.get("analysis");
  if (requestedAnalysis) await loadAnalysisUrl(requestedAnalysis);
  const dispose = () => atlasRenderer?.dispose();
  window.addEventListener("pagehide", dispose, { once: true });
  window.__archview = Object.freeze({ state, loadUrl, loadText, loadObject, loadAnalysisFiles, loadAnalysisUrl, loadAnalysisObject: acceptAnalysis, dispose });
  return state.read();
}
