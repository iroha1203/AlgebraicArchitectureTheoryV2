export const MODES = Object.freeze(["architecture", "analysis", "improve"]);
export const SURFACES = Object.freeze(["atlas", "outline"]);

const initialState = Object.freeze({
  mode: "architecture",
  surface: "atlas",
  view: "isometric",
  phase: "booting",
  renderer: "starting",
  repository: null,
  revision: null,
  cover: null,
  zoom: "cover",
  selection: null,
  selections: Object.freeze([]),
  selectionHistory: Object.freeze([]),
  finding: null,
  architecture: Object.freeze({ status: "idle", index: null, issues: Object.freeze([]), source: null }),
  analysis: Object.freeze({ status: "absent", bundle: null, issues: Object.freeze([]), source: null }),
  error: null,
});

export function createArchViewState() {
  let state = { ...initialState };
  const listeners = new Set();

  const selectionKey = (selection) => selection ? JSON.stringify(selection) : "none";
  const commitSelection = (selection, zoom, additive = false, extra = {}) => {
    const currentSelections = state.selections?.length ? state.selections : state.selection ? [state.selection] : [];
    const nextSelections = additive
      ? [...currentSelections.filter((entry) => selectionKey(entry) !== selectionKey(selection)), selection]
      : [selection];
    const changed = selectionKey(state.selection) !== selectionKey(selection) || JSON.stringify(currentSelections) !== JSON.stringify(nextSelections) || Object.entries(extra).some(([key, value]) => state[key] !== value);
    const history = changed && state.selection
      ? [...state.selectionHistory, Object.freeze({ selection: state.selection, selections: Object.freeze([...currentSelections]), zoom: state.zoom, cover: state.cover })].slice(-100)
      : state.selectionHistory;
    state = { ...state, ...extra, zoom, selection, selections: Object.freeze(nextSelections), selectionHistory: Object.freeze(history) };
    return publish();
  };

  const read = () => Object.freeze({ ...state });

  const publish = () => {
    const snapshot = read();
    for (const listener of listeners) listener(snapshot);
    return snapshot;
  };

  return Object.freeze({
    read,
    subscribe(listener) {
      listeners.add(listener);
      listener(read());
      return () => listeners.delete(listener);
    },
    selectMode(mode) {
      if (!MODES.includes(mode)) throw new Error(`Unknown ArchView mode: ${mode}`);
      state = { ...state, mode };
      return publish();
    },
    selectSurface(surface) {
      if (!SURFACES.includes(surface)) throw new Error(`Unknown ArchView surface: ${surface}`);
      state = { ...state, surface };
      return publish();
    },
    selectView(view) {
      if (!["isometric", "top", "front"].includes(view)) throw new Error(`Unknown camera view: ${view}`);
      state = { ...state, view };
      return publish();
    },
    rendererReady() {
      state = { ...state, phase: "ready", renderer: "ready", error: null };
      return publish();
    },
    rendererFailed(error) {
      state = {
        ...state,
        phase: "error",
        renderer: "unavailable",
        error: error instanceof Error ? error.message : String(error),
      };
      return publish();
    },
    architectureLoading(source) {
      state = { ...state, finding: null, selection: null, selections: Object.freeze([]), selectionHistory: Object.freeze([]), architecture: Object.freeze({ status: "loading", index: null, issues: Object.freeze([]), source }), analysis: Object.freeze({ status: "absent", bundle: null, issues: Object.freeze([]), source: null }) };
      return publish();
    },
    architectureLoaded(index, source) {
      const status = index.empty ? "empty" : index.unresolved.length ? "unresolved" : "loaded";
      state = {
        ...state,
        repository: index.id,
        revision: index.schema,
        cover: index.covers[0]?.id || null,
        zoom: index.covers.length ? "cover" : "context",
        selection: null,
        selections: Object.freeze([]),
        selectionHistory: Object.freeze([]),
        finding: null,
        architecture: Object.freeze({ status, index, issues: index.unresolved, source }),
        analysis: Object.freeze({ status: "absent", bundle: null, issues: Object.freeze([]), source: null }),
      };
      return publish();
    },
    architectureFailed(error, source) {
      const issues = Array.isArray(error?.issues) ? error.issues : [{ path: "$", message: error instanceof Error ? error.message : String(error) }];
      state = {
        ...state,
        repository: null,
        revision: null,
        cover: null,
        zoom: "cover",
        selection: null,
        selections: Object.freeze([]),
        selectionHistory: Object.freeze([]),
        finding: null,
        architecture: Object.freeze({ status: "error", index: null, issues: Object.freeze(issues), source }),
        analysis: Object.freeze({ status: "absent", bundle: null, issues: Object.freeze([]), source: null }),
      };
      return publish();
    },
    analysisLoading(source) {
      state = { ...state, finding: null, analysis: Object.freeze({ status: "loading", bundle: null, issues: Object.freeze([]), source }) };
      return publish();
    },
    analysisAccepted(bundle, source) {
      state = { ...state, finding: null, analysis: Object.freeze({ status: "accepted", bundle, issues: Object.freeze([]), source }) };
      return publish();
    },
    analysisRejected(error, source) {
      const status = ["malformed", "mismatch", "unresolved"].includes(error?.status) ? error.status : "malformed";
      const issues = Array.isArray(error?.issues) ? error.issues : [{ path: "$", message: error instanceof Error ? error.message : String(error) }];
      state = { ...state, finding: null, analysis: Object.freeze({ status, bundle: null, issues: Object.freeze(issues), source }) };
      return publish();
    },
    selectFinding(findingId) {
      if (state.analysis.status !== "accepted" || typeof findingId !== "string" || !findingId) throw new Error(`Unknown finding selection: ${findingId}`);
      state = { ...state, mode: state.mode === "architecture" ? "analysis" : state.mode, finding: findingId, selection: null, selections: Object.freeze([]) };
      return publish();
    },
    selectCover(coverId, additive = false) {
      const index = state.architecture.index;
      if (!index?.coversById.has(coverId)) throw new Error(`Unknown Cover selection: ${coverId}`);
      return commitSelection(Object.freeze({ kind: "cover", id: coverId }), "cover", additive, { cover: coverId });
    },
    selectContext(contextId, additive = false) {
      const index = state.architecture.index;
      if (!index?.contextsById.has(contextId)) throw new Error(`Unknown Context selection: ${contextId}`);
      return commitSelection(Object.freeze({ kind: "context", id: contextId }), "context", additive);
    },
    selectSubject(contextId, subject, additive = false) {
      const index = state.architecture.index;
      const context = index?.contextsById.get(contextId);
      const exists = (context?.atoms || []).some((atomId) => index.atomsById.get(atomId)?.subject === subject);
      if (!exists) throw new Error(`Unknown Subject selection: ${contextId}::${subject}`);
      return commitSelection(Object.freeze({ kind: "subject", id: subject, contextId }), "subject", additive);
    },
    selectAtom(atomId, contextId = null, additive = false) {
      const index = state.architecture.index;
      if (!index?.atomsById.has(atomId)) throw new Error(`Unknown Atom selection: ${atomId}`);
      if (contextId && !index.contextsById.get(contextId)?.atoms?.includes(atomId)) throw new Error(`Atom ${atomId} is not a member of Context ${contextId}.`);
      return commitSelection(Object.freeze({ kind: "atom", id: atomId, contextId }), "atom", additive);
    },
    selectSource(sourceId, atomId = null, contextId = null, sourceTargetKey = null, additive = false) {
      const index = state.architecture.index;
      if (atomId && !index.atomsById.has(atomId)) throw new Error(`Unknown Atom source owner: ${atomId}`);
      const explicitlyReferenced = atomId && index.atomsById.get(atomId)?.refs?.includes(sourceId);
      if (!index?.sourcesById.has(sourceId) && !explicitlyReferenced) throw new Error(`Unknown Source selection: ${sourceId}`);
      return commitSelection(Object.freeze({ kind: "source", id: sourceId, atomId, contextId, sourceTargetKey }), "source", additive);
    },
    selectRestriction(sourceId, targetId, additive = false) {
      const index = state.architecture.index;
      if (!index?.contextsById.get(sourceId)?.restrictsTo?.includes(targetId)) throw new Error(`Unknown restriction: ${sourceId}->${targetId}`);
      return commitSelection(Object.freeze({ kind: "restriction", id: `${sourceId}->${targetId}`, sourceId, targetId }), "context", additive);
    },
    selectSharedSupport(atomId, contextIds, additive = false) {
      const index = state.architecture.index;
      const uniqueContextIds = [...new Set(contextIds || [])].sort();
      if (!index?.atomsById.has(atomId) || uniqueContextIds.length < 2 || !uniqueContextIds.every((contextId) => index.contextsById.get(contextId)?.atoms?.includes(atomId))) {
        throw new Error(`Unknown shared support: ${atomId}`);
      }
      return commitSelection(Object.freeze({ kind: "shared-support", id: `shared::${atomId}`, atomId, contextIds: Object.freeze(uniqueContextIds) }), "atom", additive);
    },
    overview() {
      if (!state.cover) {
        state = { ...state, zoom: "cover", selection: null, selections: Object.freeze([]) };
        return publish();
      }
      return commitSelection(Object.freeze({ kind: "cover", id: state.cover }), "cover");
    },
    backSelection() {
      if (!state.selectionHistory.length) return read();
      const history = [...state.selectionHistory];
      const previous = history.pop();
      state = { ...state, selection: previous.selection, selections: previous.selections, zoom: previous.zoom, cover: previous.cover, selectionHistory: Object.freeze(history) };
      return publish();
    },
  });
}
