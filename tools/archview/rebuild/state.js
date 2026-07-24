export const MODES = Object.freeze(["architecture", "analysis", "improve"]);

const initialState = Object.freeze({
  mode: "architecture",
  view: "isometric",
  phase: "booting",
  renderer: "starting",
  repository: null,
  revision: null,
  cover: null,
  zoom: "cover",
  selection: null,
  finding: null,
  architecture: Object.freeze({ status: "idle", index: null, issues: Object.freeze([]), source: null }),
  analysis: Object.freeze({ status: "absent", bundle: null, issues: Object.freeze([]), source: null }),
  error: null,
});

export function createArchViewState() {
  let state = { ...initialState };
  const listeners = new Set();

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
      state = { ...state, finding: null, architecture: Object.freeze({ status: "loading", index: null, issues: Object.freeze([]), source }), analysis: Object.freeze({ status: "absent", bundle: null, issues: Object.freeze([]), source: null }) };
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
      state = { ...state, mode: state.mode === "architecture" ? "analysis" : state.mode, finding: findingId, selection: null };
      return publish();
    },
    selectCover(coverId) {
      const index = state.architecture.index;
      if (!index?.coversById.has(coverId)) throw new Error(`Unknown Cover selection: ${coverId}`);
      state = { ...state, cover: coverId, zoom: "cover", selection: Object.freeze({ kind: "cover", id: coverId }) };
      return publish();
    },
    selectContext(contextId) {
      const index = state.architecture.index;
      if (!index?.contextsById.has(contextId)) throw new Error(`Unknown Context selection: ${contextId}`);
      state = { ...state, zoom: "context", selection: Object.freeze({ kind: "context", id: contextId }) };
      return publish();
    },
    selectSubject(contextId, subject) {
      const index = state.architecture.index;
      const context = index?.contextsById.get(contextId);
      const exists = (context?.atoms || []).some((atomId) => index.atomsById.get(atomId)?.subject === subject);
      if (!exists) throw new Error(`Unknown Subject selection: ${contextId}::${subject}`);
      state = { ...state, zoom: "subject", selection: Object.freeze({ kind: "subject", id: subject, contextId }) };
      return publish();
    },
    selectAtom(atomId, contextId = null) {
      const index = state.architecture.index;
      if (!index?.atomsById.has(atomId)) throw new Error(`Unknown Atom selection: ${atomId}`);
      if (contextId && !index.contextsById.get(contextId)?.atoms?.includes(atomId)) throw new Error(`Atom ${atomId} is not a member of Context ${contextId}.`);
      state = { ...state, zoom: "atom", selection: Object.freeze({ kind: "atom", id: atomId, contextId }) };
      return publish();
    },
    selectSource(sourceId, atomId = null, contextId = null, sourceTargetKey = null) {
      const index = state.architecture.index;
      if (!index?.sourcesById.has(sourceId)) throw new Error(`Unknown Source selection: ${sourceId}`);
      if (atomId && !index.atomsById.has(atomId)) throw new Error(`Unknown Atom source owner: ${atomId}`);
      state = { ...state, zoom: "source", selection: Object.freeze({ kind: "source", id: sourceId, atomId, contextId, sourceTargetKey }) };
      return publish();
    },
    selectRestriction(sourceId, targetId) {
      const index = state.architecture.index;
      if (!index?.contextsById.get(sourceId)?.restrictsTo?.includes(targetId)) throw new Error(`Unknown restriction: ${sourceId}->${targetId}`);
      state = { ...state, zoom: "context", selection: Object.freeze({ kind: "restriction", id: `${sourceId}->${targetId}`, sourceId, targetId }) };
      return publish();
    },
    selectSharedSupport(atomId, contextIds) {
      const index = state.architecture.index;
      const uniqueContextIds = [...new Set(contextIds || [])].sort();
      if (!index?.atomsById.has(atomId) || uniqueContextIds.length < 2 || !uniqueContextIds.every((contextId) => index.contextsById.get(contextId)?.atoms?.includes(atomId))) {
        throw new Error(`Unknown shared support: ${atomId}`);
      }
      state = { ...state, zoom: "atom", selection: Object.freeze({ kind: "shared-support", id: `shared::${atomId}`, atomId, contextIds: Object.freeze(uniqueContextIds) }) };
      return publish();
    },
    overview() {
      state = { ...state, zoom: "cover", selection: state.cover ? Object.freeze({ kind: "cover", id: state.cover }) : null };
      return publish();
    },
  });
}
