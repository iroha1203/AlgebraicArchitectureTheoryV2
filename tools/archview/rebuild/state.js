export const MODES = Object.freeze(["architecture", "analysis", "improve"]);

const initialState = Object.freeze({
  mode: "architecture",
  view: "isometric",
  phase: "booting",
  renderer: "starting",
  repository: null,
  revision: null,
  cover: null,
  selection: null,
  architecture: Object.freeze({ status: "idle", index: null, issues: Object.freeze([]), source: null }),
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
      state = { ...state, architecture: Object.freeze({ status: "loading", index: null, issues: Object.freeze([]), source }) };
      return publish();
    },
    architectureLoaded(index, source) {
      const status = index.empty ? "empty" : index.unresolved.length ? "unresolved" : "loaded";
      state = {
        ...state,
        repository: index.id,
        revision: index.schema,
        cover: index.covers[0]?.id || null,
        selection: null,
        architecture: Object.freeze({ status, index, issues: index.unresolved, source }),
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
        selection: null,
        architecture: Object.freeze({ status: "error", index: null, issues: Object.freeze(issues), source }),
      };
      return publish();
    },
    selectAtom(atomId) {
      const index = state.architecture.index;
      if (!index?.atomsById.has(atomId)) throw new Error(`Unknown Atom selection: ${atomId}`);
      state = { ...state, selection: Object.freeze({ kind: "atom", id: atomId }) };
      return publish();
    },
  });
}
