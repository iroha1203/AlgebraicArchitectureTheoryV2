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
  });
}
