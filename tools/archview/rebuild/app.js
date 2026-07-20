import { createArchViewState, MODES } from "./state.js";

const MODE_COPY = Object.freeze({
  architecture: {
    heading: "Architecture inspector",
    title: "No architecture loaded",
    copy: "Load an ArchMap in the next implementation stage to compose Contexts and Atoms.",
    summary: "Select a Context or Atom after loading an ArchMap.",
    analysis: "No analysis loaded",
    source: "No source selected",
  },
  analysis: {
    heading: "Analysis inspector",
    title: "No analysis loaded",
    copy: "Architecture remains available when a compatible ArchSig run is loaded in a later stage.",
    summary: "Select a finding after loading compatible analysis artifacts.",
    analysis: "No analysis loaded",
    source: "No evidence source selected",
  },
  improve: {
    heading: "Improve inspector",
    title: "No improvement target selected",
    copy: "Explicit evidence and repair targets will appear here after analysis is loaded.",
    summary: "Select an explicit repair target after loading compatible analysis artifacts.",
    analysis: "No analysis loaded",
    source: "No improvement source selected",
  },
});

function requireElement(selector) {
  const element = document.querySelector(selector);
  if (!element) throw new Error(`Required ArchView element is missing: ${selector}`);
  return element;
}

export async function startArchView() {
  const root = requireElement("#archview-app");
  const host = requireElement("#atlas-canvas-host");
  const errorPanel = requireElement("#webgl-error");
  const errorMessage = requireElement("#webgl-error-message");
  const rendererStatus = requireElement("#renderer-status");
  const modeButtons = [...document.querySelectorAll("[data-mode-button]")];
  const viewButtons = [...document.querySelectorAll("[data-view]")];
  const state = createArchViewState();
  let atlasRenderer = null;

  const publishTestState = (snapshot) => {
    window.__archviewFoundationState = {
      ...snapshot,
      modeCount: MODES.length,
      canvasCount: host.querySelectorAll("canvas").length,
    };
  };

  state.subscribe((snapshot) => {
    const copy = MODE_COPY[snapshot.mode];
    root.dataset.mode = snapshot.mode;
    root.dataset.phase = snapshot.phase;
    requireElement("#empty-state-title").textContent = copy.title;
    requireElement("#empty-state-copy").textContent = copy.copy;
    requireElement("#inspector-heading").textContent = copy.heading;
    requireElement("#inspector-summary").textContent = copy.summary;
    requireElement("#analysis-status").textContent = copy.analysis;
    requireElement("#source-status").textContent = copy.source;
    requireElement("#technical-mode").textContent = snapshot.mode;
    rendererStatus.textContent = snapshot.renderer;
    modeButtons.forEach((button) => button.setAttribute("aria-pressed", String(button.dataset.modeButton === snapshot.mode)));
    viewButtons.forEach((button) => {
      if (button.dataset.view !== "reset") button.setAttribute("aria-pressed", String(button.dataset.view === snapshot.view));
    });
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

  const dispose = () => atlasRenderer?.dispose();
  window.addEventListener("pagehide", dispose, { once: true });
  window.__archviewFoundation = Object.freeze({ state, dispose });
  return state.read();
}
