import * as THREE from "three";
import { OrbitControls } from "three/addons/controls/OrbitControls.js";

const CAMERA_VIEWS = Object.freeze({
  isometric: { position: [14, 13, 18], target: [0, 0, 0] },
  top: { position: [0, 25, 0.01], target: [0, 0, 0] },
  front: { position: [0, 8, 24], target: [0, 0, 0] },
});

const ATOM_COLORS = Object.freeze({
  component: 0x6d7890,
  relation: 0x8c6f62,
  capability: 0x687b67,
  state: 0x9a765b,
  effect: 0xa35f38,
  authority: 0x596a78,
  contract: 0x756686,
  semantic: 0x7d745e,
  runtime: 0x4f7773,
});

function disposeTree(root) {
  root.traverse((object) => {
    object.geometry?.dispose();
    if (Array.isArray(object.material)) object.material.forEach((material) => material.dispose());
    else object.material?.dispose();
    object.material?.map?.dispose();
  });
  root.clear();
}

function atomGeometry(kind) {
  if (kind === "relation") return new THREE.OctahedronGeometry(0.38, 0);
  if (kind === "state") return new THREE.CylinderGeometry(0.38, 0.38, 0.34, 16);
  if (kind === "effect" || kind === "runtime") return new THREE.ConeGeometry(0.4, 0.72, 5);
  if (kind === "contract") return new THREE.TorusGeometry(0.3, 0.11, 8, 20);
  if (kind === "authority") return new THREE.DodecahedronGeometry(0.38, 0);
  if (kind === "semantic") return new THREE.SphereGeometry(0.38, 16, 12);
  return new THREE.BoxGeometry(0.62, 0.48, 0.62);
}

function labelSprite(text) {
  const canvas = document.createElement("canvas");
  canvas.width = 512;
  canvas.height = 96;
  const context = canvas.getContext("2d");
  context.clearRect(0, 0, canvas.width, canvas.height);
  context.fillStyle = "rgba(250, 247, 239, 0.92)";
  context.fillRect(0, 0, canvas.width, canvas.height);
  context.strokeStyle = "rgba(73, 68, 60, 0.24)";
  context.strokeRect(1, 1, canvas.width - 2, canvas.height - 2);
  context.fillStyle = "#292d2d";
  context.font = "30px Georgia, serif";
  context.textAlign = "center";
  context.textBaseline = "middle";
  context.fillText(text, canvas.width / 2, canvas.height / 2, canvas.width - 28);
  const texture = new THREE.CanvasTexture(canvas);
  texture.colorSpace = THREE.SRGBColorSpace;
  const sprite = new THREE.Sprite(new THREE.SpriteMaterial({ map: texture, transparent: true, depthWrite: false }));
  sprite.scale.set(4.8, 0.9, 1);
  return sprite;
}

export function createAtlasRenderer(host) {
  if (!(host instanceof HTMLElement)) throw new Error("Atlas canvas host was not found.");

  const renderer = new THREE.WebGLRenderer({ antialias: true, alpha: true });
  renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
  renderer.outputColorSpace = THREE.SRGBColorSpace;
  renderer.toneMapping = THREE.NeutralToneMapping;
  renderer.toneMappingExposure = 1;
  renderer.shadowMap.enabled = true;
  renderer.shadowMap.type = THREE.PCFSoftShadowMap;
  renderer.domElement.setAttribute("aria-label", "Paper Atlas three-dimensional canvas");
  host.replaceChildren(renderer.domElement);

  const scene = new THREE.Scene();
  scene.background = new THREE.Color(0xf4efe4);

  const camera = new THREE.PerspectiveCamera(38, 1, 0.1, 300);
  const controls = new OrbitControls(camera, renderer.domElement);
  controls.enableDamping = !window.matchMedia("(prefers-reduced-motion: reduce)").matches;
  controls.dampingFactor = 0.07;
  controls.autoRotate = false;
  controls.minDistance = 8;
  controls.maxDistance = 80;
  controls.maxPolarAngle = Math.PI * 0.49;

  const decorativeSurface = new THREE.Group();
  decorativeSurface.userData.visualChannel = "decoration";
  scene.add(decorativeSurface);

  const paper = new THREE.Mesh(
    new THREE.PlaneGeometry(70, 44),
    new THREE.MeshStandardMaterial({ color: 0xeee6d7, roughness: 1, metalness: 0 })
  );
  paper.rotation.x = -Math.PI / 2;
  paper.position.y = -0.035;
  paper.receiveShadow = true;
  decorativeSurface.add(paper);

  const constructionLines = new THREE.GridHelper(70, 35, 0xb9ad98, 0xd6ccbc);
  constructionLines.material.transparent = true;
  constructionLines.material.opacity = 0.16;
  constructionLines.position.y = 0;
  decorativeSurface.add(constructionLines);

  const architectureSurface = new THREE.Group();
  architectureSurface.userData.visualChannel = "architecture";
  scene.add(architectureSurface);
  const selectionSurface = new THREE.Group();
  scene.add(selectionSurface);
  let atomMeshes = [];
  let selectableMeshes = [];
  let onSelection = null;

  scene.add(new THREE.HemisphereLight(0xfffbf2, 0xb7aa91, 1.7));
  const daylight = new THREE.DirectionalLight(0xfff6e7, 2.1);
  daylight.position.set(-8, 18, 12);
  daylight.castShadow = true;
  daylight.shadow.mapSize.set(1024, 1024);
  daylight.shadow.camera.left = -28;
  daylight.shadow.camera.right = 28;
  daylight.shadow.camera.top = 20;
  daylight.shadow.camera.bottom = -20;
  scene.add(daylight);

  let frame = 0;
  let disposed = false;

  const resize = () => {
    const width = Math.max(1, host.clientWidth);
    const height = Math.max(1, host.clientHeight);
    renderer.setSize(width, height, false);
    camera.aspect = width / height;
    camera.updateProjectionMatrix();
  };

  const render = () => {
    if (disposed) return;
    controls.update();
    renderer.render(scene, camera);
    frame = window.requestAnimationFrame(render);
  };

  const setView = (name) => {
    const view = CAMERA_VIEWS[name];
    if (!view) throw new Error(`Unknown camera view: ${name}`);
    camera.position.fromArray(view.position);
    controls.target.fromArray(view.target);
    controls.update();
  };

  const reset = () => setView("isometric");
  reset();
  resize();

  const resizeObserver = new ResizeObserver(resize);
  resizeObserver.observe(host);
  frame = window.requestAnimationFrame(render);

  const selectAtom = (atomId) => {
    disposeTree(selectionSurface);
    for (const mesh of atomMeshes.filter((candidate) => candidate.userData.atomId === atomId)) {
      const ring = new THREE.Mesh(
        new THREE.RingGeometry(0.52, 0.62, 32),
        new THREE.MeshBasicMaterial({ color: 0x314d7d, side: THREE.DoubleSide, transparent: true, opacity: 0.92 })
      );
      ring.rotation.x = -Math.PI / 2;
      ring.position.copy(mesh.position);
      ring.position.y = 0.2;
      selectionSurface.add(ring);
    }
  };

  const setArchitecture = (index, layout, selectHandler) => {
    disposeTree(architectureSurface);
    disposeTree(selectionSurface);
    atomMeshes = [];
    selectableMeshes = [];
    onSelection = selectHandler;
    if (!index || index.empty || !layout) return Object.freeze({ contextPlates: 0, subjectGroups: 0, atomGlyphs: 0, restrictions: 0, sharedSupports: 0 });

    layout.contexts.forEach((contextLayout, contextIndex) => {
      const context = index.contextsById.get(contextLayout.id);
      const { x, y, z } = contextLayout.position;
      const plate = new THREE.Mesh(
        new THREE.BoxGeometry(contextLayout.width, 0.16, contextLayout.height),
        new THREE.MeshStandardMaterial({ color: contextIndex % 2 === 0 ? 0xd9d0bf : 0xe1d8c8, roughness: 0.96, metalness: 0, transparent: true, opacity: 0.92 })
      );
      plate.position.set(x, y, z);
      plate.receiveShadow = true;
      plate.userData = { contextId: context.id, kind: "context" };
      architectureSurface.add(plate);
      selectableMeshes.push(plate);

      const label = labelSprite(context.label || context.id);
      label.position.set(x, 0.32, z - contextLayout.height / 2 + 0.65);
      label.userData = { contextId: context.id, kind: "context-label" };
      architectureSurface.add(label);
    });

    for (const subject of layout.subjects) {
      const marker = labelSprite(subject.subject);
      marker.scale.set(2.7, 0.52, 1);
      marker.position.set(subject.position.x, subject.position.y, subject.position.z - 1.15);
      marker.userData = { kind: "subject", subject: subject.subject, contextId: subject.contextId };
      architectureSurface.add(marker);
      selectableMeshes.push(marker);
    }

    for (const atomLayout of layout.atoms) {
      const atom = index.atomsById.get(atomLayout.atomId);
      const mesh = new THREE.Mesh(
        atomGeometry(atom.kind),
        new THREE.MeshStandardMaterial({ color: ATOM_COLORS[atom.kind] || 0x6d7890, roughness: 0.78, metalness: 0 })
      );
      mesh.position.set(atomLayout.position.x, atomLayout.position.y, atomLayout.position.z);
      mesh.castShadow = true;
      mesh.userData = { atomId: atom.id, contextId: atomLayout.contextId, kind: "atom" };
      architectureSurface.add(mesh);
      atomMeshes.push(mesh);
      selectableMeshes.push(mesh);
    }

    for (const restriction of layout.restrictions) {
      const start = new THREE.Vector3(restriction.source.x, 0.27, restriction.source.z);
      const end = new THREE.Vector3(restriction.target.x, 0.27, restriction.target.z);
      const direction = end.clone().sub(start);
      const length = direction.length();
      if (length > 0) architectureSurface.add(new THREE.ArrowHelper(direction.normalize(), start, length, 0x77736a, 0.55, 0.25));
    }

    for (const support of layout.sharedSupports) {
      const sheet = new THREE.Mesh(
        new THREE.CircleGeometry(1.15, 32),
        new THREE.MeshStandardMaterial({ color: 0xc9d2d0, transparent: true, opacity: 0.44, roughness: 1, side: THREE.DoubleSide })
      );
      sheet.rotation.x = -Math.PI / 2;
      sheet.position.set(support.position.x, support.position.y, support.position.z);
      sheet.userData = { kind: "shared-support", atomId: support.atomId };
      architectureSurface.add(sheet);
    }
    return Object.freeze({ contextPlates: layout.contexts.length, subjectGroups: layout.subjects.length, atomGlyphs: atomMeshes.length, restrictions: layout.restrictions.length, sharedSupports: layout.sharedSupports.length });
  };

  const raycaster = new THREE.Raycaster();
  const pointer = new THREE.Vector2();
  const handlePointer = (event) => {
    if (!selectableMeshes.length) return;
    const bounds = renderer.domElement.getBoundingClientRect();
    pointer.x = ((event.clientX - bounds.left) / bounds.width) * 2 - 1;
    pointer.y = -((event.clientY - bounds.top) / bounds.height) * 2 + 1;
    raycaster.setFromCamera(pointer, camera);
    const hit = raycaster.intersectObjects(selectableMeshes, false)[0];
    if (!hit) return;
    const data = hit.object.userData;
    if (data.kind === "atom") {
      selectAtom(data.atomId);
      onSelection?.("atom", data.atomId, data.contextId);
    } else if (data.kind === "context") onSelection?.("context", data.contextId);
    else if (data.kind === "subject") onSelection?.("subject", data.subject, data.contextId);
  };
  renderer.domElement.addEventListener("pointerdown", handlePointer);

  return Object.freeze({
    setView,
    reset,
    setArchitecture,
    selectAtom,
    dispose() {
      if (disposed) return;
      disposed = true;
      window.cancelAnimationFrame(frame);
      resizeObserver.disconnect();
      controls.dispose();
      renderer.domElement.removeEventListener("pointerdown", handlePointer);
      disposeTree(architectureSurface);
      disposeTree(selectionSurface);
      paper.geometry.dispose();
      paper.material.dispose();
      constructionLines.geometry.dispose();
      constructionLines.material.dispose();
      renderer.dispose();
      renderer.domElement.remove();
    },
  });
}
