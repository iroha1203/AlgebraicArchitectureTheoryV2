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
  if (kind === "capability") return new THREE.TetrahedronGeometry(0.44, 0);
  if (kind === "state") return new THREE.CylinderGeometry(0.38, 0.38, 0.34, 16);
  if (kind === "effect") return new THREE.ConeGeometry(0.4, 0.72, 5);
  if (kind === "runtime") return new THREE.CapsuleGeometry(0.24, 0.5, 5, 10);
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
  renderer.domElement.setAttribute("aria-describedby", "camera-help");
  renderer.domElement.tabIndex = 0;
  host.replaceChildren(renderer.domElement);

  const scene = new THREE.Scene();
  scene.background = new THREE.Color(0xf4efe4);

  const camera = new THREE.PerspectiveCamera(38, 1, 0.1, 300);
  const controls = new OrbitControls(camera, renderer.domElement);
  const reducedMotion = window.matchMedia("(prefers-reduced-motion: reduce)").matches;
  controls.enableDamping = !reducedMotion;
  controls.dampingFactor = 0.07;
  controls.autoRotate = false;
  controls.enableRotate = true;
  controls.enablePan = true;
  controls.enableZoom = true;
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
  let analysisSupport = null;
  let currentLayout = null;
  let currentIndex = null;
  let currentSelection = null;
  let onSelection = null;
  let onSceneHover = null;
  let architectureGeneration = 0;
  let overviewCenter = new THREE.Vector3();
  let overviewScale = 1;

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
  const compass = document.querySelector("#atlas-compass");
  const compassNeedle = document.querySelector("#atlas-compass-needle");

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
    if (compassNeedle) {
      const direction = camera.position.clone().sub(controls.target);
      const bearing = THREE.MathUtils.radToDeg(Math.atan2(direction.x, direction.z));
      compassNeedle.style.transform = `rotate(${-bearing}deg)`;
      compassNeedle.style.transformOrigin = "21px 21px";
      compass?.setAttribute("aria-label", `Atlas camera bearing ${Math.round((bearing + 360) % 360)} degrees`);
    }
    renderer.render(scene, camera);
    frame = window.requestAnimationFrame(render);
  };

  const setView = (name) => {
    const view = CAMERA_VIEWS[name];
    if (!view) throw new Error(`Unknown camera view: ${name}`);
    const damping = controls.enableDamping;
    controls.enableDamping = false;
    controls.update();
    camera.position.fromArray(view.position).multiplyScalar(overviewScale).add(overviewCenter);
    controls.target.copy(overviewCenter);
    controls.update();
    controls.enableDamping = damping;
  };

  const reset = () => setView("isometric");
  reset();
  resize();

  const resizeObserver = new ResizeObserver(resize);
  resizeObserver.observe(host);
  frame = window.requestAnimationFrame(render);

  const selectionMatches = (data, selection) => {
    if (!selection) return false;
    if (selection.kind === "source") return data.kind === "atom" && data.atomId === selection.atomId && (!selection.contextId || data.contextId === selection.contextId);
    if (selection.kind === "atom") return data.kind === "atom" && data.atomId === selection.id && (!selection.contextId || data.contextId === selection.contextId);
    if (selection.kind === "context") return data.kind === "context" && data.contextId === selection.id;
    if (selection.kind === "subject") return data.kind === "subject" && data.subject === selection.id && data.contextId === selection.contextId;
    if (selection.kind === "restriction") return data.kind === "restriction" && data.sourceId === selection.sourceId && data.targetId === selection.targetId;
    if (selection.kind === "shared-support") return data.kind === "shared-support" && data.atomId === selection.atomId;
    return false;
  };

  const setSelection = (selection, selections = []) => {
    currentSelection = selection;
    disposeTree(selectionSurface);
    const activeSelections = selections.length ? selections : selection ? [selection] : [];
    const matches = selectableMeshes.filter((candidate) => activeSelections.some((entry) => selectionMatches(candidate.userData || {}, entry)));
    const contextIds = new Set();
    for (const object of matches) {
      const bounds = new THREE.Box3().setFromObject(object);
      if (bounds.isEmpty()) continue;
      const center = bounds.getCenter(new THREE.Vector3());
      const size = bounds.getSize(new THREE.Vector3());
      const ring = new THREE.Mesh(
        new THREE.RingGeometry(0.84, 1, 48),
        new THREE.MeshBasicMaterial({ color: 0x314d7d, side: THREE.DoubleSide, transparent: true, opacity: 0.94, depthTest: false })
      );
      ring.rotation.x = -Math.PI / 2;
      ring.position.set(center.x, Math.max(0.19, bounds.min.y + 0.04), center.z);
      ring.scale.set(Math.max(0.56, size.x / 2 + 0.24), Math.max(0.56, size.z / 2 + 0.24), 1);
      ring.renderOrder = 10;
      ring.userData = { kind: "selection-ring", visualChannel: "decoration" };
      selectionSurface.add(ring);
      if (object.userData.contextId && object.userData.kind !== "context") contextIds.add(object.userData.contextId);
    }
    if (!matches.length && currentLayout) {
      for (const entry of activeSelections) {
        const atomId = entry.kind === "source" ? entry.atomId : entry.kind === "atom" ? entry.id : null;
        const points = atomId ? currentLayout.atoms.filter((row) => row.atomId === atomId && (!entry.contextId || row.contextId === entry.contextId))
          : entry.kind === "subject" ? currentLayout.subjects.filter((row) => row.subject === entry.id && row.contextId === entry.contextId)
          : entry.kind === "context" ? currentLayout.contexts.filter((row) => row.id === entry.id).map((row) => ({ ...row, contextId: row.id })) : [];
        for (const point of points) {
          const ring = new THREE.Mesh(new THREE.RingGeometry(0.84, 1, 48), new THREE.MeshBasicMaterial({ color: 0x314d7d, side: THREE.DoubleSide, transparent: true, opacity: 0.94, depthTest: false }));
          ring.rotation.x = -Math.PI / 2;
          ring.position.set(point.position.x, 0.2, point.position.z);
          ring.renderOrder = 10;
          selectionSurface.add(ring);
          contextIds.add(point.contextId);
          if (atomId && currentIndex) {
            const atom = currentIndex.atomsById.get(atomId);
            if (atom) {
              const detail = new THREE.Mesh(atomGeometry(atom.kind), new THREE.MeshStandardMaterial({ color: ATOM_COLORS[atom.kind] || 0x6d7890, roughness: 0.78, metalness: 0 }));
              detail.position.set(point.position.x, point.position.y, point.position.z);
              detail.userData = { kind: "selected-atom-detail", visualChannel: "derived" };
              selectionSurface.add(detail);
            }
          }
        }
      }
    }
    for (const contextId of contextIds) {
      const plate = selectableMeshes.find((candidate) => candidate.userData?.kind === "context" && candidate.userData.contextId === contextId);
      if (!plate) continue;
      const helper = new THREE.Box3Helper(new THREE.Box3().setFromObject(plate), 0x7185ac);
      helper.userData = { kind: "selection-context-frame", visualChannel: "decoration" };
      selectionSurface.add(helper);
    }
    const rings = selectionSurface.children.filter((object) => object.geometry?.type === "RingGeometry").length;
    return Object.freeze({ kind: selection?.kind || null, id: selection?.id || selection?.atomId || null, selections: activeSelections.length, rings, contextFrames: contextIds.size, outlines: rings });
  };

  const selectAtom = (atomId) => setSelection({ kind: "atom", id: atomId });

  const selectionPoint = (selection = currentSelection) => {
    if (!selection || !currentLayout) return false;
    let point = null;
    if (selection.kind === "context") point = currentLayout.contexts.find((row) => row.id === selection.id)?.position;
    if (selection.kind === "subject") point = currentLayout.subjects.find((row) => row.subject === selection.id && row.contextId === selection.contextId)?.position;
    if (["atom", "source"].includes(selection.kind)) {
      const atomId = selection.kind === "source" ? selection.atomId : selection.id;
      point = currentLayout.atoms.find((row) => row.atomId === atomId && (!selection.contextId || row.contextId === selection.contextId))?.position;
    }
    if (selection.kind === "restriction") {
      const row = currentLayout.restrictions.find((candidate) => candidate.sourceId === selection.sourceId && candidate.targetId === selection.targetId);
      if (row) point = { x: (row.source.x + row.target.x) / 2, y: 0.3, z: (row.source.z + row.target.z) / 2 };
    }
    if (selection.kind === "shared-support") point = currentLayout.sharedSupports.find((row) => row.atomId === selection.atomId)?.position;
    if (selection.kind === "cover") return new THREE.Vector3(0, 0, 0);
    if (!point) return null;
    return new THREE.Vector3(point.x, point.y || 0, point.z);
  };

  const focusSelection = (selection = currentSelection) => {
    if (selection?.kind === "cover") return reset(), true;
    const target = selectionPoint(selection);
    if (!target) return false;
    const offset = camera.position.clone().sub(controls.target);
    const distance = THREE.MathUtils.clamp(offset.length(), controls.minDistance, 34);
    if (!offset.length()) offset.set(14, 13, 18);
    offset.setLength(distance);
    const damping = controls.enableDamping;
    controls.enableDamping = false;
    controls.update();
    controls.target.copy(target);
    camera.position.copy(target).add(offset);
    controls.update();
    controls.enableDamping = damping;
    return true;
  };

  const screenPointForSelection = (selection = currentSelection) => {
    const point = selectionPoint(selection);
    if (!point) return null;
    const projected = point.clone().project(camera);
    const bounds = renderer.domElement.getBoundingClientRect();
    return Object.freeze({ x: bounds.left + ((projected.x + 1) / 2) * bounds.width, y: bounds.top + ((1 - projected.y) / 2) * bounds.height });
  };

  const cameraState = () => Object.freeze({
    position: Object.freeze(camera.position.toArray()),
    target: Object.freeze(controls.target.toArray()),
    distance: camera.position.distanceTo(controls.target),
    rotate: controls.enableRotate,
    pan: controls.enablePan,
    zoom: controls.enableZoom,
    reducedMotion,
  });

  const nudgeCamera = (command) => {
    const offset = camera.position.clone().sub(controls.target);
    if (command === "rotate-left" || command === "rotate-right") offset.applyAxisAngle(new THREE.Vector3(0, 1, 0), command === "rotate-left" ? 0.14 : -0.14);
    if (command === "zoom-in" || command === "zoom-out") offset.multiplyScalar(command === "zoom-in" ? 0.86 : 1.16).clampLength(controls.minDistance, controls.maxDistance);
    if (command.startsWith("pan-")) {
      const forward = controls.target.clone().sub(camera.position).setY(0).normalize();
      const right = new THREE.Vector3().crossVectors(forward, camera.up).normalize();
      const delta = command === "pan-left" ? right.multiplyScalar(-1) : command === "pan-right" ? right : command === "pan-up" ? forward : forward.multiplyScalar(-1);
      camera.position.add(delta);
      controls.target.add(delta);
    } else camera.position.copy(controls.target).add(offset);
    controls.update();
    return cameraState();
  };

  const rememberMaterial = (material) => {
    if (!material.userData.archviewBase) material.userData.archviewBase = { color: material.color?.getHex() ?? null, opacity: material.opacity, transparent: material.transparent };
    return material.userData.archviewBase;
  };

  const styleObject = (object, emphasis, color = null) => object.traverse((child) => {
    const materials = Array.isArray(child.material) ? child.material : child.material ? [child.material] : [];
    materials.forEach((material) => {
      const base = rememberMaterial(material);
      material.opacity = emphasis === "dim" ? Math.min(base.opacity, 0.16) : base.opacity;
      material.transparent = emphasis === "dim" || base.transparent;
      if (material.color && base.color !== null) material.color.setHex(emphasis === "support" && color !== null ? color : base.color);
      material.needsUpdate = true;
    });
  });

  const setAnalysisSupport = (support) => {
    analysisSupport = support;
    const edgeVisuals = [];
    const active = support && (support.atomIds.length || support.contextIds.length || support.edgeIds.length || support.sharedAtomIds.length);
    const highlight = ({ measured_nonzero: 0xb87932, measured_zero: 0x54799a, unmeasured: 0x7c7b76, unknown: 0x7c7b76, not_computed: 0x7c7b76 })[support?.state] || 0x3e7780;
    for (const object of architectureSurface.children) {
      const data = object.userData || {};
      if (data.kind === "atom-instances") {
        const activeSet = new Set(support?.atomIds || []);
        data.instances.forEach((instance, index) => object.setColorAt(index, new THREE.Color(!active ? (ATOM_COLORS[data.atomKind] || 0x6d7890) : activeSet.has(instance.atomId) ? highlight : 0xb8b3a8)));
        if (object.instanceColor) object.instanceColor.needsUpdate = true;
        continue;
      }
      if (data.kind === "atom-points") {
        const colors = object.geometry.getAttribute("color");
        const activeSet = new Set(support?.atomIds || []);
        data.instances.forEach((instance, index) => {
          const color = new THREE.Color(!active ? (ATOM_COLORS[instance.atomKind] || 0x6d7890) : activeSet.has(instance.atomId) ? highlight : 0xb8b3a8);
          colors.setXYZ(index, color.r, color.g, color.b);
        });
        colors.needsUpdate = true;
        continue;
      }
      if (data.kind === "context-instances") {
        const supported = data.instances.some((instance) => support?.contextIds.includes(instance.contextId));
        object.material.color.setHex(!active ? 0xd9d0bf : supported ? highlight : 0xb8b3a8);
        continue;
      }
      const edgeId = data.kind === "restriction" ? `${data.sourceId}->${data.targetId}` : null;
      const supported = data.kind === "atom" ? support?.atomIds.includes(data.atomId)
        : ["context", "context-label", "subject"].includes(data.kind) ? support?.contextIds.includes(data.contextId)
        : data.kind === "restriction" ? support?.edgeIds.includes(edgeId)
        : data.kind === "shared-support" ? support?.sharedAtomIds.includes(data.atomId)
        : false;
      const edgeHighlight = data.kind !== "restriction" ? highlight
        : support?.unmeasuredEdgeIds?.includes(edgeId) ? 0x7c7b76
        : support?.mismatchEdgeIds?.includes(edgeId) ? 0xb87932
        : support?.agreementEdgeIds?.includes(edgeId) ? 0x54799a
        : 0x3e7780;
      styleObject(object, !active ? "base" : supported ? "support" : "dim", edgeHighlight);
      if (data.kind === "restriction") {
        let materialColor = null;
        object.traverse((child) => {
          if (materialColor !== null) return;
          const material = Array.isArray(child.material) ? child.material[0] : child.material;
          if (material?.color) materialColor = material.color.getHex();
        });
        edgeVisuals.push(Object.freeze({ edgeId, supported: Boolean(supported), color: materialColor }));
      }
    }
    return Object.freeze({ active: Boolean(active), atoms: support?.atomIds.length || 0, contexts: support?.contextIds.length || 0, edges: support?.edgeIds.length || 0, sharedSupports: support?.sharedAtomIds.length || 0, state: support?.state || null, edgeStates: Object.freeze({ agreement: support?.agreementEdgeIds?.length || 0, mismatch: support?.mismatchEdgeIds?.length || 0, unmeasured: support?.unmeasuredEdgeIds?.length || 0, participant: (support?.edgeIds || []).filter((edge) => !support?.agreementEdgeIds?.includes(edge) && !support?.mismatchEdgeIds?.includes(edge) && !support?.unmeasuredEdgeIds?.includes(edge)).length }), edgeVisuals: Object.freeze(edgeVisuals) });
  };

  const setArchitecture = (index, layout, selectHandler, hoverHandler = null) => {
    const startedAt = performance.now();
    const generation = ++architectureGeneration;
    disposeTree(architectureSurface);
    disposeTree(selectionSurface);
    atomMeshes = [];
    selectableMeshes = [];
    onSelection = selectHandler;
    onSceneHover = hoverHandler;
    analysisSupport = null;
    currentLayout = layout;
    currentIndex = index;
    currentSelection = null;
    overviewCenter.set(0, 0, 0);
    overviewScale = 1;
    decorativeSurface.scale.set(1, 1, 1);
    camera.far = 300;
    camera.updateProjectionMatrix();
    controls.maxDistance = 80;
    if (!index || index.empty || !layout) return Object.freeze({ contextPlates: 0, subjectGroups: 0, atomGlyphs: 0, restrictions: 0, sharedSupports: 0, progressive: false, complete: true });

    const layoutPoints = [...layout.contexts, ...layout.atoms].map((row) => row.position);
    if (layoutPoints.length) {
      const bounds = new THREE.Box3().setFromPoints(layoutPoints.map((point) => new THREE.Vector3(point.x, point.y || 0, point.z)));
      const candidateCenter = bounds.getCenter(new THREE.Vector3());
      const size = bounds.getSize(new THREE.Vector3());
      overviewScale = Math.max(1, Math.max(size.x / 22, size.z / 28));
      if (overviewScale > 1) overviewCenter.copy(candidateCenter);
      controls.maxDistance = Math.max(80, overviewScale * 80);
      decorativeSurface.scale.set(overviewScale, 1, overviewScale);
      camera.far = Math.max(300, overviewScale * 100);
      camera.updateProjectionMatrix();
      reset();
    }

    const progressive = layout.atoms.length > 500;
    if (progressive) {
      const geometry = new THREE.BoxGeometry(1, 0.16, 1);
      const material = new THREE.MeshBasicMaterial({ color: 0xd9d0bf });
      const plates = new THREE.InstancedMesh(geometry, material, layout.contexts.length);
      const matrix = new THREE.Matrix4();
      const quaternion = new THREE.Quaternion();
      const instances = [];
      layout.contexts.forEach((contextLayout, contextIndex) => {
        const baseColor = contextIndex % 2 === 0 ? 0xd9d0bf : 0xe1d8c8;
        matrix.compose(new THREE.Vector3(contextLayout.position.x, contextLayout.position.y, contextLayout.position.z), quaternion, new THREE.Vector3(contextLayout.width, 1, contextLayout.height));
        plates.setMatrixAt(contextIndex, matrix);
        instances.push({ contextId: contextLayout.id, kind: "context", baseColor, visualChannel: "derived", renderedFrom: `contexts.${contextLayout.id}` });
      });
      plates.instanceMatrix.needsUpdate = true;
      plates.userData = { kind: "context-instances", instances };
      architectureSurface.add(plates);
      selectableMeshes.push(plates);
    }
    for (const [contextIndex, contextLayout] of (progressive ? [] : layout.contexts).entries()) {
      const context = index.contextsById.get(contextLayout.id);
      const { x, y, z } = contextLayout.position;
      const plate = new THREE.Mesh(
        new THREE.BoxGeometry(contextLayout.width, 0.16, contextLayout.height),
        new THREE.MeshStandardMaterial({ color: contextIndex % 2 === 0 ? 0xd9d0bf : 0xe1d8c8, roughness: 0.96, metalness: 0, transparent: true, opacity: 0.92 })
      );
      plate.position.set(x, y, z);
      plate.receiveShadow = true;
      plate.userData = { contextId: context.id, kind: "context", visualChannel: "derived", renderedFrom: `contexts.${context.id}` };
      architectureSurface.add(plate);
      selectableMeshes.push(plate);

      const label = labelSprite(context.label || context.id);
      label.position.set(x, 0.32, z - contextLayout.height / 2 + 0.65);
      label.userData = { contextId: context.id, kind: "context-label" };
      architectureSurface.add(label);
    }

    const visibleSubjects = progressive ? [] : layout.subjects;
    for (const subject of visibleSubjects) {
      const marker = labelSprite(subject.subject);
      marker.scale.set(2.7, 0.52, 1);
      marker.position.set(subject.position.x, subject.position.y, subject.position.z - 1.15);
      marker.userData = { kind: "subject", subject: subject.subject, contextId: subject.contextId, visualChannel: "layout", renderedFrom: `exact subject ${subject.subject}` };
      architectureSurface.add(marker);
      selectableMeshes.push(marker);
    }

    const atomGeometryTypes = {};
    const addAtom = (atomLayout) => {
      const atom = index.atomsById.get(atomLayout.atomId);
      const mesh = new THREE.Mesh(
        atomGeometry(atom.kind),
        new THREE.MeshStandardMaterial({ color: ATOM_COLORS[atom.kind] || 0x6d7890, roughness: 0.78, metalness: 0 })
      );
      mesh.position.set(atomLayout.position.x, atomLayout.position.y, atomLayout.position.z);
      mesh.castShadow = true;
      mesh.userData = { atomId: atom.id, atomKind: atom.kind, contextId: atomLayout.contextId, kind: "atom", visualChannel: "derived", renderedFrom: `contexts.${atomLayout.contextId}.atoms` };
      architectureSurface.add(mesh);
      atomMeshes.push(mesh);
      selectableMeshes.push(mesh);
      atomGeometryTypes[atom.kind] = mesh.geometry.type;
    };

    let pointCloud = null;
    if (!progressive) for (const atomLayout of layout.atoms) addAtom(atomLayout);
    else {
      const geometry = new THREE.BufferGeometry();
      geometry.setAttribute("position", new THREE.BufferAttribute(new Float32Array(layout.atoms.length * 3), 3));
      geometry.setAttribute("color", new THREE.BufferAttribute(new Float32Array(layout.atoms.length * 3), 3));
      geometry.setDrawRange(0, 0);
      pointCloud = new THREE.Points(geometry, new THREE.PointsMaterial({ size: 0.72, sizeAttenuation: true, vertexColors: true, transparent: true, opacity: 0.92 }));
      pointCloud.userData = { kind: "atom-points", instances: [], visualChannel: "derived" };
      architectureSurface.add(pointCloud);
      atomMeshes.push(pointCloud);
      selectableMeshes.push(pointCloud);
      for (const kind of new Set(layout.atoms.map((row) => row.kind))) atomGeometryTypes[kind] = "Points";
    }

    if (progressive && layout.restrictions.length) {
      const points = [];
      for (const restriction of layout.restrictions) points.push(restriction.source.x, 0.27, restriction.source.z, restriction.target.x, 0.27, restriction.target.z);
      const geometry = new THREE.BufferGeometry();
      geometry.setAttribute("position", new THREE.Float32BufferAttribute(points, 3));
      const lines = new THREE.LineSegments(geometry, new THREE.LineBasicMaterial({ color: 0x77736a, transparent: true, opacity: 0.32 }));
      lines.userData = { kind: "restriction-bundle", visualChannel: "derived", renderedFrom: "contexts.*.restrictsTo", count: layout.restrictions.length };
      architectureSurface.add(lines);
    }
    for (const restriction of progressive ? [] : layout.restrictions) {
      const start = new THREE.Vector3(restriction.source.x, 0.27, restriction.source.z);
      const end = new THREE.Vector3(restriction.target.x, 0.27, restriction.target.z);
      const direction = end.clone().sub(start);
      const length = direction.length();
      if (length > 0) {
        const normalized = direction.clone().normalize();
        const arrow = new THREE.ArrowHelper(normalized, start, length, 0x77736a, 0.55, 0.25);
        arrow.userData = { kind: "restriction", sourceId: restriction.sourceId, targetId: restriction.targetId, visualChannel: "derived", renderedFrom: `contexts.${restriction.sourceId}.restrictsTo` };
        architectureSurface.add(arrow);
        const hitTarget = new THREE.Mesh(
          new THREE.CylinderGeometry(0.2, 0.2, length, 8),
          new THREE.MeshBasicMaterial({ transparent: true, opacity: 0.001, depthWrite: false })
        );
        hitTarget.position.copy(start).add(end).multiplyScalar(0.5);
        hitTarget.quaternion.setFromUnitVectors(new THREE.Vector3(0, 1, 0), normalized);
        hitTarget.userData = { ...arrow.userData };
        architectureSurface.add(hitTarget);
        selectableMeshes.push(hitTarget);
      }
    }

    if (progressive && layout.sharedSupports.length) {
      const geometry = new THREE.CircleGeometry(1.15, 16);
      geometry.rotateX(-Math.PI / 2);
      const mesh = new THREE.InstancedMesh(geometry, new THREE.MeshBasicMaterial({ color: 0xc9d2d0, transparent: true, opacity: 0.18, side: THREE.DoubleSide }), layout.sharedSupports.length);
      const matrix = new THREE.Matrix4();
      layout.sharedSupports.forEach((support, index) => { matrix.makeTranslation(support.position.x, support.position.y, support.position.z); mesh.setMatrixAt(index, matrix); });
      mesh.instanceMatrix.needsUpdate = true;
      mesh.userData = { kind: "shared-support-bundle", visualChannel: "derived", renderedFrom: "explicit Context Atom memberships", count: layout.sharedSupports.length };
      architectureSurface.add(mesh);
    }
    for (const support of progressive ? [] : layout.sharedSupports) {
      const sheet = new THREE.Mesh(
        new THREE.CircleGeometry(1.15, 32),
        new THREE.MeshStandardMaterial({ color: 0xc9d2d0, transparent: true, opacity: 0.44, roughness: 1, side: THREE.DoubleSide })
      );
      sheet.rotation.x = -Math.PI / 2;
      sheet.position.set(support.position.x, support.position.y, support.position.z);
      sheet.userData = { kind: "shared-support", atomId: support.atomId, contextIds: support.contextIds, visualChannel: "derived", renderedFrom: "explicit Context Atom memberships" };
      architectureSurface.add(sheet);
      selectableMeshes.push(sheet);
    }
    const stats = {
      contextPlates: layout.contexts.length,
      subjectGroups: layout.subjects.length,
      atomGlyphs: atomMeshes.length,
      totalAtoms: layout.atoms.length,
      restrictions: layout.restrictions.length,
      sharedSupports: layout.sharedSupports.length,
      progressive,
      complete: !progressive,
      batches: progressive ? 0 : 1,
      skeletonReady: true,
      subjectLabelLod: progressive ? "context" : "subject",
      atomLod: progressive ? "points" : "glyphs",
      startedAt,
      skeletonReadyAt: performance.now(),
      completedAt: progressive ? null : performance.now(),
      atomGeometryTypes,
      restrictionRecords: Object.freeze(layout.restrictions.map(({ sourceId, targetId }) => Object.freeze({ sourceId, targetId, renderedFrom: `contexts.${sourceId}.restrictsTo`, visualChannel: "derived" }))),
      sharedSupportRecords: Object.freeze(layout.sharedSupports.map(({ atomId, contextIds }) => Object.freeze({ atomId, contextIds, renderedFrom: "explicit Context Atom memberships", visualChannel: "derived" }))),
    };
    if (progressive) {
      const batchSize = 120;
      let cursor = 0;
      const appendBatch = () => {
        if (generation !== architectureGeneration || disposed) return;
        const stop = Math.min(layout.atoms.length, cursor + batchSize);
        const positions = pointCloud.geometry.getAttribute("position");
        const colors = pointCloud.geometry.getAttribute("color");
        while (cursor < stop) {
          const row = layout.atoms[cursor++];
          const index = cursor - 1;
          positions.setXYZ(index, row.position.x, row.position.y, row.position.z);
          const color = new THREE.Color(ATOM_COLORS[row.kind] || 0x6d7890);
          colors.setXYZ(index, color.r, color.g, color.b);
          pointCloud.userData.instances[index] = { atomId: row.atomId, atomKind: row.kind, contextId: row.contextId, kind: "atom", visualChannel: "derived", renderedFrom: `contexts.${row.contextId}.atoms` };
        }
        positions.needsUpdate = true;
        colors.needsUpdate = true;
        pointCloud.geometry.setDrawRange(0, cursor);
        stats.atomGlyphs = cursor;
        stats.batches += 1;
        stats.complete = cursor === layout.atoms.length;
        if (stats.complete) stats.completedAt = performance.now();
        window.__archviewRenderStats = stats;
        if (!stats.complete) window.requestAnimationFrame(appendBatch);
      };
      window.requestAnimationFrame(appendBatch);
    }
    return stats;
  };

  const raycaster = new THREE.Raycaster();
  const pointer = new THREE.Vector2();
  const hitAt = (event) => {
    if (!selectableMeshes.length) return;
    const bounds = renderer.domElement.getBoundingClientRect();
    pointer.x = ((event.clientX - bounds.left) / bounds.width) * 2 - 1;
    pointer.y = -((event.clientY - bounds.top) / bounds.height) * 2 + 1;
    raycaster.setFromCamera(pointer, camera);
    return raycaster.intersectObjects(selectableMeshes, false)[0] || null;
  };
  const hitData = (hit) => Array.isArray(hit?.object.userData?.instances) ? hit.object.userData.instances[hit.instanceId ?? hit.index] : hit?.object.userData;
  const selectHit = (hit, additive = false) => {
    if (!hit) return;
    const data = hitData(hit);
    if (data.kind === "atom") {
      onSelection?.("atom", data.atomId, data.contextId, additive);
    } else if (data.kind === "context") onSelection?.("context", data.contextId, null, additive);
    else if (data.kind === "subject") onSelection?.("subject", data.subject, data.contextId, additive);
    else if (data.kind === "restriction") onSelection?.("restriction", data.sourceId, data.targetId, additive);
    else if (data.kind === "shared-support") onSelection?.("shared-support", data.atomId, data.contextIds, additive);
  };
  let pointerStart = null;
  const handlePointerDown = (event) => { pointerStart = { x: event.clientX, y: event.clientY, button: event.button, pointerId: event.pointerId, maxDistance: 0 }; };
  const handlePointerUp = (event) => {
    if (!pointerStart || pointerStart.pointerId !== event.pointerId) return;
    const distance = Math.hypot(event.clientX - pointerStart.x, event.clientY - pointerStart.y);
    const select = pointerStart.button === 0 && event.button === 0 && pointerStart.maxDistance <= 5 && distance <= 5;
    pointerStart = null;
    if (select) selectHit(hitAt(event), event.shiftKey);
  };
  const handlePointerCancel = () => { pointerStart = null; };
  const handleContextMenu = (event) => event.preventDefault();
  const handleDoubleClick = (event) => {
    const hit = hitAt(event);
    if (!hit) return;
    selectHit(hit, event.shiftKey);
    focusSelection();
  };
  const handleHover = (event) => {
    const data = hitData(hitAt(event));
    renderer.domElement.style.cursor = data ? "pointer" : "grab";
    if (!data) return onSceneHover?.(null);
    if (data.kind === "restriction") onSceneHover?.(`Restriction · ${data.sourceId} → ${data.targetId} · Rendered from ${data.renderedFrom}`);
    else if (data.kind === "shared-support") onSceneHover?.(`Shared support · ${data.atomId} · ${data.contextIds.join(", ")}`);
    else if (data.kind === "context") onSceneHover?.(`Context · ${data.contextId}`);
    else if (data.kind === "subject") onSceneHover?.(`Subject group · ${data.subject} · ${data.contextId}`);
    else if (data.kind === "atom") onSceneHover?.(`Atom · ${data.atomId} · ${data.contextId}`);
  };
  const handlePointerMove = (event) => {
    if (pointerStart?.pointerId === event.pointerId) pointerStart.maxDistance = Math.max(pointerStart.maxDistance, Math.hypot(event.clientX - pointerStart.x, event.clientY - pointerStart.y));
    handleHover(event);
  };
  const handlePointerLeave = () => onSceneHover?.(null);
  const handleKeyboard = (event) => {
    const command = event.key === "ArrowLeft" ? (event.shiftKey ? "pan-left" : "rotate-left")
      : event.key === "ArrowRight" ? (event.shiftKey ? "pan-right" : "rotate-right")
      : event.key === "ArrowUp" && event.shiftKey ? "pan-up"
      : event.key === "ArrowDown" && event.shiftKey ? "pan-down"
      : ["+", "="].includes(event.key) ? "zoom-in"
      : event.key === "-" ? "zoom-out" : null;
    if (event.key === "Home") { event.preventDefault(); reset(); return; }
    if (!command) return;
    event.preventDefault();
    nudgeCamera(command);
  };
  renderer.domElement.addEventListener("pointerdown", handlePointerDown);
  renderer.domElement.addEventListener("pointerup", handlePointerUp);
  renderer.domElement.addEventListener("pointercancel", handlePointerCancel);
  renderer.domElement.addEventListener("dblclick", handleDoubleClick);
  renderer.domElement.addEventListener("contextmenu", handleContextMenu);
  renderer.domElement.addEventListener("pointermove", handlePointerMove);
  renderer.domElement.addEventListener("pointerleave", handlePointerLeave);
  renderer.domElement.addEventListener("keydown", handleKeyboard);

  return Object.freeze({
    setView,
    reset,
    setArchitecture,
    setAnalysisSupport,
    setSelection,
    selectAtom,
    focusSelection,
    screenPointForSelection,
    cameraState,
    nudgeCamera,
    dispose() {
      if (disposed) return;
      disposed = true;
      window.cancelAnimationFrame(frame);
      resizeObserver.disconnect();
      controls.dispose();
      renderer.domElement.removeEventListener("pointerdown", handlePointerDown);
      renderer.domElement.removeEventListener("pointerup", handlePointerUp);
      renderer.domElement.removeEventListener("pointercancel", handlePointerCancel);
      renderer.domElement.removeEventListener("dblclick", handleDoubleClick);
      renderer.domElement.removeEventListener("contextmenu", handleContextMenu);
      renderer.domElement.removeEventListener("pointermove", handlePointerMove);
      renderer.domElement.removeEventListener("pointerleave", handlePointerLeave);
      renderer.domElement.removeEventListener("keydown", handleKeyboard);
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
