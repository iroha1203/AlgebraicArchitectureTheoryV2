import * as THREE from "three";
import { OrbitControls } from "three/addons/controls/OrbitControls.js";

const CAMERA_VIEWS = Object.freeze({
  isometric: { position: [14, 13, 18], target: [0, 0, 0] },
  top: { position: [0, 25, 0.01], target: [0, 0, 0] },
  front: { position: [0, 8, 24], target: [0, 0, 0] },
});

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

  return Object.freeze({
    setView,
    reset,
    dispose() {
      if (disposed) return;
      disposed = true;
      window.cancelAnimationFrame(frame);
      resizeObserver.disconnect();
      controls.dispose();
      paper.geometry.dispose();
      paper.material.dispose();
      constructionLines.geometry.dispose();
      constructionLines.material.dispose();
      renderer.dispose();
      renderer.domElement.remove();
    },
  });
}
