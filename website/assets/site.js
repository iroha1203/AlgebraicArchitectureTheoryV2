const navLinks = Array.from(document.querySelectorAll(".site-nav a"));

if (window.location.protocol === "file:") {
  document.querySelectorAll('a[href$="/"]').forEach((link) => {
    const href = link.getAttribute("href");

    if (!href || href.startsWith("http")) return;

    link.addEventListener("click", (event) => {
      event.preventDefault();
      window.location.href = new URL(`${href}index.html`, window.location.href);
    });
  });
}

const hashNavLinks = navLinks.filter((link) =>
  link.getAttribute("href")?.startsWith("#")
);
const sections = hashNavLinks
  .map((link) => document.querySelector(link.getAttribute("href")))
  .filter(Boolean);

if ("IntersectionObserver" in window && sections.length > 0) {
  const activeById = new Map(
    hashNavLinks.map((link) => [link.getAttribute("href").slice(1), link])
  );

  const observer = new IntersectionObserver(
    (entries) => {
      const visible = entries
        .filter((entry) => entry.isIntersecting)
        .sort((a, b) => b.intersectionRatio - a.intersectionRatio)[0];

      if (!visible) return;

      hashNavLinks.forEach((link) => link.classList.remove("is-active"));
      activeById.get(visible.target.id)?.classList.add("is-active");
    },
    { rootMargin: "-20% 0px -65% 0px", threshold: [0.1, 0.35, 0.6] }
  );

  sections.forEach((section) => observer.observe(section));
}

const currentPath = window.location.pathname.replace(/index\.html$/, "");

navLinks
  .filter((link) => !link.getAttribute("href")?.startsWith("#"))
  .forEach((link) => {
    const target = new URL(link.getAttribute("href"), window.location.href);
    const targetPath = target.pathname.replace(/index\.html$/, "");

    if (targetPath === currentPath) {
      link.classList.add("is-active");
    }
  });

document.querySelector("[data-current-year]").textContent =
  new Date().getFullYear();

const sftPages = [
  { href: "", label: "SFT Overview" },
  { href: "field/", label: "1. The Field" },
  { href: "field/codebase-memory-artifact-force/", label: "1-1. Memory and Force" },
  { href: "field/agents-organization-recurrent-paths/", label: "1-2. Agents and Organization" },
  { href: "field/governance-feedback-futures/", label: "1-3. Feedback and Futures" },
  { href: "computation/", label: "2. The Computation" },
  { href: "computation/slice-observation/", label: "2-1. Slice and Observation" },
  { href: "computation/support-step-forecast-cone/", label: "2-2. Support and Cone" },
  { href: "computation/envelope-calibration/", label: "2-3. Envelope and Calibration" },
  { href: "intervention/", label: "3. The Intervention" },
  { href: "intervention/governance-attractor-engineering/", label: "3-1. Governance and Attractor" },
  { href: "intervention/ai-proposal-governance/", label: "3-2. AI Proposal Governance" },
  { href: "intervention/lifecycle-closed-loop/", label: "3-3. Lifecycle and Closed Loop" },
];

const sftReferences = [
  { href: "formal-core/", label: "Formal Core" },
  { href: "formal-anchors/", label: "Formal Anchors" },
  { href: "theorem-candidates/", label: "Theorem Candidates" },
  { href: "research-program/", label: "Research Program" },
  { href: "positioning/", label: "Positioning" },
  { href: "status/", label: "Status" },
  { href: "glossary/", label: "Glossary" },
];

const currentSftPath = (() => {
  const pathname = window.location.pathname.replace(/index\.html$/, "");
  const marker = "/sft/";
  const markerIndex = pathname.indexOf(marker);

  if (markerIndex === -1) return null;
  return pathname.slice(markerIndex + marker.length);
})();

const sftRelativeHref = (target) => {
  if (currentSftPath === null) return target || "./";

  const depth = currentSftPath.split("/").filter(Boolean).length;
  const prefix = "../".repeat(depth);

  if (!target) return prefix || "./";
  return `${prefix}${target}`;
};

const buildSftSourcePanel = (title, items, open = false) => {
  const panel = document.createElement("div");
  panel.className = "source-panel";
  if (open) panel.dataset.sidebarOpen = "true";

  const heading = document.createElement("h2");
  heading.textContent = title;
  panel.appendChild(heading);

  const list = document.createElement("ul");
  items.forEach((item) => {
    const listItem = document.createElement("li");
    const link = document.createElement("a");
    link.href = sftRelativeHref(item.href);
    link.textContent = item.label;

    if (currentSftPath === item.href) {
      link.setAttribute("aria-current", "page");
    }

    listItem.appendChild(link);
    list.appendChild(listItem);
  });

  panel.appendChild(list);
  return panel;
};

if (currentSftPath !== null) {
  document.querySelectorAll(".article-sidebar").forEach((sidebar) => {
    sidebar.querySelectorAll(":scope > .source-panel").forEach((panel) => {
      panel.remove();
    });

    sidebar.appendChild(buildSftSourcePanel("SFT pages", sftPages, true));
    sidebar.appendChild(buildSftSourcePanel("SFT references", sftReferences));
  });
}

document
  .querySelectorAll(
    ".article-sidebar > .toc-panel, .article-sidebar > .source-panel, .article-sidebar > .version-panel, .article-sidebar > .boundary-note"
  )
  .forEach((panel, index) => {
    const heading = panel.querySelector(":scope > h2");
    if (!heading) return;

    const panelId =
      panel.id || `sidebar-panel-${index + 1}-${heading.textContent.trim().toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/^-|-$/g, "")}`;
    panel.id = panelId;

    const content = document.createElement("div");
    content.id = `${panelId}-content`;
    content.className = "sidebar-panel-content";

    Array.from(panel.children)
      .filter((child) => child !== heading)
      .forEach((child) => {
        content.appendChild(child);
      });
    panel.appendChild(content);

    const button = document.createElement("button");
    button.type = "button";
    button.className = "sidebar-toggle";
    button.setAttribute("aria-controls", content.id);
    button.textContent = heading.textContent;
    heading.replaceChildren(button);

    const expanded =
      panel.classList.contains("toc-panel") || panel.dataset.sidebarOpen === "true";
    button.setAttribute("aria-expanded", String(expanded));
    panel.classList.toggle("is-open", expanded);
    content.hidden = !expanded;

    button.addEventListener("click", () => {
      const nextExpanded = button.getAttribute("aria-expanded") !== "true";
      button.setAttribute("aria-expanded", String(nextExpanded));
      panel.classList.toggle("is-open", nextExpanded);
      content.hidden = !nextExpanded;
    });
  });

document.querySelectorAll("[data-copy-code]").forEach((button) => {
  const figure = button.closest(".code-panel");
  const code = figure?.querySelector("code");

  button.addEventListener("click", async () => {
    if (!code) return;

    try {
      await navigator.clipboard.writeText(code.textContent.trimEnd());
      const original = button.textContent;
      button.textContent = "Copied";
      window.setTimeout(() => {
        button.textContent = original;
      }, 1200);
    } catch {
      button.textContent = "Copy failed";
      window.setTimeout(() => {
        button.textContent = "Copy";
      }, 1200);
    }
  });
});
