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

const compactSidebarQuery = window.matchMedia("(max-width: 880px)");

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

    const desktopExpanded =
      panel.classList.contains("toc-panel") || panel.dataset.sidebarOpen === "true";
    const expanded = compactSidebarQuery.matches ? false : desktopExpanded;
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
