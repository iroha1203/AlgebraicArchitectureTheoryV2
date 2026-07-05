const themeStorageKey = "aat-sft-theme";
const systemDarkQuery = window.matchMedia("(prefers-color-scheme: dark)");
let storedTheme = null;

try {
  storedTheme = localStorage.getItem(themeStorageKey);
} catch {
  storedTheme = null;
}

if (storedTheme === "light" || storedTheme === "dark") {
  document.documentElement.dataset.theme = storedTheme;
}

function getEffectiveTheme() {
  const selectedTheme = document.documentElement.dataset.theme;
  if (selectedTheme === "light" || selectedTheme === "dark") return selectedTheme;
  return systemDarkQuery.matches ? "dark" : "light";
}

function updateThemeToggle(button) {
  const effectiveTheme = getEffectiveTheme();
  const nextTheme = effectiveTheme === "dark" ? "light" : "dark";
  const icon =
    effectiveTheme === "dark"
      ? '<svg class="theme-toggle-icon" viewBox="0 0 24 24" aria-hidden="true"><path d="M20.2 14.8A7.4 7.4 0 0 1 9.2 3.8 8.3 8.3 0 1 0 20.2 14.8Z" fill="none" stroke="currentColor" stroke-width="1.9" stroke-linecap="round" stroke-linejoin="round"/></svg>'
      : '<svg class="theme-toggle-icon" viewBox="0 0 24 24" aria-hidden="true"><path d="M12 3v2.5M12 18.5V21M4.6 4.6l1.8 1.8M17.6 17.6l1.8 1.8M3 12h2.5M18.5 12H21M4.6 19.4l1.8-1.8M17.6 6.4l1.8-1.8M12 8a4 4 0 1 0 0 8 4 4 0 0 0 0-8Z" fill="none" stroke="currentColor" stroke-width="1.9" stroke-linecap="round" stroke-linejoin="round"/></svg>';

  button.innerHTML = icon;
  button.setAttribute(
    "aria-label",
    `Current theme: ${effectiveTheme}. Switch to ${nextTheme} theme`
  );
  button.title = `Current theme: ${effectiveTheme}. Switch to ${nextTheme} theme`;
}

document.querySelectorAll(".header-inner").forEach((header) => {
  const nav = header.querySelector(".site-nav");
  if (!nav || header.querySelector(".theme-toggle")) return;

  const actions = document.createElement("div");
  actions.className = "header-actions";
  nav.before(actions);
  actions.appendChild(nav);

  const button = document.createElement("button");
  button.type = "button";
  button.className = "theme-toggle";
  button.setAttribute("aria-live", "polite");
  updateThemeToggle(button);

  button.addEventListener("click", () => {
    const nextTheme = getEffectiveTheme() === "dark" ? "light" : "dark";
    document.documentElement.dataset.theme = nextTheme;
    try {
      localStorage.setItem(themeStorageKey, nextTheme);
    } catch {}
    updateThemeToggle(button);
  });

  systemDarkQuery.addEventListener("change", () => {
    if (!document.documentElement.dataset.theme) {
      updateThemeToggle(button);
    }
  });

  actions.appendChild(button);
});

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

const tocLinks = Array.from(document.querySelectorAll(".toc-panel a")).filter(
  (link) => link.getAttribute("href")?.startsWith("#")
);
const tocSections = tocLinks
  .map((link) => document.getElementById(link.getAttribute("href").slice(1)))
  .filter(Boolean);

if ("IntersectionObserver" in window && tocSections.length > 0) {
  const tocLinkById = new Map(
    tocLinks.map((link) => [link.getAttribute("href").slice(1), link])
  );

  const tocVisibleIds = new Set();

  const atPageBottom = () =>
    window.innerHeight + window.scrollY >= document.scrollingElement.scrollHeight - 4;

  const setActiveTocSection = (id) => {
    const link = tocLinkById.get(id);
    if (!link || link.classList.contains("is-active")) return;

    tocLinks.forEach((other) => other.classList.remove("is-active"));
    link.classList.add("is-active");
  };

  const tocObserver = new IntersectionObserver(
    (entries) => {
      entries.forEach((entry) => {
        if (entry.isIntersecting) {
          tocVisibleIds.add(entry.target.id);
        } else {
          tocVisibleIds.delete(entry.target.id);
        }
      });

      // At the very end of the page the observer band never reaches a short
      // final section, so bottom-out pins the last section instead.
      const current = atPageBottom()
        ? tocSections[tocSections.length - 1]
        : tocSections.find((section) => tocVisibleIds.has(section.id));

      if (current) {
        setActiveTocSection(current.id);
      } else {
        // The band sits in the hero above the first section: nothing is current.
        tocLinks.forEach((link) => link.classList.remove("is-active"));
      }
    },
    { rootMargin: "-15% 0px -70% 0px", threshold: 0 }
  );

  tocSections.forEach((section) => tocObserver.observe(section));

  // The sticky sidebar can be taller than the viewport. Let its scroll
  // position follow the page's reading progress, so the end of the page
  // also shows the end of the sidebar. Hover pauses the coupling so the
  // reader can scroll the sidebar by hand.
  const sidebarScroller = document.querySelector(".article-sidebar");
  let sidebarSyncQueued = false;

  const syncSidebarScroll = () => {
    sidebarSyncQueued = false;
    if (!sidebarScroller || document.body.classList.contains("sidebar-open")) return;
    if (sidebarScroller.matches(":hover")) return;

    const sidebarRange = sidebarScroller.scrollHeight - sidebarScroller.clientHeight;
    const pageRange = document.scrollingElement.scrollHeight - window.innerHeight;
    if (sidebarRange <= 0 || pageRange <= 0) return;

    sidebarScroller.scrollTop = (window.scrollY / pageRange) * sidebarRange;
  };

  window.addEventListener(
    "scroll",
    () => {
      if (atPageBottom()) {
        setActiveTocSection(tocSections[tocSections.length - 1].id);
      }
      if (!sidebarSyncQueued) {
        sidebarSyncQueued = true;
        window.requestAnimationFrame(syncSidebarScroll);
      }
    },
    { passive: true }
  );
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

const fabSidebar = document.querySelector(".article-sidebar");
if (fabSidebar) {
  const fab = document.createElement("button");
  fab.type = "button";
  fab.className = "sidebar-fab";
  fab.setAttribute("aria-label", "Open page navigation");
  fab.setAttribute("aria-expanded", "false");
  fab.innerHTML =
    '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" aria-hidden="true"><line x1="4" y1="6" x2="20" y2="6"></line><line x1="4" y1="12" x2="20" y2="12"></line><line x1="4" y1="18" x2="14" y2="18"></line></svg>';
  document.body.appendChild(fab);

  const setDrawer = (open) => {
    document.body.classList.toggle("sidebar-open", open);
    fab.setAttribute("aria-expanded", String(open));
    if (open) {
      fabSidebar.querySelectorAll(".sidebar-toggle").forEach((button) => {
        button.setAttribute("aria-expanded", "true");
        const panel = button.closest(".toc-panel, .source-panel, .version-panel, .boundary-note");
        const content = panel?.querySelector(".sidebar-panel-content");
        panel?.classList.add("is-open");
        if (content) content.hidden = false;
      });
    }
  };

  fab.addEventListener("click", () => {
    setDrawer(!document.body.classList.contains("sidebar-open"));
  });

  fabSidebar.addEventListener("click", (event) => {
    if (event.target.closest("a")) setDrawer(false);
  });

  document.addEventListener("keydown", (event) => {
    if (event.key === "Escape" && document.body.classList.contains("sidebar-open")) {
      setDrawer(false);
    }
  });
}
