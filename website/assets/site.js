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
