const navLinks = Array.from(document.querySelectorAll(".site-nav a"));
const sections = navLinks
  .map((link) => document.querySelector(link.getAttribute("href")))
  .filter(Boolean);

if ("IntersectionObserver" in window && sections.length > 0) {
  const activeById = new Map(
    navLinks.map((link) => [link.getAttribute("href").slice(1), link])
  );

  const observer = new IntersectionObserver(
    (entries) => {
      const visible = entries
        .filter((entry) => entry.isIntersecting)
        .sort((a, b) => b.intersectionRatio - a.intersectionRatio)[0];

      if (!visible) return;

      navLinks.forEach((link) => link.classList.remove("is-active"));
      activeById.get(visible.target.id)?.classList.add("is-active");
    },
    { rootMargin: "-20% 0px -65% 0px", threshold: [0.1, 0.35, 0.6] }
  );

  sections.forEach((section) => observer.observe(section));
}

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
