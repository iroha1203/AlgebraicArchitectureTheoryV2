# Website

This directory is the source area for the public AAT / SFT research website.

The website is separate from `docs/`:

- `docs/` remains the repository's first-class research and implementation documentation.
- `website/` provides the public reading surface for GitHub Pages.

See [SITEMAP.md](SITEMAP.md) for the planned route structure, reading paths, and
pagination rules.

The public site uses English as the source of truth. Japanese explanations
should be handled as outreach articles on Qiita, Zenn, Hashnode, or similar
media, with links back to the canonical English pages.

## Intended Site Structure

```text
/
  Author profile and research overview

/aat/
  Algebraic Architecture Theory landing and chapter-cluster pages

/sft/
  Software Field Theory article / theory site

/archsig/
  ArchSig manual and reference

/interface/
  AAT -> SFT dependency and claim-boundary guide

/tooling/
  Tooling bridge and claim-boundary overview

/outreach/
  Hashnode, Zenn, Qiita, and other public article links
```

## Publishing Target

Initial target: GitHub Pages with a custom domain.

This directory currently uses a no-build static stack:

- `index.html`
- `assets/site.css`
- `assets/site.js`
- MathJax from a CDN for TeX rendering
- Google Fonts for the primary Latin serif, sans, and monospace faces

Until the site generator copies or renders repository documents into public
routes, the top page links to the canonical documents on GitHub.

## Design Notes

This is a text-first research site. Typography is the main interface:

- Long-form prose uses `Source Serif 4` with Japanese serif fallbacks.
- Navigation and compact labels use `Inter` with Japanese sans fallbacks.
- Code and Lean-like fragments use `IBM Plex Mono`.
- Math is rendered with MathJax CommonHTML.

Avoid adding a heavy frontend framework unless the site starts needing behavior
that plain HTML, CSS, and a small script cannot handle cleanly.
