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

/outreach/
  Hashnode, Zenn, Qiita, and other public article links
```

## Publishing Target

Initial target: GitHub Pages, deployed from the `website/` directory by the
`Website Pages` GitHub Actions workflow.

Repository settings should use GitHub Actions as the Pages source. The workflow
uploads `website/` as the Pages artifact and deploys it to the `github-pages`
environment on pushes to `main` that change `website/**` or the workflow file.
It can also be run manually with `workflow_dispatch`.

A custom domain can be added later by committing `website/CNAME` after the DNS
target is chosen. Until then, do not hard-code the final public host in site
links or metadata.

This directory currently uses a no-build static stack:

- `index.html`
- `assets/site.css`
- `assets/site.js`
- MathJax from a CDN for TeX rendering
- Google Fonts for the primary Latin serif, sans, and monospace faces

The committed `website/.nojekyll` file keeps GitHub Pages from treating
underscore-prefixed paths or future generated assets as Jekyll input.

AAT chapter-cluster pages are implemented as static directory routes under
`aat/`. SFT Part pages are implemented as static directory routes under
`sft/`. Remaining major sections still point readers back to canonical
repository documents until their public routes are added.

## Local Preview

From the repository root:

```bash
python3 -m http.server 8000 --directory website
```

Then open `http://localhost:8000/`.

Directly opening `website/index.html` also works for the current top page, but
the local server is closer to the GitHub Pages serving model and should be used
when directory routes are added.

## Path Rules

- Use relative asset paths such as `assets/site.css` and `assets/site.js`.
- Avoid root-absolute paths such as `/assets/site.css`; project Pages sites may
  be served below a repository path.
- Use directory routes with local `index.html` files for public pages.
- Link repository source documents with absolute GitHub URLs until those
  documents are rendered into `website/`.
- Keep canonical public pages in English. Japanese explanations belong in
  outreach articles that link back to the canonical site.

## Design Notes

This is a text-first research site. Typography is the main interface:

- Long-form prose uses `Source Serif 4` with Japanese serif fallbacks.
- Navigation and compact labels use `Inter` with Japanese sans fallbacks.
- Code and Lean-like fragments use `IBM Plex Mono`.
- Math is rendered with MathJax CommonHTML.

Avoid adding a heavy frontend framework unless the site starts needing behavior
that plain HTML, CSS, and a small script cannot handle cleanly.
