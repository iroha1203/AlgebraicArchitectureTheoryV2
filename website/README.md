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

## Content Policy

AAT and SFT pages are first-class theory pages, not promotional summaries.
They should stay faithful to the repository's canonical theory documents and
use a precise, paper-like expository style. Public article platforms such as
Zenn, Hashnode, and Qiita are outreach surfaces for motivation and intuition;
they are not where the full theory, theorem boundaries, or claim discipline are
maintained.

The AAT section should be treated as a web-native preprint / monograph surface:
the place where the theory can be published carefully before a slower
arXiv-style paper is prepared. Its purpose is to give readers a complete,
accurate, and stable account of the theory, including definitions, assumptions,
theorem patterns, examples, counterexamples, Lean status, and non-conclusions.

When expanding AAT and SFT pages:

- Treat `docs/aat/mathematical_theory.md` and
  `docs/sft/software_field_theory.md` as the source texts.
- Preserve definitions, assumptions, non-conclusions, and claim levels.
- Prefer theorem-style structure: definitions, interpretation, examples,
  boundaries, and links to Lean status where appropriate.
- Keep AAT pages strong enough to stand alone as web theory sections, not only
  as summaries of the repository documents.
- Record an AAT release snapshot on public theory pages: last updated date,
  source commit, and Lean status snapshot. Links from theory pages to canonical
  docs should use commit-pinned GitHub URLs for public releases, not
  `blob/main`, so the website and cited source text do not drift silently.
- Do not compress formal distinctions into slogans or general software advice.
- Keep ArchSig and tooling evidence separate from AAT / SFT theorem claims.
- For ArchSig pages, separate the Core, Review, SFT, and Operational product
  surfaces from remaining research, calibration, and adapter gaps.

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
`aat/`. The AAT / SFT interface is implemented as `interface/`. SFT Part pages
are implemented as static directory routes under `sft/`. ArchSig manual and
reference pages are implemented as static directory routes under `archsig/`.
Profile and outreach pages are implemented as top-level static directory
routes.

## SEO Sitemap Policy

Do not commit a production `sitemap.xml` until the public domain or GitHub
Pages base URL is fixed. Once the domain is chosen, generate or manually add
`website/sitemap.xml` from the routes in `website/SITEMAP.md`, using the final
public root as the URL base. Until then, avoid placeholder hosts in metadata,
links, and sitemap entries.

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

AAT and SFT prose should read like long-form research exposition. The target is
a technically careful reader who needs the actual theory, not a short popular
explanation. Outreach pages can be lighter; canonical AAT / SFT pages should be
substantive enough to stand on their own while still linking back to the source
documents.

Avoid adding a heavy frontend framework unless the site starts needing behavior
that plain HTML, CSS, and a small script cannot handle cleanly.
