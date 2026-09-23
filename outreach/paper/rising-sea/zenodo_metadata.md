# Zenodo deposit metadata

> 2026-09-23 に publish 済み。record: https://zenodo.org/records/22913489
> description の正本は `en/main.tex` の abstract(`en/01-abstract.tex`)であり、
> 本文 abstract を変更したら下記変種を同期する。

## 1. Deposit metadata

| Field | Value |
| --- | --- |
| Resource type | Publication / Preprint |
| Title | Foundations of Algebraic Architecture Theory: A Rising Sea of Geometry, Transport, Comparison, and Reconstruction |
| Creators | Nakahata, Hiroyuki(Independent Researcher、ORCID 0009-0008-5928-0234) |
| Publication date | 2026-09-23 |
| Language | English |
| Version | 1.0.0 |
| License | CC BY 4.0(2026-09-23 確定。単一レコード全体 — PDF・tex/bib source — に適用) |
| DOI | version DOI `10.5281/zenodo.22913489`、concept DOI `10.5281/zenodo.22913488`(title page への印字はしない — 2026-09-23 著者裁定) |
| Related identifiers | 未設定(repository・固定版への参照は PDF の付録Bが担う) |
| Keywords | software architecture; algebraic geometry; algebraic architecture theory(deposit 時に3語へ絞った) |

Notes: AI 協働開示は論文本体の付録Cが正本(metadata の追加開示は不要)。

**Upload 規律(SAGA 2026-07-27 教訓)**: Zenodo はディレクトリ構造を持たないため、
deposit へは **`paper.py package` が生成する zip 単一アーカイブ+閲覧用の standalone
`main.pdf` の2ファイルだけ**を upload する。publish 前の preview では
**file 数と file 一覧を zip の記録と突合**する。

## 2. Description(Zenodo 用 abstract 変種)

Zenodo description は HTML whitelist のみ(MathJax 不可)。数式は Unicode inline 形。
`en/arxiv-abstract.txt` から機械的に変換した4段落。

```html
<p>AI-generated software changes make it increasingly important to determine what a change preserves, where local consistency fails to extend globally, and which alternatives remain. We develop the foundations of Algebraic Architecture Theory (AAT) from Atoms, typed primitive facts, and Laws, equations that objects must satisfy. A reading specifies what counts as structure and which operations and laws to preserve.</p>
<p>The main reconstruction theorem identifies the category of full geometries and all their structure-preserving morphisms with an independently defined category of local models, up to equivalence. Objects are recovered up to isomorphism and morphisms between fixed endpoints uniquely.</p>
<p>The theory addresses gluing, diagnosis, transport, classification of changes, and reconstruction. From finite Atom families we construct cores closed under operations and geometries with sites and coefficients. We give conditions under which a Čech obstruction detects the existence of a global state and, through comparison with repair semantics, a global repair. We compare diagnoses and give a finite criterion for uniform invariance given computable finite data. Transport along exact changes has a universal property and commutes with base change on exact pointed pullback squares. Comparisons of routes generated from the same square, finite comparison diagram, and geometry factor into an invertible comparison and an idempotent normalization. We characterize when observations determine comparison preservation and classify compatible lifts.</p>
<p>Encodings of lens and protocol semantics preserve and reflect laws and recover semantics-preserving morphisms. Applications classify and count operation-preserving changes and extend morphisms uniquely from finite tables. Corresponding Lean declarations are listed in the appendix.</p>
```

## 3. Citation guide(concept DOI / version DOI)

- **Concept DOI**: 全 version を束ねる DOI。常に最新 version へ解決される。
- **Version DOI**: v1.0.0 に固定される DOI。再現性の文脈ではこちらを引用する。

- version DOI(v1.0.0): `10.5281/zenodo.22913489`
- concept DOI: `10.5281/zenodo.22913488`

PDF へは印字しない(2026-09-23 著者裁定)。
