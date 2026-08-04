# Zenodo deposit metadata(ドラフト)

> release identity(tag / DOI)確定時に `TBD` を埋めて deposit フォームへ転記する。
> abstract の platform 変種の正本はこのファイル(LaTeX 正本 = `en/main.tex` の
> `\begin{abstract}` から機械的に変換。本文 abstract を変更したら両変種を同期する)。

## 1. Deposit metadata

| Field | Value |
| --- | --- |
| Resource type | Publication / Preprint |
| Title | SAGA: A Comparison Theorem for Local-to-Global Software Architecture — From Semantic Repair Cohomology to Algebraic-Geometric Descent |
| Creators | Nakahata, Hiroyuki(Independent Researcher、ORCID 0009-0008-5928-0234) |
| Publication date | TBD(release 日) |
| Language | English |
| Version | 1.0.0 |
| License | **CC BY 4.0**(2026-07-26 決定。単一レコード全体 — PDF・tex/bib source・証拠束 — に適用。PDF 本体への license 表記は任意だが、release 時に title page 脚注へ「CC BY 4.0」を一行入れると deposit と自己記述が一致する) |
| DOI | **version DOI 予約済み(2026-07-26): `10.5281/zenodo.21603762`**。title page・§6・付録C.4・CITATION.md へ印字済み。concept DOI は publish 時に自動付与されるため bundle 内には書かず「Zenodo record ページ参照」とする |
| Related identifiers | `https://github.com/iroha1203/AlgebraicArchitectureTheoryV2`(isSupplementTo / release tag TBD を付す)、FudanSELab/train-ticket commit `313886e99bef`(isDerivedFrom、対象 case study) |
| Keywords | software architecture; Čech cohomology; algebraic geometry; sheaf; descent; Lean; formal verification; microservices; architecture analysis |

Notes: AI 協働開示は論文本体の Acknowledgments が正本(metadata の追加開示は不要)。

**Upload 規律(2026-07-27 教訓の成文化)**: Zenodo はディレクトリ構造を持たないため、
deposit へは **`build_bundle.py` が生成する zip 単一アーカイブ+閲覧用の standalone
`main.pdf` の2ファイルだけ**を upload する。bundle ツリーをそのまま upload すると
flat 化で同名ファイル(`out/head/` vs `out/repaired/` の13対)が衝突し、片方が
黙って欠落する(v1.0.0 初版で実際に発生。New version で修復)。publish 前の
preview では **file 数と file 一覧を bundle と突合**する。

## 2. Description(Zenodo 用 abstract 変種)

Zenodo description は HTML whitelist のみ(MathJax 不可)。数式は Unicode inline 形。

```html
<p>In a software architecture, each individual service can obey its own conventions and each handoff between adjacent services can hold, and yet a semantic inconsistency may remain that appears only on a full traversal of the system. This paper independently constructs two cohomologies that measure this gap between local correctness and global correctness, and proves that they agree. The first construction speaks the language of <em>repair</em>: from the semantic repair options admitted in each local context and their equivalence relation, it generates the coefficient M_sem. The second speaks the language of <em>equations</em>: it organizes the constraints of the architecture as a simultaneous equation system and generates the quotient coefficient Q_E by its obstruction ideal. Over a selected finite cover 𝒰 in Algebraic Architecture Theory (AAT) — the theory that constructs software architecture as algebraic geometry — and under finitely many selection conditions matching the local data, the comparison map induces an isomorphism H¹_sem(𝒰) ≅ Ȟ¹(𝒰, Q_E) together with a correspondence of residual classes. We call this the SAGA comparison theorem. The obstruction measured in the language of repair and the obstruction measured in the language of equations are the same cohomology class, so semantic diagnosis and geometric computation translate into each other in both directions. Moreover, when the family of repair states satisfies the sheaf condition, the existence of a global repair is equivalent to the vanishing of the obstruction class on both sides: Nonempty P_sem(W) ⟺ [r_sem] = 0 ⟺ [r_E] = 0.</p>
<p>The paper presents this result in three layers: the mathematical proof of the comparison theorem (Sections 3–5); the Lean formalization status at release time (Section 6); and a diagnosis in which the measurement tool ArchSig, on a real open-source microservice system, reproducibly walks the full circle from measuring a nonzero obstruction to its disappearance after repair (Section 7). The three layers refer to the same release identity, and each claim is connected to primary evidence. This yields, for whole-loop inconsistencies that per-service verification cannot capture, a connected diagnostic path of proved mathematics, machine-checked status, and reproducible measurement.</p>
```

## 3. arXiv 用 abstract 変種(併用時)

arXiv abstract は inline `$...$` のみ(標準 LaTeX / AMS マクロ限定、自作マクロ不可)。

```text
In a software architecture, each individual service can obey its own conventions and each handoff between adjacent services can hold, and yet a semantic inconsistency may remain that appears only on a full traversal of the system. This paper independently constructs two cohomologies that measure this gap between local correctness and global correctness, and proves that they agree. The first construction speaks the language of repair: from the semantic repair options admitted in each local context and their equivalence relation, it generates the coefficient $M_{\mathrm{sem}}$. The second speaks the language of equations: it organizes the constraints of the architecture as a simultaneous equation system and generates the quotient coefficient $Q_E$ by its obstruction ideal. Over a selected finite cover $\mathcal{U}$ in Algebraic Architecture Theory (AAT) --- the theory that constructs software architecture as algebraic geometry --- and under finitely many selection conditions matching the local data, the comparison map induces an isomorphism $H^1_{\mathrm{sem}}(\mathcal{U}) \cong \check{H}^1(\mathcal{U}, Q_E)$ together with a correspondence of residual classes. We call this the SAGA comparison theorem. The obstruction measured in the language of repair and the obstruction measured in the language of equations are the same cohomology class, so semantic diagnosis and geometric computation translate into each other in both directions. Moreover, when the family of repair states satisfies the sheaf condition, the existence of a global repair is equivalent to the vanishing of the obstruction class on both sides. The paper presents this result in three layers: the mathematical proof of the comparison theorem; the Lean formalization status at release time; and a diagnosis in which the measurement tool ArchSig, on a real open-source microservice system, reproducibly walks the full circle from measuring a nonzero obstruction to its disappearance after repair. The three layers refer to the same release identity, and each claim is connected to primary evidence.
```

## 4. Citation guide(concept DOI / version DOI)

Zenodo は record ごとに2種類の DOI を発行する。

- **Concept DOI**: 全 version を束ねる DOI。常に最新 version へ解決される。
  「SAGA 論文(最新版)」を指したい引用はこちら。**publish 時に自動付与**され、
  それまで番号は不明 — bundle 内の文書には書かず、Zenodo record ページを参照先とする。
- **Version DOI**: 各 version(v1.0.0 等)に固定される DOI。
  再現性の文脈(この証拠束・この Lean status を検証した)ではこちらを引用する。
  draft の「Get a DOI now」で **publish 前に予約**し、PDF と本 guide へ転記する。

推奨引用形(TBD を確定値で置換):

```text
Nakahata, H. (2026). SAGA: A Comparison Theorem for Local-to-Global
Software Architecture. Zenodo. https://doi.org/TBD(version DOI)
```

形式化の深化(v1.1 / v2.0)に追随する場合は concept DOI を、
本 release の検証結果を参照する場合は version DOI を用いる。
