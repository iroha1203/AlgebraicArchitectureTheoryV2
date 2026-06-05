# AAT Website Renewal Plan

この文書は、`website/aat/**` を Atom refoundation 後の AAT に合わせて再構成するための
作業計画である。目的は小幅な copy 修正ではなく、AAT website を現在の理論を読むための
web-native monograph として設計し直すことである。

複数セッションにまたがって作業しても意図が失われないように、中心思想、route、各ページの
責務、既存ページの扱い、claim boundary、検証手順をここに固定する。

## 結論

AAT website は、Atom refoundation を入口にした章構成へ更新する。

現行の `website/aat/**` は、selected presentation、`ArchitectureObject`,
`ArchitectureCore`, finite universe を基礎として読む旧い構成を多く残している。
これらは重要な素材だが、AAT の root ではない。

現在の AAT は次の順序で読む。

```text
Atom
  -> AtomAxiomSystem
  -> Molecule
  -> Architecture Object / AATCore
  -> DesignLaw
  -> ObstructionCircuit
  -> Zero Curvature / Flatness
  -> ArchitectureSignature
  -> Operations / Repair / Synthesis
  -> Dynamics / Geometry / Representations
```

したがって、AAT website は「選択された presentation から始まる解説」ではなく、
「primitive architectural facts から architecture algebra が立ち上がる解説」へ再設計する。

## Source of Truth

本文の primary source は次を使う。

- `docs/aat/mathematical_theory/README.md`
- `docs/aat/mathematical_theory/part_1_atoms_objects_laws.md`
- `docs/aat/mathematical_theory/part_2_flatness_calculus_geometry.md`
- `docs/aat/mathematical_theory/part_3_analytic_state_examples.md`
- `docs/aat/lean_theorem_index.md`
- `docs/aat/proof_obligations.md`
- `docs/sft/aat_interface.md`
- `docs/tool/**`
- `Formal/Arch/Atom/Foundation.lean`
- `Formal/Arch/AAT/**`
- `Formal/Arch/Observation/AtomPresentation.lean`
- `Formal/Arch/Observation/ArchMap.lean`
- `Formal/Arch/Signature/AATCoreBridge.lean`

`website/aat/**` は source of truth ではない。公開読書面である。
website 独自の theorem claim、tool correctness claim claim、
empirical claim は追加しない。

## Core Thesis

AAT website 全体は、次の読みを支える構成にする。

```text
AAT studies software architecture as an algebra of primitive architectural facts:
atoms assemble into molecules and architecture objects, laws evaluate those
configurations, obstruction circuits locate minimal failures, and signatures
record the resulting multi-axis reading.
```

公開本文では、AAT を Atom 公理系から立ち上がる純粋理論として読む。
Atom、molecule、law、obstruction circuit、zero curvature は、まず AAT 内部の
数学的対象として提示する。observation、tooling、ArchSig、SFT handoff に関する境界は、
純粋 AAT から外部の観測・分析・応用 layer へ接続する箇所で明示する。

## 既存ページの扱い

現行 AAT ページは素材として使うが、章構成は維持しない。

重要な制約として、リニューアルによって AAT website を痩せさせない。
現行ページはすでに web-native monograph として相当量の定義、命題、証明アイデア、
例、反例、Lean status、audit link を持っている。新構成ではそれらを短い概要へ圧縮せず、
Atom refoundation 後の理論順に再配置し、必要な箇所では増補する。各章は現行ページと
同等以上の密度、読書価値、検証可能性を持つことを完成条件とする。

- `website/aat/foundations/` は Atom 章へ作り替える。
- 旧 `foundations/` の selected presentation、`ArchitectureObject`,
  `ArchitectureCore`, `ComponentUniverse`, complete extraction boundary は、新しい
  `architecture-objects/` へ移す。
- `laws-and-witnesses/` は `laws/` と `obstruction-circuits/` へ分割する。
- `local-law-packages/` は `design-principle-layers/` へ改名または再位置付けする。
- `calculus-and-extensions/` は `operations-and-calculus/` へ発展させる。
- `repair-and-dynamics/` は `dynamics-and-geometry/` へ発展させる。
- `architecture-signature/`, `representations-and-effects/`,
  `canonical-examples-and-readings/`, `related-work/`, `status/`,
  `formal-anchors/` は route を維持してもよいが、Atom refoundation に合わせて
  冒頭、導線、anchor を更新する。

既存 HTML をそのまま移植しない。使う場合も、文単位で採用する前に source docs と Lean index に戻って確認する。

## 新しい全体構成

AAT website は、数学本文 `docs/aat/mathematical_theory/` の三部構成に合わせて、
3-part monograph として読む。

Part I は Atom から object と law が立ち上がるところを扱う。
Part II は flatness、zero curvature、signature、calculus、geometry を扱う。
Part III は graph / category / matrix / state-transition / effect などの computable
representation と例を扱う。

推奨 canonical route は次の通り。

```text
/aat/
  Overview

Part I. Atoms, Objects, and Laws
/aat/atoms/
  Atoms and Primitive Architectural Facts

/aat/architecture-objects/
  Molecules and Architecture Objects

/aat/laws/
  Design Laws and Invariants

/aat/obstruction-circuits/
  Obstruction Circuits

Part II. Flatness, Calculus, and Geometry
/aat/zero-curvature/
  Flatness and Zero Curvature

/aat/architecture-signature/
  Architecture Signature

/aat/design-principle-layers/
  Local and Global Law Packages

/aat/operations-and-calculus/
  Operations, Repair, and Synthesis

/aat/dynamics-and-geometry/
  Paths, Homotopy, and Diagram Filling

Part III. Representations, Effects, and Examples
/aat/representations-and-effects/
  Computable Representations and Effects

/aat/canonical-examples-and-readings/
  Examples, Counterexamples, and Readings

/aat/related-work/
  Related Work and Novelty

References
/aat/status/
  Lean Status

/aat/formal-anchors/
  Formal Anchors Audit
```

`docs/website/SITEMAP.md` が canonical route 管理である。
この計画書と `SITEMAP.md` が食い違う場合は、まず両者を同期する。

## Chapter Responsibilities

### `/aat/` Overview

目的:

- AAT section の入口。
- Atom から Signature / Operations / Dynamics までの読書順を見せる。
- AAT と SFT / ArchSig の関係を短く示す。

書くこと:

- AAT の一文定義。
- `Atom -> Molecule -> Law -> ObstructionCircuit -> Signature -> Operation` の流れ。
- 章インデックス。
- Formal Anchors と Status への導線。

書かないこと:

- 長い manifesto。
- Issue / proof obligation の詳細。
- theorem boundary の表を landing page に置くこと。

### `/aat/atoms/` Atoms and Primitive Architectural Facts

目的:

- AAT の root を定義する。
- Atom は observation、law、tool output、SFT event から生成されない primitive typed fact であることを説明する。

書くこと:

- `Atom`, `Axis`, `AtomKind`, `AtomPredicate`, `AtomAxiomSystem`。
- atom kind の代表例: component, relation, capability, state, effect, authority,
  contract, semantic, runtime interaction。
- `singleFact`, predicate preservation, boundary independence, law independence。
- taxonomy は open であり、global completeness claim ではないこと。
- `RawAtomCandidate`, `ObservedAtom`, `AtomObservationGap`, `AtomPresentation` の位置付け。

書かないこと:

- tool output を atom truth として扱うこと。
- missing observation を atom absence として扱うこと。
- Atom taxonomy の完全性を主張すること。

### `/aat/architecture-objects/` Molecules and Architecture Objects

目的:

- Atom から architecture object がどう構成されるかを説明する。
- 旧 Foundations の selected presentation / `ArchitectureCore` / `ComponentUniverse` を、Atom 後段の object presentation として再配置する。

書くこと:

- `Molecule` は finite configuration of already-existing atoms。
- role / pattern は primitive atom ではなく molecule interpretation。
- `ArchitectureObject` は atom configuration / molecule から読まれる構成対象。
- selected presentation、observation context、finite universe、coverage、exactness。
- complete extraction boundary。

書かないこと:

- selected presentation を AAT の root として扱うこと。
- `ComponentUniverse` を source-observation layer と同一視すること。

### `/aat/laws/` Design Laws and Invariants

目的:

- design principles を AAT の law と invariant family として読む。

書くこと:

- `DesignLaw` は molecule を評価する。
- law は atom existence を生成しない。
- `Lawful`, invariant family, preservation, reflection, improvement。
- SOLID、Layered / Clean Architecture、Event Sourcing / Saga / CRUD、
  Circuit Breaker / Replicated Log を law family / layer として整理する。

書かないこと:

- SOLID を universal principle として扱うこと。
- local contract success から global decomposability を結論すること。

### `/aat/obstruction-circuits/` Obstruction Circuits

目的:

- AAT の診断力を見せる中心章。
- law failure を smell ではなく law-relative minimal bad molecule として読む。

書くこと:

- `ObstructionCircuit = MinimalBadMolecule`。
- `FiniteMoleculeUniverse`。
- `LawfulnessBridge`。
- badness、minimality、coverage、exactness。
- minimal bad molecule が design review の読みをどう変えるか。

書かないこと:

- 任意の tool warning を obstruction circuit と呼ぶこと。
- minimality / selected universe なしに global failure を主張すること。

### `/aat/zero-curvature/` Flatness and Zero Curvature

目的:

- lawfulness、obstruction absence、flatness、zero curvature の関係をまとめる。

書くこと:

- `LawfulWithinMoleculeConfiguration`。
- `NoRequiredObstructionCircuit`。
- `ZeroCurvaturePackage`。
- selected law universe と required molecule configuration。
- zero curvature は selected theorem package に相対的であること。

書かないこと:

- zero score や tool pass を global lawfulness と読むこと。
- runtime / semantic / empirical conclusion を static package から出すこと。

### `/aat/architecture-signature/` Architecture Signature

目的:

- architecture を単一スコアではなく多軸診断として読む。

書くこと:

- Signature axis、required zero axis、measured axis、unmeasured axis。
- Atom `Axis` と report axis の関係と差異。
- ArchSig は Atom / AAT を生成せず、ArchMap + LawPolicy から law-relative reading を出す analysis layer。
- claim level、available evidence、non-conclusion。

書かないこと:

- Architecture Signature を quality score として扱うこと。
- ArchSig output を Lean theorem discharge として扱うこと。

### `/aat/design-principle-layers/` Local and Global Law Packages

目的:

- design principles を AAT の law package layers として分類する。

書くこと:

- SOLID は local contract layer。
- Layered / Clean Architecture は global structure layer。
- Event Sourcing / Saga / CRUD は state-transition algebra layer。
- Circuit Breaker / Replicated Log は runtime dependency / distributed convergence layer。
- local law package と global structure theorem の非含意。

書かないこと:

- layer 間の theorem を未証明のまま同一視すること。

### `/aat/operations-and-calculus/` Operations, Repair, and Synthesis

目的:

- 設計原則を、architecture invariant を保存・改善する操作として読む。

書くこと:

- `ArchitectureOperation`。
- preservation, improvement, strict repair。
- feature extension。
- operation-invariant correspondence。
- repair and synthesis package。

書かないこと:

- operation が all-axis monotonicity を保証すると読むこと。
- repair safety を証明なしに一般化すること。

### `/aat/dynamics-and-geometry/` Paths, Homotopy, and Diagram Filling

目的:

- AAT が static structure だけでなく architecture evolution の幾何を扱うことを示す。

書くこと:

- architecture path。
- signature trajectory。
- path homotopy。
- diagram filling。
- monodromy / continuation。
- repair trajectory と non-fillability。

書かないこと:

- selected trajectory disagreement から global semantic impossibility を無条件に結論すること。

### `/aat/representations-and-effects/` Computable Representations and Effects

目的:

- AAT の概念を graph、category、matrix、analytic representation、state-transition algebra で計算可能に読む。

書くこと:

- graph representation。
- `ComponentCategory` は thin category であり path count / walk length を忘れること。
- walk / path / adjacency matrix / nilpotence / spectral reading。
- state-transition algebra。
- effect law surface。

書かないこと:

- `Decomposable` に acyclicity、finite propagation、nilpotence、spectral condition を混ぜること。

### `/aat/canonical-examples-and-readings/` Examples, Counterexamples, and Readings

目的:

- 理論の使い方と境界を例で見せる。

書くこと:

- coupon feature extension。
- static flat but semantic obstruction。
- repair transfer counterexample。
- SOLID-style counterexamples。
- ArchMap / observation examples。
- Atom / molecule / law / circuit の小さな worked example。

書かないこと:

- counterexample を単なる caveat として末尾に押し込むこと。

### `/aat/related-work/` Related Work and Novelty

目的:

- AAT の位置付けを、既存の architecture description、ATAM、metrics、graph analysis、
  formal methods、category-theoretic models と比較する。

書くこと:

- AAT の新規性は Atom root、law-relative obstruction circuit、multi-axis signature、
  operation calculus の組み合わせであること。
- 既存手法を置き換えるのではなく、どの claim を theorem-shaped にするかを整理すること。

### `/aat/status/` Lean Status

目的:

- Lean status、proof obligations、empirical hypotheses を本文から分離して管理する。

書くこと:

- 最新 snapshot。
- `proved`, `defined only`, `future proof obligation`, `empirical hypothesis` の読み。
- Atom refoundation の current formal core。
- Formal Anchors への導線。

書かないこと:

- Status を AAT の読者向け主本文として膨らませること。

### `/aat/formal-anchors/` Formal Anchors Audit

目的:

- website claims と Lean declarations の対応を public audit として示す。

書くこと:

- Atom Axiom System / AATCore Refoundation。
- Molecule / Law / Circuit / ZeroCurvature。
- Observation / ArchMap boundary。
- Architecture Signature bridge。
- Operations / Repair / Synthesis。
- Dynamics / Representation / Examples。

書かないこと:

- Formal Anchors を landing page や概念導入の代わりにすること。

## Quality Bar

AAT renewal は simplification project ではない。reader-facing quality bar は現行 AAT
website と同等以上に置く。

各 chapter は原則として次を持つ。

- 章の research question。
- AAT 内部の中心定義。
- 対応する Lean 名または theorem-index anchor。
- theorem-shaped statement または proposition。
- proof idea または formal reading。
- small example。
- counterexample または non-conclusion。
- 次章へ進む読書導線。

避けること:

- 既存の豊かな章を短い glossary page に縮退させること。
- Atom refoundation を理由に、旧ページの selected presentation、finite universe、
  law package、signature、calculus、repair、representation の内容を落とすこと。
- route skeleton だけを作り、本文密度が追いつかない状態を完成扱いにすること。
- status / formal anchors へ説明を逃がし、本文で概念が読めない構成にすること。

各リニューアル PR では、削除した段落がどの新章へ移ったか、またはなぜ不要になったかを確認する。
不要と判断する場合も、理論の古さ、重複、claim boundary の不一致など理由を明確にする。

## Migration Strategy

移行は blue/green 方式で行う。既存の `website/aat/**` は公開中の安定版として残し、
新版は `website/aat2/**` 配下に作成する。`aat2` が本文密度、リンク、navigation、
Formal Anchors、Status、Playwright 確認まで完了してから、最後に canonical path を
`/aat/` へ切り替える。

移行中の原則:

- `website/aat/**` は完成済み公開面として壊さない。
- `website/aat2/**` は renewal draft / preview surface として作る。
- `website/sitemap.xml` は切り替え完了まで原則として既存 `/aat/` を canonical とする。
- `docs/website/SITEMAP.md` には、移行中 route と最終 canonical route の対応を明記する。
- `aat2` から公開導線を張る場合は、preview / renewal draft であることを内部導線上で明確にする。
- 全章が Quality Bar を満たすまで、`aat2` を `/aat/` に昇格しない。

### Phase 1: AAT2 Information Architecture

- `website/aat2/` を作成する。
- `docs/website/SITEMAP.md` に `/aat2/` preview routes と最終 `/aat/` canonical routes の対応を追加する。
- `website/aat2/index.html` の chapter index を新構成で作る。
- `aat2` 配下の sidebar、next / previous navigation、relative asset path の方針を固定する。
- 既存 `website/aat/**` の内部リンクはこの段階では変更しない。

### Phase 2: AAT2 Atom Foundation

- `website/aat2/atoms/index.html` を作る。
- 既存 `website/aat/foundations/` は残す。
- 旧 `foundations/` から移すべき内容と、新 Atom chapter に新規追加する内容を対応付ける。
- Atom / observation / ArchMap の boundary を最初に確定する。

### Phase 3: AAT2 Object and Law Core

- `website/aat2/architecture-objects/`, `website/aat2/laws/`,
  `website/aat2/obstruction-circuits/`, `website/aat2/zero-curvature/` を作る。
- 旧 `foundations/` と `laws-and-witnesses/` の有用な内容を再配置する。
- Molecule / DesignLaw / ObstructionCircuit / LawfulnessBridge の流れを本文で固定する。

### Phase 4: AAT2 Signature and Calculus

- `website/aat2/architecture-signature/` を Atom axis / measured axis / ArchSig boundary に合わせて作る。
- `website/aat2/design-principle-layers/`, `website/aat2/operations-and-calculus/` を整備する。
- 既存 `website/aat/local-law-packages/`, `website/aat/calculus-and-extensions/` は残し、
  `aat2` 側で新 route 名と本文構成を確定する。

### Phase 5: AAT2 Dynamics, Representations, Examples

- `website/aat2/dynamics-and-geometry/` を作る。
- `website/aat2/representations-and-effects/` を computable readings として作る。
- `website/aat2/canonical-examples-and-readings/` を Atom / molecule / law / circuit の
  worked examples と counterexamples の章として強化する。

### Phase 6: AAT2 Formal Anchors and Status

- `website/aat2/status/` を最新 snapshot と Atom refoundation core に合わせて作る。
- `website/aat2/formal-anchors/` に Atom / AATCore refoundation anchor を追加し、
  旧 foundations anchor を architecture objects 側へ移す。
- commit-pinned GitHub links を更新する。

### Phase 7: Cutover

- `aat2` の全 route を local server と Playwright で確認する。
- `aat2` の全章が Quality Bar を満たすことを確認する。
- `website/sitemap.xml` を `/aat2/` ではなく最終 `/aat/` canonical route へ更新する。
- 旧 `website/aat/**` を破棄し、完成した `website/aat2/**` を `website/aat/**` に改名する。
- 内部リンク、breadcrumb、sidebar、next / previous navigation、canonical / OGP URL を `/aat/` に切り替える。
- 切り替え後に旧 `/aat2/` route を残すか削除するかを決め、残す場合は noindex / preview 扱いにする。

## Cutover Policy

最終移行では、旧 `website/aat/**` を破棄し、完成した `website/aat2/**` を
`website/aat/**` に改名する。旧 route 互換のために内容を legacy path へ寄せることはしない。

cutover の判断基準:

- `aat2` の全章が Quality Bar を満たしている。
- `aat2` の全 route、sidebar、breadcrumb、next / previous navigation が完成している。
- `aat2` の Formal Anchors と Status が Atom refoundation 後の Lean surface に対応している。
- `aat2` 内部リンクが最終 `/aat/` path へ機械的に置換可能である。
- `website/sitemap.xml`、canonical URL、OGP URL、内部導線を最終 `/aat/` に切り替えられる。
- 切り替え PR では、旧 `website/aat/**` の削除と `website/aat2/**` から
  `website/aat/**` への移動を主変更にし、本文 rewrite を混ぜない。

## Writing Rules

- 公開本文は英語で書く。
- AAT を metrics catalog や tool manual にしない。
- AAT を SOLID の形式化として狭く見せない。
- AAT を graph analysis だけに還元しない。
- `does not claim` から章を始めない。
- ただし non-conclusion は各章の末尾、Status、Formal Anchors に置く。
- Atom / observation / law / tooling / SFT の boundary を混同しない。
- `Architecture Signature` は単一スコアではなく multi-axis diagnostic として書く。
- Lean status は `proved`, `defined only`, `future proof obligation`, `empirical hypothesis` を使う。
- website 独自の theorem claim を置かない。

## Validation

AAT website 変更では、少なくとも次を確認する。

```bash
git diff --check
rg -n "[\u200B-\u200F\u202A-\u202E\u2066-\u2069]" docs/website website/aat
rg -n "\b(axiom|admit|sorry|unsafe)\b" Formal docs
```

`aat2` 作成中は scan 対象に `website/aat2` も含める。

website HTML / route / asset path を変更した場合は、local server と Playwright で確認する。
Codex から Playwright を起動する場合は、macOS のブラウザ起動権限により sandbox 外実行を使う。

```bash
python3 -m http.server 0 --directory website
playwright --version
```

確認すること:

- added / renamed route が開ける。
- sidebar と next / previous navigation が新構成と一致する。
- relative asset path が壊れていない。
- `website/sitemap.xml` と `docs/website/SITEMAP.md` が一致する。
- commit-pinned GitHub links が存在する。
- mobile / desktop で本文、sidebar、table、code block が破綻しない。

docs-only の計画書変更では、`git diff --check` と hidden / bidi Unicode scan を最低限確認する。
