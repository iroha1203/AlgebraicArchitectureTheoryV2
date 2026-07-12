# PRD: AAT Lean Standard Architecture Scheme Core

- 作成: 2026-07-12
- 対象: `Formal/AG/LawAlgebra`のaffine chart・scheme・decoration層、examples、aggregate、statement contracts、axiom audit、Lean台帳
- 数学的正典: `docs/aat/algebraic_geometric_theory/` 第III部 定義8.1〜10.3、Appendix A.4〜A.5
- 品質基準: `AGENTS.md`、`docs/guideline.md`、`docs/aat/guideline.md`、`docs/aat/lean_quality_standard.md`
- tracking Issue: 未作成。Issue作成と依存登録が済むまで実行不可
- executable contract: `Formal/AG/StatementContractsStandardArchitectureScheme.lean`。実装と同時に作成し、CIでelaborateする
- 実行単位: GitHub tracking Issue配下の `1 Issue = 1 PR`

## 実行開始条件

- tracking Issueが作成され、対象main commit、target一覧、material premise表、子Issue依存が登録されている。
- 同Issueが、同一AAT site上のcommutative-ring-valued structure sheaf、raw-to-sheafified canonical map、
  section-ring APIを提供するmerged宣言へのdependencyを持つ。

いずれかが欠ける間、このPRDは実行しない。

## Statement Design

この節は本PRDの設計入力であり、実装開始後にtargetの仮定・結論・量化対象を変更しない。
実装状態は記録しない。実装後は
`Formal/AG/StatementContractsStandardArchitectureScheme.lean`が実装宣言の型を直接検査する。
別のMarkdown contractは作成しない。

### SD1 — decorationとaffine chart

`AATDecoration (X : AlgebraicGeometry.Scheme)`はAtom label、selected law reading、signature、
interpretationの追加dataだけを持つ。`restrict`、`restrict_id`、`restrict_comp`を固定targetとし、
open immersion、affineness、coverage、overlap、cocycle、law-generated idealをfieldにしない。

```lean
structure DecoratedAffineScheme (k : Type) [CommRing k] where
  algebra : CommAlgCat k
  underlying : AlgebraicGeometry.Scheme
  specIso : underlying ≅ AlgebraicGeometry.Spec.obj
    (CategoryTheory.op algebra.toCommRingCat)
  decoration : AATDecoration underlying

structure ArchitectureAffineChart
    (X : AlgebraicGeometry.Scheme) (D : AATDecoration X)
    (k : Type) [CommRing k] where
  domain : DecoratedAffineScheme k
  map : domain.underlying ⟶ X
```

`IsArchitectureAffineChart`を`IsOpenImmersion map`とdecoration restriction equalityの
conjunctionとして別定義する。chart dataと成立proofを分離し、constructorとreference modelが
このpredicateを放電する。

`DecoratedAffineScheme.ofSpec`、`isAffine`、`toLocallyRingedSpace`を固定する。
legacy変換はactual `Spec` comparisonとdecoration一致を入力する場合だけ許す。

### SD2 — affine atlasとactual overlap

```lean
structure ArchitectureAffineAtlas
    (X : AlgebraicGeometry.Scheme) (D : AATDecoration X)
    (k : Type) [CommRing k] where
  Index : Type
  chart : Index → ArchitectureAffineChart X D k
```

pair overlapはatlasの選択fieldにせずactual pullbackまたはopen intersectionから定義する。
`IsArchitectureAffineAtlas`を全chartの`IsArchitectureAffineChart`とMathlibのactual joint-cover predicateの
conjunctionとして別定義する。standard coreはatlas dataとこのproofを保持するが、主constructorと
reference modelはprimitive chart dataからproofを放電し、field射影だけの完成定理を置かない。
`overlap`、左右のmap、その`IsOpenImmersion`、`overlap_commutes`、
`triple_overlap_cocycle`、`decoration_overlap`を固定targetとする。
`jointlyCovers`はMathlib predicateを直接使用し、自由な`Prop` labelへ置換しない。

### SD3 — standard architecture scheme core

```lean
structure StandardArchitectureScheme (k : Type) [CommRing k] where
  underlying : AlgebraicGeometry.Scheme
  decoration : AATDecoration underlying
  atlas : ArchitectureAffineAtlas underlying decoration k
  atlasValid : IsArchitectureAffineAtlas atlas
```

underlyingを`LocallyRingedSpace`へ弱めない。ringed AAT siteとのchart comparisonは、
context、section-ring isomorphism、overlap restrictionとのactual morphism equalityを持つ
`ArchitectureChartPresentation`として型付けし、自由なcompatibility propositionにしない。

### SD4 — decorated morphismとforgetful functor

`StandardArchitectureScheme.Hom X Y`はunderlying scheme morphismと、固定されたdecoration componentを
保存する具体predicateを持つ。`Hom.id`、`Hom.comp`、`Hom.ext`、category instance、
`forget : StandardArchitectureScheme k ⟶ AlgebraicGeometry.Scheme`、
`forget_faithful`を固定targetとする。同じcomparison mapを重複dataとしてHomに持たせない。

### SD5 — constructors、example、representability

`singleAffine`とunderlying comparison、二chart・非空overlap・非identity restriction・joint coverageを
証明する`twoChartReferenceModel`一式を固定する。

```lean
def sheafifiedChartRepresentability
    (P : SheafifiedChartPresentation k raw sheafified)
    (R : Type) [CommRing R] [Algebra k R] :
    hWU k raw R ≃ hWU k sheafified R
```

このequivalenceは`P.comparison`とその逆を使う。`apply`、`symm_apply`、`natural`と、
identityではないcomparisonを使うreference theoremを固定し、定義的に同一な型の`Equiv.refl`で閉じない。

## 問い

通常のMathlib `Scheme`をunderlying geometryとして保ち、そのaffine open coverに
AAT decorationを載せた`ArchitectureScheme`を、actual morphismとcompatibility theoremで構成できるか。

```text
standard Scheme X
  + affine open cover {U_i -> X}
  + U_i ≅ Spec A_i
  + typed AAT decoration D_i
  + overlap restriction and cocycle
  = standard ArchitectureScheme core
```

このPRDは、AAT固有のScheme類似物を作るものではない。
AAT decorationを忘れたときMathlib `Scheme`とそのaffine atlasがそのまま残り、
後続のlaw geometry、cohomology、deformationが標準scheme APIを利用できる基盤を作る。

## 現状診断

- `SpecAAT`は`PrimeSpectrum`、obstruction ideal、selected decorationを保持する。
- `AffineAATChart`はselected algebraと`SpecAAT`を結ぶが、chart自身はMathlib `Scheme`を第一級fieldとして持たない。
- `affineChartMathlibSpecLocallyRingedSpace`はchart algebraをMathlib `Spec.toLocallyRingedSpace`へ接続する。
- `ChartCompatibility`のopen immersion、overlap representability、restriction、ideal、decoration、cocycle、locally ringed conditionは自由な`Prop` slotである。
- `ArchitectureScheme`はpairwise `ChartCompatibility`を格納するが、各conditionの成立証明、joint coverage、actual overlap scheme、actual cocycleを要求しない。
- underlying objectは`LocallyRingedSpace`であり、actual Mathlib `Scheme`とaffine atlasを必須にしない。
- `singleAffineSpec`は単一chartのidentity surfaceとして有用だが、一般atlas gluingの証拠ではない。
- `sheafifiedChartRepresentability`はpresentation引数を使わない`Equiv.refl`であり、sheafified chart comparisonを証明していない。

既存のraw quotient representabilityとMathlib `Spec` bridgeは再利用する。
新coreはactual `Scheme`を先に持ち、その上のaffine open coverとdecorationを表す。
chart dataだけから一般schemeを構成するgluing theoremは、基礎型の成立後に独立した要求として扱う。

## アウトカム

完了時に次が成り立つ。

1. underlying objectがactual Mathlib `Scheme`であり、global AAT decorationを持つstandard architecture scheme coreがある。
2. affine chartはactual affine scheme、chart-to-underlying morphism、open immersion proofを持つ。
3. chart familyがunderlying topological spaceをjointly coverすることをactual predicateで証明する。
4. pair overlapはunderlying schemeのpullbackまたはopen intersectionとして構成され、左右のchart mapと一致する。
5. chosen affine atlasはglobal decorationのlocal presentationであり、chart restriction、pair overlap、triple overlapで整合する。
6. AAT decorationを忘れるfaithfulなforgetful functorがある。
7. single-affine constructorと、二chart・非空overlapを持つ非退化exampleがある。
8. raw/sheafified chart representabilityがactual algebra comparisonまたはnatural isomorphismを使う。
9. legacy `ArchitectureScheme`は新coreの完了証拠として使われず、必要な証明を伴う場合だけ移行できる。

## 採否規律

- 数学本文はread-onlyとし、`docs/aat/algebraic_geometric_theory/**`を変更しない。
- underlying geometryにはMathlib `AlgebraicGeometry.Scheme`を使う。
- `LocallyRingedSpace`だけを持つpackageをstandard architecture schemeの完了証拠にしない。
- actual morphism、open immersion、joint coverage、overlap、cocycleを自由な`Prop` labelで代用しない。
- dataとpropertyを分離し、propertyは既存Mathlib predicateまたは具体的なAAT compatibility predicateとして定義する。
- schemeをchart gluingから構成するAPIが不足していても、set-level gluingやstored `LocallyRingedSpace`へ弱めない。
- 新coreはstandard Schemeを先に受け取り、その上のatlasを証明する形式から開始してよい。
- target statementと参照definitionは、このPRDの`Statement Design`節を不変入力とする。

## 改修要求

### R0 — 現行surface・Mathlib API・fixed statementの確定

- tracking Issueに対象main commitを固定する。
- `SpecAAT`、`AffineAATChart`、`ChartCompatibility`、`ArchitectureScheme`、
  `singleAffineSpec`、raw/sheafified representabilityのsignatureと利用箇所を棚卸しする。
- Mathlibの`Scheme`、`Spec`、`IsAffine`、`IsOpenImmersion`、open cover、fiber product、
  affine open、restriction APIの利用可能範囲を確認する。
- material premiseを本文由来、放電済み、未放電へ分類する。

### R1 — global AAT decorationの独立定義

- standard scheme`X`上のglobal AAT decorationを小さいdataとして定義する。
- 最低限、typed coordinate labels、selected Atom reading、selected law reading、signature reading、
  interpretation mapを表現できるようにする。
- obstruction idealとlawful closed geometryは保持しない。後続のlaw geometryがselected law readingから生成する。
- decorationにはopen immersion、coverage、representability、cocycleなどのscheme propertyを混ぜない。
- open subschemeへのrestrictionを定義し、identityとcompositionを証明する。
- scheme morphismに沿うdecoration preservationは、underlying morphismと固定されたdecoration restrictionから
  決まるcomponent mapが満たすPropとして定義する。morphismへ追加のcomparison map dataを持たせない。
- identity、composition、extensionalityを証明し、後続でdecorated morphism categoryへ育てられるAPIにする。

### R2 — decorated affine scheme

- coefficient algebra`A`とactual Mathlib `Spec A`を持つdecorated affine schemeを導入する。
- underlying affine scheme、underlying locally ringed space、point spaceへのforgetful APIを用意する。
- `SpecAAT` / `AffineAATChart`から、underlying `Spec`とdecorationの一致を証明できる場合のconstructorを提供する。
- raw configuration representabilityは現行quotient universal propertyを再利用する。
- chart algebra、scheme global sections、selected presentationのcomparison mapを明示する。

### R3 — sheafified representabilityの実質化

- `SheafifiedChartPresentation`を使う主定理は、その`comparison`をproof bodyで実際に使用する。
- raw/sheafified algebra isomorphism、represented functor間のnatural isomorphism、
  またはselected localizationでのpresentation preservationのいずれかを構成する。
- generator/relationの保存が必要なstatementでは、具体的なmap、surjectivity、kernel equality、
  quotient comparisonとして定式化する。
- `Equiv.refl`だけでselected presentationを消費しない。
- identity caseとは異なる少なくとも一つの有限またはlocalization exampleを証明する。

### R4 — affine chart on a standard Scheme

- underlying scheme`X`、affine scheme`U_i`、chart morphism`U_i ⟶ X`、
  `IsOpenImmersion`、`IsAffine U_i`、decorated affine schemeとのcomparisonを持つchart dataを導入する。
- 可能な限りMathlib `Scheme.AffineOpenCover`をactual atlas dataとして利用し、
  open immersionとjoint coverageのduplicate fieldを再発明しない。
- 各chartのlocal decorationがglobal decorationのrestrictionであることをactual equalityまたはtyped isoで証明する。
- 各chartにorigin context`W_i`を与え、ringed AAT siteのsection algebra`O_X^U(W_i)`と
  chart coordinate ringのactual ring isomorphismを構成する。
- section-ring comparisonがpair overlapのrestriction mapと可換であることを証明する。
- chart imageをunderlying topological space上のopen setとして読むAPIを用意する。
- chart restrictionとopen immersion compositionをMathlib APIへ接続する。
- conclusion-shaped compatibilityをfieldへ入れず、chart dataから証明するtheoremを分離する。

### R5 — affine open coverとactual overlap

- chart imageが`X`をjointly coverすることをactual topological statementとして定義する。
- pair overlapをchart morphismのpullbackまたはopen intersectionとして構成する。
- overlapから左右chartへのmapがopen immersionであることを証明する。
- coordinate algebra comparison、structure sheaf restriction、decoration restrictionをoverlap objectへ型付けする。
- triple overlapでunderlying scheme mapsとdecoration comparisonが一致することを証明する。
- overlap scheme、map、comparisonをあらかじめ選んでcocycle結論をfieldにするだけの経路を作らない。

### R6 — standard architecture scheme core

- actual Mathlib `Scheme`、global decoration、chosen affine open cover、local presentation、
  pair/triple compatibilityをまとめるcoreを導入する。
- coreのproperty fieldはR4〜R5の具体predicateとproofを保持し、自由な`Prop` labelを保持しない。
- underlying scheme、chart、overlap、decoration、structure sheafへのconstructor/destructor/ext APIを用意する。
- standard scheme morphismとdecoration preservation proofからdecorated morphismを定義する。
- preservation proof以外の追加morphism dataを持たず、proof irrelevanceを使ったHom extensionalityを証明する。
- decorated morphismのidentity、composition、category lawsを証明し、actual category instanceを構成する。
- decorationを忘れるfunctorを構成し、Hom extensionalityからfaithfulnessを証明する。

### R7 — constructors and examples

- actual `Spec A`からsingle-affine standard architecture schemeを構成する。
- 非自明coefficient ring、二つ以上のchart、非空overlap、非恒等restrictionを持つexampleを構成する。
- exampleのopen immersion、joint coverage、pair overlap、triple compatibilityをLean theoremで確認する。
- 二つの同一chartをindexだけ変えて並べる例や、overlapが空の例だけを主証拠にしない。

### R8 — optional chart gluing constructor

- Mathlibの利用可能なAPIで、compatible affine chartsからunderlying schemeを構成できる場合は、
  standard architecture scheme coreへのgluing constructorを追加する。
- gluing後のchart maps、joint coverage、overlap、decoration compatibilityを証明する。
- このconstructorが実装不能でも、既存standard scheme上のactual atlasを持つR6〜R7が完成していれば、
  その事実だけを理由にfixed statementを変更しない。gluing constructorを必須targetに固定した場合は停止する。

### R9 — legacy migration・統合・監査

- legacy `ChartCompatibility` / `ArchitectureScheme`から新coreへの変換は、
  actual Scheme、open immersion、coverage、overlap、cocycleの証明が追加で与えられる場合だけ提供する。
- `allConditions`を持たないlegacy valueに自動adapterを与えない。
- 新moduleを`Formal/AG.lean`へ接続する。
- target declarationsとnontrivial examplesをstatement contractsとaxiom auditへ追加する。
- Lean theorem indexとproof-obligation台帳を必要範囲で同期する。

## Acceptance Criteria

- [ ] AC1: executable contractがstandard scheme core、chart、forgetful API、nontrivial exampleの実装signatureを直接参照する。
- [ ] AC2: standard architecture scheme coreのunderlying objectがactual Mathlib `Scheme`である。
- [ ] AC3: 各chartがactual affine scheme、chart morphism、open immersion proofを持つ。
- [ ] AC4: chart familyがunderlying schemeをjointly coverすることがactual predicateで証明される。
- [ ] AC5: pair overlapがactual scheme objectとmorphismで構成され、左右chart restrictionと一致する。
- [ ] AC6: triple overlapのunderlying mapとdecoration comparisonがactual equalityまたはiso coherenceとして証明される。
- [ ] AC7: global decorationがcoreの第一級dataであり、chosen atlasのlocal decorationはそのrestrictionとして構成される。
- [ ] AC8: 各chartのAAT section ringとcoordinate ringがactual ring isomorphismで接続され、overlap restrictionと可換である。
- [ ] AC9: decorated morphismはunderlying scheme morphismとpreservation proofだけを持ち、actual category instanceとfaithful forgetful functorが構成される。
- [ ] AC10: raw representabilityがquotient universal propertyを使い、sheafified representabilityがselected comparisonを実際に使う。
- [ ] AC11: single-affine constructorがactual `Spec`から発火する。
- [ ] AC12: 二chart、非空overlap、非自明coefficient ringを持つexampleがopen immersion、coverage、compatibilityを満たし、identity caseではないfinite/localization presentationがsheafified representability comparisonを発火させる。
- [ ] AC13: 新主経路に自由な`Prop` slot、`Prop + holds`、結論相当certificate、未使用material premiseがない。
- [ ] AC14: legacy packageだけではnew coreへ変換できず、必要なstandard geometry proofを要求する。
- [ ] AC15: 新definitionにconstructor/destructor/ext/characterization/comparison APIがあり、主要利用者がdefinition unfoldに依存しない。
- [ ] AC16: target declarationsとexamplesがstandard axiomsのみを使用し、statement contractsとaxiom auditがgreenである。
- [ ] AC17: `docs/aat/algebraic_geometric_theory/**`に変更がなく、Lean台帳だけが必要範囲で同期される。
- [ ] AC18: `math-lean-review`の4本の独立査読がすべて`No major findings`である。

## Failure Contract

次は完了ではなく失敗である。

- `LocallyRingedSpace`、chart labels、arbitrary compatibility propsを並べただけのnew package。
- `openImmersion : Prop`、`cocycle : Prop`などを実データと証明の代用にすること。
- all-identity chart、empty overlap、single chartだけでatlas completionを主張すること。
- sheafified representabilityでpresentation comparisonを使わないこと。
- standard Schemeへ接続しないAAT専用scheme analogueを追加すること。
- AAT structure sheaf section ringとscheme chart coordinate ringを独立に格納したままにすること。
- additional comparison map dataをmorphismへ持たせたままforgetful functorのfaithfulnessを主張すること。
- legacy wrapperのrenameまたはrepackageだけでnew core完成とすること。
- implementation convenienceを理由に数学本文のarchitecture schemeを弱めること。

## 停止条件

- 数学本文のarchitecture scheme定義にLean実装と独立した反例、型不整合、well-definedness欠陥が見つかった。
- fixed statementを弱める、material premiseを増やす、参照definitionを結論相当に変更する必要が生じた。
- Mathlib APIではactual Scheme、open immersion、joint coverage、overlapを固定statementどおり表現できない。
- nontrivial two-chart exampleが構成できず、identityまたはempty-overlap exampleだけが残る。
- decoration compatibilityをtyped comparison mapとして構成できず、自由な`Prop` slotが必要になる。

停止報告には、該当AC、最小の反例またはAPI blocker、試したMathlib route、未放電仮定、
本文改訂の要否、代替となるstandard geometry設計を記録する。

## Non-goals

- law-generated ideal sheaf、lawful closed subscheme、factorization theoremの構成。
- conormal sequence、Čech connecting class、first-order lift、G-07蒸留。
- arbitrary schemeに対する一般的なaffine gluing theoryの再実装。
- algebraic stack、gerbe、derived scheme、cotangent complexの構成。
- general reading functoriality、coverage refinement、coefficient base change。
- 数学本文へのLean status、Issue、PR、declaration名の追加。

## 検証

検証手順と実行主体は`AGENTS.md`の「よく使う検証」「PR前の確認」と
`docs/aat/guideline.md`を直接適用する。task固有の追加検査は、actual Scheme、
`Scheme.AffineOpenCover`、pair/triple overlap、section-ring comparison、Hom extensionality、
forgetful faithfulnessをstatement contractsとaxiom auditが直接参照していることの確認である。
