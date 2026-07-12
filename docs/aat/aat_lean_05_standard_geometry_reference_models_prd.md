# PRD: AAT Lean Standard Geometry Reference Models

- 作成: 2026-07-13
- 対象: `Formal/AG/Examples`と`Formal/AG/LawAlgebra`のstandard geometry reference model、aggregate、statement contracts、axiom audit、Lean台帳
- 数学的正典: `docs/aat/algebraic_geometric_theory/` 第II部〜第III部、Appendix A.4〜A.8・B章のfinite examples
- 品質基準: `AGENTS.md`、`docs/guideline.md`、`docs/aat/guideline.md`、`docs/aat/lean_quality_standard.md`
- tracking Issue: 未作成。Issue作成と依存登録が済むまで実行不可
- executable contract: `Formal/AG/StatementContractsStandardGeometryReferenceModels.lean`。実装と同時に作成し、CIでelaborateする
- 実行単位: GitHub tracking Issue配下の `1 Issue = 1 PR`

## 実行開始条件

- tracking Issueが作成され、対象main commit、target一覧、material premise表、子Issue依存が登録されている。
- 同Issueが、Atom由来ringed site、actual standard architecture scheme、law-generated `IdealSheafData`、
  lawful closed subscheme、actual factorization、law inclusion comparisonに加え、semantic lawfulnessを
  witness vanishingの別名にせず本文 定理11.1のpremiseをproof-useするfull correspondence theoremを提供するmerged宣言へのdependencyを持つ。

いずれかが欠ける間、このPRDは実行しない。

## Statement Design

この節を本PRDのfixed statement designとする。別のMarkdown contractは作成しない。
target名、primitive input、生成経路、結論のconjunctを実装中に変更しない。
実装後は`Formal/AG/StatementContractsStandardGeometryReferenceModels.lean`が実装signatureを回帰検査する。

### SD1 — primitive inputと生成物

`StandardGeometryReferenceInput`はcoefficient ring、typed coordinate presentation、二つのcover generator、
weak/strong closed-equational witness family、そのlaw inclusion、lawful-both、weaker-only、
unlawful-bothの三evaluationだけを持つ。Scheme、chart、overlap、ideal、closed subscheme、
scheme morphism、lawfulness、factorization、strictness/nonempty proofをfieldに持たない。

単一の`standardGeometryReferenceInput`から、次をupstream constructorで生成する。

- `standardGeometryReferenceScheme : AlgebraicGeometry.Scheme`
- `standardGeometryReferenceArchitectureScheme : StandardArchitectureScheme k`
- `standardGeometryReferenceWeakReading` / `standardGeometryReferenceStrongReading`
- `standardGeometryReferenceLawInclusion`
- weak/strong `IdealSheafData`とlawful closed subscheme
- 三evaluationに対応するactual `Spec ℤ ⟶ standardGeometryReferenceScheme`

第一候補の具体値は`ℤ[x]`、`D(x)`、`D(1-x)`、`(x(x-1))`、`(x)`とする。
候補変更が必要ならPRDを先に改訂し、同一input provenanceと以下の結論を維持する。

### SD2 — component target

次の名前と結論を固定する。

- `standardGeometryReference_twoChart_cover`: actual affine chart maps、open immersion、joint coverage、
  overlapとsection-ring/localization、global/local decoration compatibilityを持つtwo-chart cover。
- `standardGeometryReference_overlap_nonempty`: actual pair overlapが非空。
- `standardGeometryReference_restriction_nonidentity`: 少なくとも一つのrestrictionがidentityでない。
- `standardGeometryReference_ideal_strict`: weak ideal `<` strong ideal。
- `standardGeometryReference_ideals_nonzero_proper`: 両idealが`⊥`でも`⊤`でもない。
- `standardGeometryReference_closed_nonempty_proper`: 両closed subschemeが非空かつambient全体でない。

結論相当proofをprimitive inputへ移さない。

### SD3 — test morphism firing

`standardGeometryReference_lawfulBoth_fires`は両readingで`LawfulAlong`とactual factorizationの存在、
`standardGeometryReference_weakerOnly_fires`はweakでlawful/factorizationあり、strongでlawfulでなく
factorizationなし、`standardGeometryReference_unlawfulBoth_fires`は両readingでlawfulでなく
factorizationなしを結論とする。各semantic claimはclosed-equational geometryのcanonical
`lawfulnessIdealFactorizationCorrespondence`をproof-useする。

### SD4 — comparisonとintegrated firing theorem

`standardGeometryReferenceComparison`はstrong lawful closed subschemeからweak lawful closed subschemeへの
actual morphismとする。`standardGeometryReferenceComparison_isClosedImmersion`と、両closed immersionを
ambient上で結ぶ`standardGeometryReferenceComparison_triangle`を固定する。

`standardGeometryReference_fires`は単一inputから、two-chart cover、非空overlap、非identity restriction、
strict/nonzero/proper ideal pair、非空proper closed geometry、三test morphismのlawfulness yes/no、
factorization yes/no、comparison closed immersion、ambient triangleを一つのconjunctionとして返す。
component theoremから組み立て、結論相当structureのfield projectionだけで閉じない。

## 問い

同一のtyped primitive inputから、standard geometry coreの全主要層を非退化に発火できるか。

```text
typed Atom / coordinate / law / cover input
  -> ringed AAT site
  -> actual Mathlib Scheme
  -> two affine open charts with inhabited overlap
  -> law-generated strict ideal pair I_U < I_V
  -> actual lawful closed subschemes
  -> lawful / unlawful test morphisms
  -> Flat_V(X) -> Flat_U(X) -> X
```

Scheme、atlas、ideal、closed immersion、factorization、lawfulness proofを別々に選んで並べるのではなく、
primitive inputから各constructorを通して同じprovenanceで導出する回帰基盤を作る。

## 現状診断

- `Formal/AG/Examples/FiniteModel.lean`にはfinite Atom/site/two-patch coverがあるが、
  two-patch coverはcontext siteでありactual scheme atlasではない。
- `Formal/AG/LawAlgebra/FiniteExamples.lean`にはnonzero witness ideal、evaluation、
  lawful/unlawful readingがあるが、主対象はring idealと`PrimeSpectrum.zeroLocus`のset-level readingである。
- scheme chart、ideal、Čech、derived、measurementのfinite examplesは複数moduleに分散し、
  同一inputからstandard Scheme・closed subscheme・test morphismまでを接続する統合fixtureがない。
- singleton、identity restriction、zero ideal、selected certificateを使うexamplesが個別interfaceの発火には使われている。
- 数学本文Appendixのworked examplesはfinite AAT geometryの縦断例を与えるが、
  actual two-chart standard Schemeとlaw-sensitive closed subscheme pairのLean回帰定理には未接続である。

## Reference model

第一候補は次のexplicit affine modelとする。Mathlib API調査で同じAcceptance Criteriaを満たせない場合だけ、
tracking Issueに根拠を記録して別のfinite-type affine modelへ変更する。

```text
A = Int[x]
X = Spec A
cover = D(x), D(1 - x)
I_U = (x(x - 1))
I_V = (x)
```

- `D(x)`と`D(1-x)`はjointly coverし、overlap`D(x(1-x))`はnonemptyである。
- `I_U < I_V`で、`Flat_V(X) -> Flat_U(X) -> X`がlaw inclusionを読む。
- evaluation`x ↦ 0`は両lawにlawful、`x ↦ 1`は`U`にlawfulで`V`にunlawful、
  `x ↦ 2`は両lawにunlawfulとなる候補である。

数値や環の選択は実装都合でロックしない。固定するのは下記の非退化条件と生成provenanceである。

## アウトカム

完了時に次が成り立つ。

1. 結論相当fieldを持たない小さいprimitive reference inputがある。
2. actual `Scheme`と二つのactual affine open chartが同じinputから生成される。
3. chartはjointly coverし、pair overlapはnonempty、restriction/localizationは非恒等である。
4. two law readingsからnonzero properなstrict ideal pairが生成される。
5. 両idealがactual `IdealSheafData.subscheme`とclosed immersionを与える。
6. lawful/unlawful test morphismがactual scheme morphismとして構成される。
7. semantic lawfulness、ideal pullback、actual factorizationのyes/noがfull correspondence theoremで一致する。
8. strict law inclusionからactual closed immersionの塔が構成される。
9. 全主要conjunctを同一inputからまとめるintegrated firing theoremがある。

## 採否規律

- 数学本文はread-onlyとし、`docs/aat/algebraic_geometric_theory/**`を変更しない。
- reference inputへScheme、ideal、chart map、closed immersion、factor morphism、lawfulness certificateを入れない。
- actual scheme atlasとcontext-site coverを同一視しない。
- semantic lawfulnessをideal vanishingの別名にしない。
- individual examplesを無関係な入力で構成し、vertical sliceと呼ばない。
- exact polynomial modelより、nonzero/proper/strict/inhabited/nonidentityの判定可能条件を固定する。
- target statementと参照definitionは、このPRDの`Statement Design`節を不変入力とする。

## 改修要求

### R0 — fixed statementとcandidate modelの監査

- tracking Issueに対象main commitを固定する。
- Mathlib `Spec`、principal open、localization、`AffineOpenCover`、`IdealSheafData`、
  quotient spectrum、evaluation-induced scheme morphismの利用可能APIを確認する。
- candidate modelのjoint coverage、inhabited overlap、ideal strictness、test evaluationを紙上計算とLean型で突合する。

### R1 — primitive reference input

- coefficient ring、typed coordinate meaning、cover generators、closed-equational witness equations、
  law inclusion、test evaluationsだけを持つinputを定義する。
- Atom / law / coordinate provenanceを既存core constructorへ接続する。
- output Scheme、ideal、atlas morphism、lawfulness、factorizationをfieldに入れない。
- nontrivialityは後続theoremで証明し、`isNontrivial : Prop`とcertificateの組をinputにしない。

### R2 — generated standard Scheme and atlas

- coordinate algebraからactual`X = Spec A`を構成する。
- two principal-open charts、actual open immersions、joint coverageを構成する。
- pair overlapをactual scheme objectとして構成し、inhabitedであることを証明する。
- chart section ringsとlocalizationsのcomparison、左右restriction、global/local decoration compatibilityを証明する。
- 二chartを同じopen rangeのduplicateとして作らない。

### R3 — law-generated strict ideal pair

- witness equationsから`I_U`と`I_V`を主constructorで生成する。
- `I_U ≤ I_V`をlaw inclusionから証明する。
- `I_U`と`I_V`がzeroでもunitでもなく、strict inclusionであることを証明する。
- affine chartsへのrestrictionとpair overlap上の一致を証明する。
- arbitrary `Ideal A`を入力して同じ結論を得るrouteを使わない。

### R4 — actual lawful closed geometry

- `I_U.subscheme`、`I_V.subscheme`と各`subschemeι`を構成する。
- actual closed immersion、kernel equality、underlying zero-locus characterizationを証明する。
- affine quotient spectrumとのcanonical comparisonを証明する。
- 両closed subschemeがnonempty properであることをactual pointまたはring theoremから証明する。

### R5 — actual test morphisms

- selected evaluationsからring homを構成し、contravariantなactual scheme morphismを得る。
- 少なくともlawful-both、weaker-only-lawful、unlawful-bothの三つの挙動を証明する。
- このPRDの`Statement Design`節が固定したcanonical full correspondence theoremから、
  semantic lawfulness、ideal pullback zero、actual factorizationの一致を証明する。
- canonical theoremが本文 定理11.1のmaterial premiseを同じ量化対象で使い、
  `LawfulnessIdealCorrespondenceAssumptions` / `LawfulnessIdealCorrespondencePackage`のfield射影で閉じないことを確認する。
- factorization yesではactual liftとtriangle、noではlift不存在を証明する。
- lawfulnessやlift不存在をinput fieldまたはopaque certificateから読まない。

### R6 — law inclusion comparison

- typed law inclusionから`I_U ≤ I_V`と`Flat_V(X) ⟶ Flat_U(X)`を構成する。
- comparison morphismがactual closed immersionであり、ambientへのtriangleが可換であることを証明する。
- selected instanceでidentity/composition lawを発火させる。
- point-set inclusionだけでcomparison completionとしない。

### R7 — integrated firing theorem

- Scheme、two-chart atlas、overlap、strict ideals、closed immersions、test morphisms、comparison morphismを
  同じprimitive inputから得る一つのconjunction theoremを証明する。
- theorem proofは各constructorとcharacterization theoremを使い、結論相当packageのfield projectionだけで閉じない。
- 各conjunctのproof-useをstatement contractと最終レビューで監査する。

### R8 — regression integration

- dedicated moduleを`Formal/AG/Examples/`に追加し、`Formal/AG.lean`へ接続する。
- target declarationsとexamplesをstatement contractsとaxiom auditへ追加する。
- existing finite examplesを再利用する場合は、actual standard coreとのcomparison theoremを持たせる。
- Lean theorem indexとproof-obligation台帳を必要範囲で同期する。
- `Formal/AG`からResearch moduleをimportしない。

## Acceptance Criteria

- [ ] AC1: executable contractがprimitive input、component theorem、integrated firing theoremの実装signatureを直接参照する。
- [ ] AC2: primitive inputにScheme、ideal、chart morphism、closed immersion、factorization、lawfulness certificateがない。
- [ ] AC3: underlying geometryがactual Mathlib `Scheme`である。
- [ ] AC4: 二chartがactual affine open immersionでjointly coverする。
- [ ] AC5: overlapがactual nonempty scheme objectで、左右restrictionと一致する。
- [ ] AC6: chart restriction/localizationが非恒等に発火する。
- [ ] AC7: chart section ringとlocalizationのcomparison、左右restriction、global/local decoration compatibilityが証明される。
- [ ] AC8: `I_U`と`I_V`が同一inputのlaw witnessesから生成される。
- [ ] AC9: ideal pairがnonzero、proper、strict inclusionを満たし、chart restrictionとoverlap一致が証明される。
- [ ] AC10: 両lawful geometriesがactual `IdealSheafData.subscheme`とclosed immersionを持つ。
- [ ] AC11: kernel equality、zero-locus characterization、affine quotient spectrum comparisonが証明される。
- [ ] AC12: 両lawful closed subschemesがnonempty properである。
- [ ] AC13: test morphismsがactual scheme morphismとして構成される。
- [ ] AC14: lawful-both、weaker-only-lawful、unlawful-bothの挙動がsemantic lawfulnessとactual factorizationの双方で証明される。
- [ ] AC15: AC14はcanonical full correspondence theoremを使い、`LawfulnessIdealCorrespondenceAssumptions` / `LawfulnessIdealCorrespondencePackage`または同型の結論fieldを使用しない。
- [ ] AC16: `Flat_V(X) ⟶ Flat_U(X)`がactual closed immersionでambient triangleが可換であり、selected instanceでidentity/composition APIが発火する。
- [ ] AC17: integrated firing theoremの全conjunctが同一primitive inputから導出され、repackageで閉じない。
- [ ] AC18: target declarationsとexamplesがstandard axiomsのみを使用し、statement contractsとaxiom auditがgreenである。
- [ ] AC19: `docs/aat/algebraic_geometric_theory/**`に変更がなく、Lean台帳だけが必要範囲で同期される。
- [ ] AC20: `math-lean-review`の4本の独立査読がすべて`No major findings`である。

## Failure Contract

次は完了ではなく失敗である。

- Scheme、atlas、ideal、morphismを無関係なinputから別々に作り、統合exampleと呼ぶこと。
- single chart、duplicate chart、empty overlap、all-identity restrictionだけで発火すること。
- arbitrary ideal、selected closed immersion、comparison morphism、factorization certificateを入力すること。
- zero ideal、unit ideal、empty lawful geometryだけでlaw geometryを発火させること。
- `PrimeSpectrum`のpoint setだけでactual closed subschemeを代用すること。
- semantic lawfulnessをideal vanishingの別名にすること。
- `LawfulnessIdealCorrespondenceAssumptions` / `LawfulnessIdealCorrespondencePackage`または同型の結論fieldからsemantic correspondenceを射影すること。
- integrated theoremを結論相当structureのfield projectionだけで閉じること。
- candidate modelの具体値に固執してAcceptance Criteriaを弱めること。

## 停止条件

- 数学本文のworked exampleまたはstandard geometry claimにLean実装と独立した反例、型不整合、well-definedness欠陥が見つかった。
- fixed statementを弱める、本文にないmaterial premiseを追加する、結論相当fieldを追加する必要が生じた。
- actual two-chart open coverまたはinhabited overlapをmerged standard APIから構成できない。
- law witnessesからnonzero proper strict ideal pairを生成できず、arbitrary ideal入力が必要になる。
- lawful/unlawful actual morphismまたはcomparison morphismをuniversal propertyから構成できない。
- 複数のcandidate modelを試しても非退化条件を同時に満たせない。

停止報告には、該当AC、試したmodel、最小API blocker、未放電仮定、
構成できた最長のprovenance chain、本文改訂の要否を記録する。

## Non-goals

- general reading functoriality、coverage refinement、coefficient base changeの新定理。
- G-07、conormal sequence、Čech connecting class、first-order liftの本体蒸留。
- legacy surfaceの削除・rename・migration。
- derived scheme、stack、gerbe、higher obstructionのreference model。
- 数学本文へのLean status、Issue、PR、declaration名の追加。

## 検証

検証手順と実行主体は`AGENTS.md`の「よく使う検証」「PR前の確認」と
`docs/aat/guideline.md`を直接適用する。task固有の追加検査は、nonempty overlap、strict ideal pair、
factorization yes/no、comparison closed immersion、integrated firing theoremの全conjunctを
statement contractsとaxiom auditが直接参照していることの確認である。
