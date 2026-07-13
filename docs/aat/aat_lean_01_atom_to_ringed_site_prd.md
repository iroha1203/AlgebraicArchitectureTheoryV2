# PRD: AAT Lean Atom由来readingからringed siteまでの生成基盤

- 作成: 2026-07-12
- 対象: `Formal/AG/Atom`、`Formal/AG/Site`、`Formal/AG/LawAlgebra` のsite・raw algebra・structure sheaf層、aggregate、statement contracts、axiom audit、Lean台帳
- 数学的正典: `docs/aat/algebraic_geometric_theory/` 第I部〜第III部
- 品質基準: `AGENTS.md`、`docs/guideline.md`、`docs/aat/guideline.md`、`docs/aat/lean_quality_standard.md`
- tracking Issue: #3308
- core / obstruction split contract: [`statement_contracts/aat_core_obstruction_split.md`](statement_contracts/aat_core_obstruction_split.md)
- executable contract: `Formal/AG/StatementContractsAtomToRingedSite.lean`。実装と同時に作成し、CIでelaborateする
- 実行単位: GitHub tracking Issue配下の `1 Issue = 1 PR`

## 実行開始条件

- tracking Issueが作成され、対象main commit、target一覧、material premise表、子Issue依存が登録されている。

## Statement Design

この節は現行statement contractを参照する設計入力であり、実装状態は記録しない。
実装後は`Formal/AG/StatementContractsAtomToRingedSite.lean`が、現行contractに固定したtargetと
実装宣言のLean signatureを回帰検査する。

### SD1 — AAT Core generation

定理10.5のcoreは、family、configuration、architecture object、law universe、signature、
object algebraを持つ無条件生成層とする。`ObstructionCircuit`はcoreの必須fieldにしない。
ここで無条件とは、selected law failureをpremiseとして要求しないことを指す。
生成済みlaw universeのindex、選ばれたfinite Atom family / relation support、
そのlawが生成済みobject上で失敗する証明がある場合だけ、`ObstructedAATCorePackage`を
dependent extensionとして構成する。

このsplitで変更するLean schema、constructor、characterization API、all-laws-hold counterexampleの
固定signatureは
[`statement_contracts/aat_core_obstruction_split.md`](statement_contracts/aat_core_obstruction_split.md)
を不変入力とする。失敗lawをconstructor内部で作らず、呼出側が生成済みlaw indexを指定する。

### SD2 — selected geometry reading

`Site.SelectedGeometryReading (core : AATCorePackage U)`は、core law universeからのtyped law selection、
coverage requirements、context preorder、overlap dataだけを保持する。
`toAATSite`は`AATSite core.object`を返し、`topology_eq_generated`はそのtopologyが
admissible coverageから生成されたMathlib `GrothendieckTopology`であることを述べる。
architecture object、core law universe、signatureは`core`から読み、coefficient ringはraw algebra層の
独立parameterとする。

### SD3 — typed raw algebra presheaf

```lean
def RawAmbientAlgebraPresheafBridge.ofTypedRestrictions
    (S : Site.AATSite A)
    (B : RawAmbientPresheafBridge (A := A) k) :
    RawAmbientAlgebraPresheafBridge S k
```

`ofTypedRestrictions_objectIso`は各objectのring equivalenceを、
`ofTypedRestrictions_map`はrestrictionが`B.res`から構成されることを述べる。
objectwise equivalenceやnaturalityを追加引数にせず、`restrictionStable`、`identity_law`、
`composition_law`をproof bodyで使う。

### SD4 — ringed AAT site

```lean
structure RingedAATSite
    {U : AtomCarrier} {A : ArchitectureObject U}
    (S : Site.AATSite A) (k : Type) [CommRing k] where
  raw : AlgebraValuedAATPresheaf S k
```

`RingedAATSite.structureSheaf`と`canonical`は`raw`のMathlib sheafificationとそのunitから定義し、
structure fieldとして選択させない。必要な`HasSheafify`はinstance parameterとする。
`ofMathlibSheafification`、`structureSheaf_eq_sheafify`、`canonical_eq_toSheafify`、
`lift_unique`、`underlyingTypeSheaf`を固定targetとする。sheafificationの普遍性は自由なfieldにせず、
Mathlib `HasSheafify`から構成・証明する。無関係なType-valued sheaf、`LocallyRingedSpace`、
presentation certificateを入力しない。

### SD5 — end-to-end constructor

```lean
def generateRingedAATSite
    (S : AtomAxiomSystem U)
    (reading : Site.SelectedGeometryReading (AATCorePackage.generate S))
    (k : Type) [CommRing k]
    (raw : RawAmbientPresheafBridge
      (A := (AATCorePackage.generate S).object) k)
    [CategoryTheory.HasSheafify
      reading.toAATSite.topology (AATCommAlgCat k)] :
    RingedAATSite reading.toAATSite k
```

characterization theoremは、site、raw presheaf、structure sheaf、canonical map、architecture objectが
それぞれ`reading.toAATSite`、`ofTypedRestrictions`、Mathlib sheafification、`toSheafify`、
`AATCorePackage.generate S`に由来することを一つの入力provenanceの下で固定する。

## 問い

固定されたAtom公理系、selected law reading、coverage requirements、coefficient ringから、
次の対象を同じ入力provenanceの下でLean上に生成できるか。

```text
Atom axiom system
  -> Atom family / configuration / architecture object
  -> core law universe / signature / object algebra / AAT core
  + generated law index / law failure -> obstructed AAT core
  + selected geometry law universe / coverage requirements / coefficient ring
  -> architecture context category
  -> admissible coverage and generated Grothendieck topology
  -> AAT site
  -> typed raw coordinate algebra presheaf
  -> commutative-ring-valued sheafification
  -> ringed AAT site presentation
```

完了対象は、無関係に選択されたsite、presheaf、sheaf、ringed spaceをpackageへ並べることではない。
各矢印をdefinition、constructor、universal property、comparison theoremで構成し、
後続のscheme・ideal・cohomology形式化が同じsiteとstructure sheafを再利用できる基盤を作る。

## 現状診断

- `AATCorePackage`、`PartIPrerequisites`、`ArchitectureGeometry`、`AATSite`、
  `AATGrothendieckTopology`は存在する。
- `AATCorePackage.ofComponents`はfamily、configuration、architecture object、law universe、
  signatureを受け取り、obstructionを必須入力にしない。actual obstructionは生成済みlaw index、
  finite circuit data、そのfailureから`ObstructedAATCorePackage`として構成する。core側はなお
  Atom公理系からのgeneration theoremではなくselected componentのassemblyである。
- `AATCorePackage.objectAlgebraOfComponents`は`PUnit`上のsingleton object/operationを使うため、
  非退化なcore generationの主証拠にはならない。
- `RawAmbientPresheafBridge`と`RawAmbientAlgebraPresheafBridge`は、context-indexed raw algebraと
  site-indexed presheafの対応を記録する。
- `LawAlgebraSheafificationBridge`はsheafified objectと普遍性を記録し、
  `ofMathlibSheafification`はMathlibの`HasSheafify`から構成できる。
- `LawAlgebraSheafPackage`はraw presheaf、sheafification、presentation stabilityをまとめるが、
  `SelectedLawAlgebraPresentation`の`presentsRaw`と`presentsSheafified`は自由な`Prop`である。
- `RingedAATTopos`はType-valued sheaf object、law algebra sheaf package、
  `LocallyRingedSpace`を独立に格納でき、それらが同じringed geometryを表すことを型が保証しない。
- 現在の`ArchitectureGeometry`は`PartIPrerequisites`のobjectとsiteを結ぶが、
  raw coordinate dataからstructure sheafまでの一本の公開constructorを持たない。

既存の各部品は再利用する。課題は新しい包括wrapperを加えることではなく、
既存部品の入力provenanceと標準Mathlib対象への接続をload-bearingなAPIにすることである。

## アウトカム

完了時に次が成り立つ。

1. Atom公理系からfamily、configuration、architecture object、core law universe、signature、object algebraを無条件に生成する公開経路があり、生成済みlawの失敗からobstructed extensionを構成できる。
2. 生成済みcoreから、selected law readingを持つAAT siteまでの公開constructorがある。
3. typed coordinate family、structural relations、restriction dataからraw ambient algebra presheafが構成される。
4. structural relation idealのrestriction stabilityが、quotient restriction mapとpresheaf functorialityの証明に実際に使われる。
5. Mathlib sheafificationからcommutative-ring-valued structure sheafとcanonical mapが構成される。
6. siteとstructure sheafを同じ対象として保持するringed AAT site presentationがある。
7. underlying Type-valued sheafはstructure sheafのforgetful imageとして得られ、無関係な入力として受け取らない。
8. 少なくとも一つの非退化有限モデルがAtom inputからcore、site、raw algebra、structure sheafまで発火する。
9. 後続のscheme・ideal形式化が新基盤をdefinition unfoldなしで利用できるAPIを持つ。

## 採否規律

- 数学本文の定義8.2と定理10.5は、無条件coreとlaw-failure相対のobstructed extensionを区別する。
- `AATCorePackage.ofComponents`または`ofAxiomRealization`によるassemblyだけを
  Atom-to-ringed-site generationの完了証拠にしない。
- 本文の定理10.5をLean都合でassembly theoremへ弱めない。
- `AATSite`、Mathlib `GrothendieckTopology`、`Sheaf`、`Under CommRingCat`を再発明しない。
- conclusion-shaped propertyをstructure field、typeclass、certificateへ追加しない。
- sheafificationの普遍性、presheaf functoriality、restriction compatibilityを
  supplied proof packageから射影するだけの主定理を完了根拠にしない。
- legacy declarationは直ちに削除しない。新基盤へsoundに変換できる場合だけadapterを置く。
- core law universeは定理10.5の生成対象とし、geometryで使うselected law universeは
  generated core law universeからのtyped selectionとして入力する。coverageとcoefficientはgeometry parameterとして入力する。
- core / obstruction splitのtarget statementと参照definitionは、現行statement contractを不変入力とする。

## 改修要求

### R0 — 現行宣言と固定statementの確定

- tracking Issueに対象main commitを固定する。
- `AATCorePackage`、`PartIPrerequisites`、`ArchitectureGeometry`、`AATSite`、
  raw algebra bridge、sheafification bridge、`LawAlgebraSheafPackage`の完全なsignatureと依存を棚卸しする。
- 各material premiseを本文由来、放電済み、未放電へ分類し、tracking Issueに記録する。

### R1 — Atom towerとAAT coreのgeneration

- `AtomAxiomSystem`からAtom family、configuration、architecture objectへ至る生成dataとconstructorを定義する。
- axiom-side `S.Family`からactual `AtomFamily U`へのcomparisonを明示し、actual familyの全要素が
  selected family tokenのimageとして由来を持つことを証明する。
- axiom-side `S.Configuration`からactual `AtomConfiguration U`へのcomparisonを明示し、
  `S.configurationOf`、actual configuration、family comparisonの可換性を証明する。
- comparison map自体を無関係なactual family/configurationと一緒に外部入力するだけの
  `AtomTowerRealization`型repackageを完了根拠にしない。本文のExtraction Doctrineまたは
  Atom公理系の生成operationからcomparisonを構成する。
- `configurationOf`、family/configuration/objectの一致をproof bodyで使う。
- axiom-side law dataからactual core `LawUniverse`へのcomparisonとimage provenanceを構成する。
- core law universe、signature、object algebraをgenerated Atom towerとaxiom-side law dataから構成し、
  selected componentの再包装にしない。
- `AATCorePackage`からmandatory obstruction law / circuitを除き、生成済みlaw index、finite circuit data、失敗証明に
  dependentな`ObstructedAATCorePackage`を定義する。
- obstructed extensionのconstructorは生成済みlaw indexを入力し、そのindexとcircuitのlawが一致することを
  型とcharacterization theoremで保証する。constructor内部でalways-false lawを作らない。
- すべてのarchitecture object上で成り立つlawにはactual `ObstructionCircuit`が存在しないことを
  counterexample theoremとして証明する。
- geometryで使うlaw universeはgenerated core law universeからのtyped selectionとして与え、
  core generationとgeometry relativityを混同しない。
- object algebraはsingleton identity exampleだけでなく、少なくとも一つの非退化operationを持つmodelで発火させる。
- Atom公理系から生成された各componentが`AATCorePackage`のfieldと一致するcharacterization theoremを証明する。
- 現行coreからarchitecture object、law universe、signatureを読む小さいAPIを整える。
- coverage requirementsとoverlap dataが同じarchitecture objectとlaw universeに型付けされるようにする。
- source、Atom vocabulary、law、coverage、coefficientの相対性を、巨大な万能structureではなく
  既存型のparameterと小さいcomparison definitionで表す。
- `ArchitectureGeometry`またはadditiveな後継型からAAT siteへのconstructorを作る。
- coreと無関係なarchitecture objectまたはlaw universeを差し替えられないことを型とcharacterization theoremで保証する。

### R2 — coverageからGrothendieck topologyまでの生成経路

- admissible coverageから`AATGrothendieckTopology`を生成する現行経路を新APIへ接続する。
- identity、base change、transitivityはMathlibの生成位相APIまたは現行証明へ接続する。
- topologyがselected coverage requirementsから生成されたことをcharacterization theoremで公開する。
- finite-poset regimeを一般APIの実例として接続し、別理論として複製しない。

### R3 — typed raw coordinate algebra presheafの実構成

- contextごとのtyped coordinate familyとstructural relation familyから
  `FreeTypedCommAlg`およびstructural quotient algebraを構成する。
- context morphismに沿うcoordinate restrictionがstructural relation idealを保存することから、
  quotient ring homを構成する。
- identityとcompositionを証明し、actual `AlgebraValuedAATPresheaf`を構成する。
- `RawAmbientAlgebraPresheafBridge.identifiesObject`と`restriction_naturality`を、
  arbitrary fieldとして受け取らず、上記構成のcomparison theoremとして得るconstructorを追加する。
- raw presheafのobjectwise algebraがselected contextのraw ambient quotientと一致することを公開APIにする。

### R4 — Mathlib sheafificationによるstructure sheaf

- R3のraw presheafに対し、利用可能な`HasSheafify`からMathlib sheafificationを構成する。
- canonical map、sheaf condition、universal propertyをMathlib APIから証明する。
- `LawAlgebraSheafificationBridge.ofMathlibSheafification`を主経路へ接続する。
- `SelectedLawAlgebraPresentation`の自由な`presentsRaw` / `presentsSheafified`は、
  新しい主経路の完成根拠に使わない。
- selected presentationが必要な場合は、generator map、quotient comparison、surjectivity、kernel equality、
  algebra isomorphismのいずれか本文の要求に対応する具体述語へ分解する。

### R5 — ringed AAT site presentation

- AAT siteとその上のcommutative-ring-valued structure sheafを同じ対象として保持する新coreを導入する。
- underlying Type-valued sheafはstructure sheafに対するforgetful functorから構成する。
- restriction ring hom、global/local section、canonical raw-to-sheafified mapへアクセスするAPIを持つ。
- extensionality、constructor/destructor、forgetful comparison、legacy comparisonを用意する。
- `RingedAATTopos`から新coreへの変換は、stored componentsの一致を証明できる場合だけ提供する。
- 新coreからlegacy surfaceへの一方向adapterは、既存利用者の段階的移行に必要な場合だけ提供する。

### R6 — 非退化finite vertical slice

- 非自明なcoefficient ring、複数context、非恒等restrictionを持つfinite modelを固定する。
- 同一入力からAAT site、raw algebra presheaf、canonical sheafification、ringed site presentationを構成する。
- 少なくとも一つのstructural relationがquotientとrestrictionに実際に影響することをLean theoremで示す。
- singleton site、`PUnit`だけのcarrier、all-`True` property、定数零restrictionだけのexampleを主発火証拠にしない。

### R7 — API統合・監査・台帳同期

- 新moduleを`Formal/AG.lean`へ接続する。
- target declarationsとfinite exampleを`Formal/AG/AxiomAudit.lean`へ追加する。
- statement contractsを通常aggregateとCIでelaborateさせる。
- 変更した本文対応宣言をLean theorem indexとproof-obligation台帳へ同期する。
- `Formal/AG`からResearch moduleをimportしない。

## Acceptance Criteria

- [ ] AC1: executable contractが主constructor、obstructed extension、ringed site presentation、非退化exampleの実装signatureを直接参照する。
- [ ] AC2: `S.Family` / `S.Configuration` / axiom-side law dataからactual family / configuration / core law universeへのcomparison、image provenance、`S.configurationOf`との可換性が証明され、無関係なselected componentの再包装ではない。
- [ ] AC3: generated architecture objectのfamily/configuration一致がcharacterization theoremで追跡でき、非退化operationを持つmodelで発火する。
- [ ] AC3a: `AATCorePackage`はobstructionを必須fieldに持たず、生成済みlaw index、finite circuit data、その失敗からだけ`ObstructedAATCorePackage`を構成できる。
- [ ] AC3b: all-holding lawにはactual `ObstructionCircuit`が存在しないことがstandard axiomsだけで証明される。
- [ ] AC4: 生成済みAAT coreからAAT siteまでのconstructorがあり、object、law universe、signature、coverage provenanceを失わない。
- [ ] AC5: admissible coverageからactual Mathlib `GrothendieckTopology`が生成される。
- [ ] AC6: typed coordinateとstructural relationからactual algebra-valued presheafが構成され、restriction identity/compositionが証明される。
- [ ] AC7: structural relation idealのrestriction stabilityがquotient restriction mapのproof bodyで使われ、非自明relationがquotientと少なくとも一つのrestriction mapを実際に変える。
- [ ] AC8: raw presheafのMathlib sheafificationからactual commutative-ring-valued sheaf、canonical map、universal propertyが得られる。
- [ ] AC9: ringed AAT site presentationがsiteとstructure sheafを同じ対象として保持し、無関係なType-valued sheafやlocally ringed spaceを入力しない。
- [ ] AC10: underlying Type-valued sheafがstructure sheafのforgetful imageとして構成される。
- [ ] AC11: 新主経路は`presentsRaw : Prop`、`presentsSheafified : Prop`、結論相当certificateの射影だけで閉じない。
- [ ] AC12: 非退化finite vertical sliceが同一Atom inputからcore、site、raw presheaf、structure sheafまで発火する。
- [ ] AC13: 新definitionにconstructor/destructor/ext/characterization/comparison APIがあり、主要利用者がdefinition unfoldに依存しない。
- [ ] AC14: target declarationsとexampleがstandard axiomsのみを使用し、statement contractsとaxiom auditがgreenである。
- [ ] AC15: 数学本文の定義8.2・定理10.5、現行statement contract、Lean台帳が二層設計へ同期される。
- [ ] AC16: `math-lean-review`の4本の独立査読がすべて`No major findings`である。

## Failure Contract

次は完了ではなく失敗である。

- unrelated componentsを並べたpackageの追加。
- `AATCorePackage.ofComponents`またはsingleton object algebraだけでAtom generationを主張すること。
- `S.Family`からactual familyへのarbitrary mapと無関係なactual familyを同時入力し、provenanceと呼ぶこと。
- actual obstruction circuitを無条件coreのfieldとして要求すること。
- 生成済みlaw indexを受けず、constructor内部で失敗lawを作ること。
- circuitのfinitenessを具体的なfinite family witnessではなく自由な`True` markerで閉じること。
- 結論相当のfailure certificateを別fieldから射影してobstructed extensionの存在を主張すること。
- arbitrary presheafとobjectwise equivalenceを入力して生成と呼ぶこと。
- presheaf functoriality、sheaf condition、sheafification普遍性を結論相当fieldから射影すること。
- `True`、未使用material premise、singletonだけで主経路を発火させること。
- Mathlib対象と接続しないAAT専用presheaf・sheaf・ringed objectの再発明。
- current codeが難しいことを理由に数学本文の主張を弱めること。

## 停止条件

- 数学本文の主張にLean実装と独立した反例、型不整合、well-definedness欠陥が見つかった。
- fixed statementを弱める、material premiseを追加する、参照definitionのsignatureを結論相当に変更する必要が生じた。
- Mathlib sheafificationを利用できず、同じ普遍性を持つ構成も対象範囲内で実装できない。
- Atom公理系からactual family/configuration/objectを生成するために本文にないmaterial premiseが必要と判明した。
- 非退化finite modelが構成できず、退化例だけが残る。

停止報告には、該当AC、最小の反例またはAPI blocker、試した構成、未放電仮定、
本文改訂の要否、独立タスクとして切り出す候補を記録する。

## Non-goals

- standard `Scheme`、affine atlas、closed subschemeの構成。
- law-generated ideal sheaf、lawful locus、conormal sheaf、Čech obstructionの構成。
- coverage refinement、coefficient base changeを含む一般reading functoriality。
- G-07または他のResearch成果の本体蒸留。
- 数学本文へのLean status、Issue、PR、declaration名の追加。

## 検証

検証手順と実行主体は`AGENTS.md`の「よく使う検証」「PR前の確認」と
`docs/aat/guideline.md`を直接適用する。task固有の追加検査は、Atom-family comparison、
image provenance、raw presheaf functoriality、sheafification universal propertyを
statement contractsとaxiom auditが直接参照していることの確認である。
