# PRD: AAT Lean Closed-Equational Law Geometry

- 作成: 2026-07-12
- 対象: `Formal/AG/LawAlgebra`のlaw witness・ideal sheaf・lawful closed geometry・factorization層、examples、aggregate、statement contracts、axiom audit、Lean台帳
- 数学的正典: `docs/aat/algebraic_geometric_theory/` 第III部 定義5.1〜11.1、Appendix A.6〜A.8
- 品質基準: `AGENTS.md`、`docs/guideline.md`、`docs/aat/guideline.md`、`docs/aat/lean_quality_standard.md`
- tracking Issue: 未作成。Issue作成と依存登録が済むまで実行不可
- executable contract: `Formal/AG/StatementContractsClosedEquationalGeometry.lean`。実装と同時に作成し、CIでelaborateする
- 実行単位: GitHub tracking Issue配下の `1 Issue = 1 PR`

## 実行開始条件

- tracking Issueが作成され、対象main commit、target一覧、material premise表、子Issue依存が登録されている。
- 同Issueが、actual Mathlib `Scheme`、global AAT decoration、actual affine open cover、
  ringed AAT site section-ring comparisonを提供するmerged宣言へのdependencyを持つ。

いずれかが欠ける間、このPRDは実行しない。

## Statement Design

この節を本PRDのfixed statement designとする。別のMarkdown contractは作成しない。
target名、入力、量化対象、material premise、結論、主要definition signatureを実装中に変更しない。
実装後は`Formal/AG/StatementContractsClosedEquationalGeometry.lean`が下記targetを直接参照し、
実装宣言のLean signatureを回帰検査する。

### SD1 — law reading、ideal sheaf、closed geometry

```lean
structure ClosedEquationalLawReading
    (X : StandardArchitectureScheme k) where
  LawIndex : Type u
  selected : Set LawIndex
  witness : ∀ L, selected L → ClosedEquationalLawWitness X L

def lawWitnessIdealSheaf (U : ClosedEquationalLawReading X)
    (L : U.LawIndex) (hL : U.selected L) : X.underlying.IdealSheafData

def lawGeneratedIdealSheaf (U : ClosedEquationalLawReading X) :
    X.underlying.IdealSheafData :=
  ⨆ L, ⨆ hL : U.selected L, lawWitnessIdealSheaf U L hL

def lawfulClosedSubscheme (U : ClosedEquationalLawReading X) :
    AlgebraicGeometry.Scheme := (lawGeneratedIdealSheaf U).subscheme

def lawfulClosedImmersion (U : ClosedEquationalLawReading X) :
    lawfulClosedSubscheme U ⟶ X.underlying :=
  (lawGeneratedIdealSheaf U).subschemeι
```

`ClosedEquationalLawReading`はlaw/witness/context/coefficient provenanceだけを持ち、ideal sheaf、
closed subscheme、closed immersion、lawfulness、factorizationをfieldに持たない。
`LawfulAlong`はsemantic predicateとして定義し、ideal comap zeroの別名にしない。

### SD2 — generationとactual factorization

```lean
def WitnessVanishes (U : ClosedEquationalLawReading X)
    (s : T ⟶ X.underlying) : Prop :=
  ∀ L, ∀ hL : U.selected L, (lawWitnessIdealSheaf U L hL).comap s = ⊥

def FactorsThroughLawfulClosedSubscheme
    (U : ClosedEquationalLawReading X) (s : T ⟶ X.underlying) :=
  {t : T ⟶ lawfulClosedSubscheme U //
    t ≫ lawfulClosedImmersion U = s}
```

`lawGeneratedIdealSheaf_eq_iSup_witness`、`lawfulClosedImmersion_isClosedImmersion`、
`lawfulClosedImmersion_ker`、affine chart上の`Spec(A/I)` comparison iso、
`witnessVanishes_iff_idealComap_eq_bot`、
`idealComap_eq_bot_iff_nonempty_factorization`、`factorization_unique`を固定targetとする。
factorizationはactual morphism、triangle equality、uniquenessで表す。

### SD3 — 定理11.1

canonical target `lawfulnessIdealFactorizationCorrespondence`は、同じ`U`、section morphism `s`、
architecture object、law universe、signature、obstruction valuation、zero-reflecting aggregation、
`U`-adequate coverと、本文の七premiseに対応するsoundness、completeness、axis exactness、
witness coverage、descent、ring restriction compatibilityの具体proofを入力する。
結論の完全なshapeを次で固定する。

```lean
(LawfulAlong U s ↔ WitnessVanishes U s) ∧
(WitnessVanishes U s ↔ (lawGeneratedIdealSheaf U).comap s = ⊥) ∧
((lawGeneratedIdealSheaf U).comap s = ⊥ ↔
  Nonempty (FactorsThroughLawfulClosedSubscheme U s)) ∧
(LawfulAlong U s ↔ omegaU valuation LU aggregation Obj = valuation.domain.zero) ∧
(LawfulAlong U s ↔ RequiredSignatureAxesZero Obj Sig)
```

七premiseはtargetと同じ対象に型付く具体predicateとし、自由な`Prop` fieldや
`LawfulnessIdealCorrespondenceAssumptions/Package`のfield射影で閉じない。
各premiseをproof bodyで使い、前半三同値はwitnessからactual closed geometryまでの構成を使う。

### SD4 — law inclusion

```lean
structure ClosedEquationalLawInclusion
    (U V : ClosedEquationalLawReading X) where
  lawMap : U.LawIndex → V.LawIndex
  selected_map : ∀ L, U.selected L → V.selected (lawMap L)
  witness_eq : ∀ L hL,
    lawWitnessIdealSheaf U L hL =
      lawWitnessIdealSheaf V (lawMap L) (selected_map L hL)
```

`lawGeneratedIdealSheaf_mono`、`lawfulClosedSubschemeMap`、そのclosed immersion、ambient triangle、
identity、compositionを固定targetとする。point-set inclusionへ弱めない。

## 問い

selected closed-equational law witnessからactual ideal sheafを生成し、
standard architecture scheme上のactual closed subschemeとlawful section factorizationまでを
同じlaw provenanceの下で構成できるか。

```text
selected closed-equational law witnesses
  -> local witness ideals I_L
  -> law-generated ideal sheaf I_U
  -> closed subscheme Flat_U(X)
  -> closed immersion Flat_U(X) -> X
  -> Lawful_U(s) iff s factors through Flat_U(X)
```

このPRDの完了対象はset-level zero locusやarbitrary ideal familyではない。
law witnessからMathlib `Scheme.IdealSheafData`とその`subschemeι`までを構成し、
後続のconormal、cohomology、deformation形式化がactual closed geometryを入力にできる基盤を作る。

## 現状診断

- `WitnessIdeal`層にはwitness coordinateから局所idealを生成する構成がある。
- `LawEquation`層にはlaw equationとrestriction compatibilityを扱うAPIがある。
- `SelectedLawWitnessIdealFamily`はlocal obstruction idealをselected idealのspanとして構成するが、
  `witnessIdeal : LawIndex -> Ideal A`を任意入力として受け取り、law witness provenanceを型に保持しない。
- `RestrictionCompatible`はlocal obstruction idealのmap inclusionを証明するが、
  scheme上のideal sheafまたはrestriction sheafとしてはbundleされていない。
- `SheafImageConstruction`はactual sheaf category imageではなく、`imageIdeal`と
  `agreesWithLocalSum` equality fieldを保持する。
- `lawfulLocus`は`PrimeSpectrum.zeroLocus`としての`Set`であり、closed subschemeを構成しない。
- `FactorsThroughLawfulLocus`はpulled idealがbottomであることの再包装であり、
  actual scheme morphismのliftやcommutative triangleを持たない。
- Mathlibには`Scheme.IdealSheafData`、`ofIdeals`、`subscheme`、`subschemeι`、
  `comap`、`map`、`subschemeMap`、`IsClosedImmersion.lift`が存在するが、現行主経路は未接続である。

課題は既存local ideal計算を捨てることではない。
law witnessから生成されたlocal idealsをstandard schemeのideal sheafへ持ち上げ、
そのclosed subschemeとfactorization universal propertyへ接続することである。

## アウトカム

完了時に次が成り立つ。

1. closed-equational law witnessが局所witness idealを生成し、そのprovenanceを保持する。
2. affine openへのrestrictionとring actionに整合するlaw-generated ideal sheafがある。
3. law universeに選ばれたwitness idealのsupremumまたはsheaf imageとして`I_U`が構成される。
4. `I_U`がactual Mathlib `Scheme.IdealSheafData`へ接続される。
5. `I_U.subscheme`と`I_U.subschemeι`がlawful closed geometryとactual closed immersionを与える。
6. `I_U.subschemeι`のkernelが`I_U`に一致し、そのrangeがlawful closed geometryを与える。
7. affine chart上で`Spec(A/I_U) -> Spec A`とのcanonical comparisonがある。
8. lawfulness、ideal pullback zero、actual factorizationが双方向に接続される。
9. law universe inclusionに対するideal inclusionとlawful closed subschemeの比較射がある。
10. law dataの違いがclosed geometryを変える非退化finite exampleがある。
11. conormal constructionが後続タスクで`I_U`から直接開始できるAPIを持つ。

## 採否規律

- 数学本文はread-onlyとし、`docs/aat/algebraic_geometric_theory/**`を変更しない。
- 対象は本文のclosed-equational lawであり、open、constructible、descent、temporal、stacky lawをidealへ押し込まない。
- `I_U`はselected law witnessから生成する。arbitrary ideal familyを入力したpackageだけで完成としない。
- standard scheme上のidealにはMathlib `Scheme.IdealSheafData`を使用またはcomparison theoremで接続する。
- lawful locusをset、support、point predicateだけで完了としない。
- factorizationはactual scheme morphismとcommutative triangleで表す。
- `FactorsThroughLawfulLocus`のように結論を同じ命題で包み直すrepackageを新主定理にしない。
- target statementと参照definitionは、このPRDの`Statement Design`節を不変入力とする。

## 改修要求

### R0 — witness route・Mathlib API・fixed statementの確定

- tracking Issueに対象main commitを固定する。
- `WitnessIdeal`、`LawEquation`、`SelectedLawWitnessIdealFamily`、
  `RestrictionCompatible`、`SheafImageConstruction`、`LawfulLocus`のsignatureと利用箇所を棚卸しする。
- Mathlib `Scheme.IdealSheafData`、affine-open ideals、restriction、`subscheme`、
  `subschemeι`、`IsClosedImmersion`、`comap`、`map`、`subschemeMap`、quotient `Spec` APIを確認する。
- material premiseを本文由来、放電済み、未放電へ分類する。

### R1 — closed-equational law witness provenance

- selected law universeのうちclosed-equational witnessを型付きで選ぶAPIを定義する。
- 各witnessをtyped coordinate、law equation、local sectionへ接続する。
- local witness idealをwitness equationsの`Ideal.span`または既存`WitnessIdeal` constructorから生成する。
- arbitrary `Ideal A`をprimary inputとして受け取らず、生成idealへのforgetful APIだけを提供する。
- law、witness、context、coefficient algebraのprovenanceをconstructor/characterization theoremで追跡できるようにする。

### R2 — affine-open ideal system

- standard schemeの各selected affine openにlaw-generated local idealを割り当てる。
- open immersionまたはaffine-open inclusionに沿うrestriction mapがwitness idealを保存することを証明する。
- identity、composition、pair overlapでの一致を証明する。
- existing `RestrictionCompatible.map_localObstructionIdeal_le`を、law-generated source/targetから得るconstructorまたは補題として再利用する。
- restriction compatibilityをarbitrary fieldとして入力するだけの主経路を作らない。

### R3 — law-generated ideal sheaf

- affine-open ideal systemからMathlib `Scheme.IdealSheafData`を構成する。
- 利用可能な場合は`Scheme.IdealSheafData.ofIdeals`とそのGalois insertion APIを使う。
- 各lawのideal sheaf`I_L`を構成し、selected law universeに対するsupremum
  `I_U = ⨆ L, I_L`をMathlib complete lattice上で定義する。
- direct sum / coproductからstructure sheafへのmapが利用可能な場合は、
  categorical imageとsupremum constructionの一致を証明する。
- objectwise local sumと`I_U.ideal U`の一致条件を具体定理にする。
- `SheafImageConstruction.imageIdeal`とequality fieldをactual sheaf imageの代用にしない。

### R4 — affine lawful closed geometry

- affine chart`Spec A`とlaw-generated ideal`I_U`からquotient ring`A / I_U`を構成する。
- induced scheme morphism`Spec(A/I_U) ⟶ Spec A`を構成する。
- actual `IsClosedImmersion` instanceまたはtheoremを得る。
- Mathlib `IdealSheafData.subscheme`によるclosed subschemeとのcanonical isoを証明する。
- `subschemeι`のkernelがlaw-generated ideal sheafに一致することをMathlib APIから証明する。
- closed immersionのrange/supportがlawful closed setと一致することを証明する。
- underlying point imageが`PrimeSpectrum.zeroLocus I_U`と一致することを証明する。
- existing set-level `lawfulLocus`をこのunderlying-point theoremへ接続する。

### R5 — global lawful closed geometry

- standard architecture schemeのunderlying Scheme上でlaw-generated`I_U : X.IdealSheafData`を構成する。
- lawful closed geometryを`I_U.subscheme`、closed immersionを`I_U.subschemeι`として定義する。
- chart restrictionがlocal affine lawful closed geometryとcanonical isoで一致することを証明する。
- pair overlapとtriple compatibilityをideal sheaf restrictionから導く。
- AAT decorationをclosed subschemeへrestrictionし、underlying closed geometryと同じlaw provenanceを保持する。

### R6 — actual factorization theorem

- architecture sectionまたはtest scheme morphism`s : T ⟶ X`に対し、semantic lawfulnessを
  selected law universeの各lawが`s`上で成立することとして定義する。
- witness equationsのvanishingは`WitnessVanishes_U(s)`などの別predicateとし、
  semantic lawfulnessまたはideal pullback zeroの別名にしない。
- `I_U ≤ s.ker`、`I_U.comap s = ⊥`または同値なMathlib ideal-sheaf statementへ接続する。
- lawfulnessから`I_U.subscheme`へのactual liftを`IsClosedImmersion.lift`または同等のuniversal propertyで構成する。
- liftと`subschemeι`のcompositionが`s`に等しいことを証明する。
- actual factorizationからideal pullback zeroとlawfulnessを逆向きに証明する。
- liftの一意性をclosed immersionのmonomorphismまたはMathlib universal propertyから証明する。
- 数学本文 定理11.1のobstruction soundness、obstruction completeness、axis exactness、
  witness coverage、U-adequate cover、sheaf descent、ring restriction compatibilityを
  同じ量化対象で本文由来material premiseとして明示し、proof bodyで実際に使う。
- 上記premiseの下でsemantic lawfulness、witness vanishing、ideal pullback zero、actual factorization、
  obstruction valuation zero、required signature axes zeroの本文どおりの同値を証明する。
- witness vanishingからsemantic lawfulnessへのsoundness/completenessをopaqueなadequacy fieldから射影しない。
- 結果を次の双方向同値として接続する。

```text
Lawful_U(s)
  <-> WitnessVanishes_U(s)
  <-> s^* I_U = 0
  <-> Nonempty { t : T -> Flat_U(X) // t ≫ ι_U = s }
  <-> omega_U(s) = 0
  <-> required Sig_U axes vanish
```

### R7 — law universe inclusion

- selected closed-equational law universe inclusionをtyped dataとして定義する。
- `U ⊆ V`から`I_U ≤ I_V`をsupremumの普遍性で証明する。
- ideal inclusionからclosed subscheme間のactual morphismを`subschemeMap`または同等のMathlib APIで構成する。
- comparison morphismがactual closed immersionであることを証明する。
- morphismと各closed immersionの可換性、identity、compositionを証明する。
- point-set inclusionだけでfunctoriality完成としない。

### R8 — 非退化finite examples

- 非自明coefficient ringと`⊥`でも`⊤`でもないlaw-generated idealを持つaffine exampleを構成する。
- quotient spectrum、closed immersion、underlying zero locus、factorization theoremを同一law inputから発火させる。
- 同一ambient scheme上でlaw dataだけが異なり、`I_U < I_V`とlawful closed subschemeが異なるpairを構成する。
- lawful closed subschemeがnonemptyでambient schemeと同一でないことを証明する。
- lawful sectionとunlawful sectionの双方をactual morphismとして示す。
- arbitrary idealを直接入力した例、zero idealだけの例、empty locusだけの例を主証拠にしない。

### R9 — legacy comparison・統合・監査

- `SelectedLawWitnessIdealFamily`からnew law-generated routeへの変換は、
  witness provenanceとrestriction proofを追加で示せる場合だけ提供する。
- set-level `lawfulLocus`とnew closed subschemeのunderlying point setの一致を証明する。
- old `FactorsThroughLawfulLocus`をactual factorization theoremの証拠に使わず、
  必要ならdeprecationまたはcomparison対象として残す。
- 新moduleを`Formal/AG.lean`へ接続する。
- target declarationsとexamplesをstatement contractsとaxiom auditへ追加する。
- Lean theorem indexとproof-obligation台帳を必要範囲で同期する。

## Acceptance Criteria

- [ ] AC1: executable contractがlaw-generated ideal sheaf、closed immersion、full correspondence、law inclusion、nontrivial exampleの実装signatureを直接参照する。
- [ ] AC2: 各local witness idealがselected closed-equational law witnessから生成され、law/context/coefficient provenanceを追跡できる。
- [ ] AC3: local idealsがaffine-open restrictionに整合し、identity/composition/pair-overlap compatibilityが証明される。
- [ ] AC4: `I_U`がactual Mathlib `Scheme.IdealSheafData`として構成され、selected law ideal sheavesのsupremumまたはactual image provenanceを持つ。
- [ ] AC5: objectwise local sumとideal sheaf sectionの一致が、明示された条件の下で証明される。
- [ ] AC6: affine lawful geometryがactual `Spec(A/I_U) ⟶ Spec A`とclosed immersion proofを持つ。
- [ ] AC7: global lawful geometryが`I_U.subscheme`と`I_U.subschemeι`として構成される。
- [ ] AC8: `I_U.subschemeι.ker = I_U`とrange/supportのlawful closed set characterizationが証明される。
- [ ] AC9: chart restrictionがlocal affine lawful closed geometryとcanonical isoで一致し、pair/triple overlap compatibilityとclosed subschemeへのglobal decoration restrictionが証明される。
- [ ] AC10: semantic lawfulnessをwitness vanishingまたはideal vanishingの別名にせず、本文 定理11.1と同じmaterial premiseの下でsemantic lawfulness、witness vanishing、ideal pullback zero、actual factorization、obstruction valuation zero、required signature axes zeroが同値であり、factor liftのtriangleと一意性が証明される。
- [ ] AC11: underlying point imageがexisting `PrimeSpectrum.zeroLocus` readingと一致する。
- [ ] AC12: law universe inclusionからideal inclusionとclosed subscheme間のactual closed immersionが構成され、ambient triangle、identity、compositionが証明される。
- [ ] AC13: 非退化finite pairが同一ambient scheme上でstrict ideal inclusion、proper nonempty closed geometry、factorization yes/noを示す。
- [ ] AC14: 新主経路にarbitrary supplied ideal、自由な`Prop` slot、結論相当certificate、未使用material premiseがない。
- [ ] AC15: 新definitionにconstructor/destructor/ext/characterization/comparison APIがあり、conormal等の後続利用者がdefinition unfoldに依存しない。
- [ ] AC16: target declarationsとexamplesがstandard axiomsのみを使用し、statement contractsとaxiom auditがgreenである。
- [ ] AC17: `docs/aat/algebraic_geometric_theory/**`に変更がなく、Lean台帳だけが必要範囲で同期される。
- [ ] AC18: `math-lean-review`の4本の独立査読がすべて`No major findings`である。

## Failure Contract

次は完了ではなく失敗である。

- arbitrary `Ideal A` familyを受け取り、law-generated idealと呼ぶpackage。
- `imageIdeal`と`agreesWithLocalSum` equality fieldだけをactual sheaf imageと呼ぶこと。
- `PrimeSpectrum.zeroLocus`のSetだけでclosed geometry完成とすること。
- ideal pullback zeroを別structureへ同じ形で包み、actual factorizationと呼ぶこと。
- semantic lawfulnessをwitness vanishingまたはideal pullback zeroとして定義し、本文 定理11.1のsoundness/completeness等を消すこと。
- closed immersion、factorization lift、commutative triangleを結論相当fieldから射影すること。
- open、temporal、descent、stacky lawを根拠なくideal sheafへ押し込むこと。
- zero ideal、empty locus、all-identity morphismだけで主経路を発火させること。
- implementation convenienceを理由に数学本文のlawfulness/factorization claimを弱めること。

## 停止条件

- 数学本文のclosed-equational law geometryにLean実装と独立した反例、型不整合、well-definedness欠陥が見つかった。
- fixed statementを弱める、material premiseを増やす、参照definitionを結論相当に変更する必要が生じた。
- Mathlib `IdealSheafData`から本文に必要なclosed subschemeまたはfactorizationを構成できない。
- law witnessからideal sheafまでのrestriction compatibilityを証明できず、arbitrary ideal familyが必要になる。
- nontrivial law-sensitive finite pairが構成できず、zero/empty examplesだけが残る。

停止報告には、該当AC、最小の反例またはAPI blocker、試したMathlib route、未放電仮定、
本文改訂の要否、代替となるstandard closed geometry設計を記録する。

## Non-goals

- open、constructible、descent、temporal、stacky lawの一般幾何。
- conormal sheaf`I/I^2`、short exact sequence、Čech connecting class、first-order lift。
- G-07または他のResearch成果の本体蒸留。
- derived zero locus、cotangent complex、`Ext^1`、higher obstruction。
- coverage refinement、coefficient base changeを含む一般reading functoriality。
- 数学本文へのLean status、Issue、PR、declaration名の追加。

## 検証

検証手順と実行主体は`AGENTS.md`の「よく使う検証」「PR前の確認」と
`docs/aat/guideline.md`を直接適用する。task固有の追加検査は、witness provenance、
`IdealSheafData`、`subschemeι.ker`、actual factorization一意性、full Lawfulness-Ideal Correspondence、
strict law inclusion exampleをstatement contractsとaxiom auditが直接参照していることの確認である。
