# G-115-aat-upper-stage-lift — 上段 mate の整合障害と orbit intertwining

- `id`: `G-115-aat-upper-stage-lift`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: Gr4 完遂 gate 第三項(O10–O11)。義務台帳は G-116、設計の source note は n1007 §3–§5。G-114 revision 3 の `ActiveRefinementBCContext` が与える二つの core route と canonical mate を、G-109 の二段 geometry transport diagram 上へ持ち上げる際の整合障害を扱う。本カードの成果物は G-116 に、整合した上段 regime、actual lifted mate component family、`UpperStageExchangeExact` を供給する。G-116 はこれらを新設しない。
- `predecessor`: G-114 revision 3(完遂済み。active refinement context と core mate)、G-109(完遂済み。Gr3 two-layer transport・upper defect cochain・reselection orbit)、G-108(完遂済み。geometry の共変 transport)、G-110(完遂済み。pointed pullback・reindexing functor)、G-106(完遂済み。defect / orbit 語彙)。
- `tracking issue`: [#4250](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4250)
- `source note`: [n1007](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)(§3 義務台帳、§4 は revision 1 の設計元。global upper lift 部分は下記 disposition で superseded)、[n1001](../../docs/note/n1001_atom_is_all_you_need_discussion.md)(§3.3 塔)、[G-109](G-109-aat-cross-stage-coherence.md)、[G-110](G-110-aat-doctrine-fiber-product.md)、[G-114](G-114-aat-refinement-base-change.md)。
- `research aim`: G-114 の core-level Beck–Chevalley mate に対し、route ごとに与えられた G-109-qualified geometry diagram と component lift candidates が一つの上段 mate をなすための有限整合障害を構成し、その消滅を edge / path / two-cell の三水準で特徴付ける。非可逆な mate では二つの upper orbit の間に関数を捏造せず、actual reselection と raw-defect cochain の intertwining relation を証明する。mate が componentwise `IsIso` のときだけ conjugation による orbit 同値へ昇格する。
- `core tension`: G-114 の reverse refinement functor は cartesian reindexing に由来する反変作用である一方、G-108 `geomTransportAlongHom` は package hom に沿う共変作用である。G-114 の target geometry から reverse route の geometry object を G-108 で自動生成する向きの射は存在しない。また一般の `η : G ⟶ H` は `Aut (G X) → Aut (H X)` を誘導せず、これは `η` が自然同型の場合に conjugation で初めて得られる。従って revision 1 の global lift と無条件 orbit map は型付かない。本カードは routewise geometry objects と component lift candidates の**供給後に残る整合問題**を正面から定理化する。component の存在自体を放電したとは数えず、G-116 の O19 にこの適用域を残す。
- `rival`: fibred 2-category における pseudonatural transformation の lift と modification obstruction。差は、AAT の actual two-layer transport、actual upper defect cochain、reselection orbit を使い、非可逆時の lax naturality と可逆時の orbit 同値を同じ Lean package で固定する点に置く。
- `claim scope`: 固定した carrier `U`、G-114 の active context、その target pointed fiber を根に持つ finite connected presentation、固定係数の `TwoLayerTransportData` の上で語る。carrier change、係数 base change、site / cover の変更、任意 raw refinement からの geometry route 生成、component lift の無条件存在、段射影方向の effectivity 反射、無限 diagram は主張しない。
- `capability categories`: base-change、tower-lift、coherence-obstruction、relational-naturality。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: component candidate の field に edge naturalityを入れる、coherence predicate の定義展開だけを主成果とする、非可逆 mate から automorphism map を作る、core pushforward だけで upper cochain theorem を閉じる、離散 diagram、constant orbit、`Classical.em` だけの正負 witness は完了扱いしない。有限障害の path / two-cell propagation、actual upper cochain の intertwining、非恒等発火を theorem body が実消費しなければならない。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、停滞なら `target-blocked`、反証なら `target-refuted`、全完了条件と final review を満たした場合だけ `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。
- `frontier`: component lifts 自体の存在障害、refinement geometry cleavage の建設、無限 diagram、係数 base change、G-113 diagnostic equivalence との合成。

- `revision disposition`:
  - revision 1 は任意の `ActiveRefinementBCContext` と任意の `TwoLayerTransportData` の間の semantic connection、ならびに reverse core route を geometry route へ送る反変 primitive を欠き `goal-defect` となった(Issue #4250 comment `5462812441`)。
  - revision 2 初稿の G-108 canonical push 案も、共変 transport を反変 route に使用しており型付かない。また low-level compatibility が完成した `GeomReadHom` と naturality を実質的に premise 化し、非可逆 mate に無条件の orbit map を要求していたため棄却する。
  - 現 revision 2 は旧 global 存在主張と同じ強さを主張しない。人間承認の改訂として、component-supply-relative な coherence obstruction と、非可逆時にも意味を持つ relational naturality を O10–O11 の fixed target とする。旧義務の帰趨は G-116 の履歴台帳に残す。

- `target theorem`: **Upper-Mate Coherence Obstruction and Orbit Intertwining Theorem**。G-114 の `ctx : ActiveRefinementBCContext` の上で:
  1. **(a) raw candidate problem と有限整合障害**: `UpperMateCandidateProblem ctx` を定義する。これは有限 index category `P`、distinguished root、root から全 vertex への zigzag path、同一係数 object、G-114 の二 core route を underlying diagram とする二つの G-109-qualified `TwoLayerTransportData P U`、および各 vertex の `GeometryTotalHom` candidate を持つ。二 route の geometry packages は各々の core route object へ正しく射影し、各 candidate は `ctx.mate.app` の対応 component へ射影する。各 raw edge は target fiber 内の射で係数写像は恒等とする。root candidate の core 射影は transport 後の `ctx.mateAtTarget` と一致する。**candidate structure に edge naturality、path coherence、two-cell coherence、`IsIso`、orbit law を入れない。** routewise geometry data と component candidates は `direction-hypothesis` であり、それらの存在を O10 の放電に数えない。

     各 edge `e : i ⟶ j` に対し、base edge の後に `η_j` を通る合成と、`η_i` の後に pulled edge を通る合成を parallel pair として保持する `UpperMateNaturalityDefect problem e` を構成する。全 pair が等しいことを `UpperMateObstructionVanishes problem` と定義し、単なる abbreviation だけで完了としない。
  2. **(b) exact coherence theorem と Gr3 接続**: 次を証明する。
     - edge obstruction の消滅 iff candidate family が有限 diagram 間の `FiniteUpperMate` をなす。
     - edge obstruction が消滅すれば、独立に構成した任意 path の二合成が一致し、nil / append lawを満たす。逆に length-one path lawから edge 消滅を回収する。
     - G-109 の unitor / compositor と authored two-cell comparator を実消費して、path representatives と two-cell pasting に対する一致を証明する。
     - vertex ごとの base / pulled automorphism family による gauge change を、両 route の edge と component candidates を同時に conjugate する作用として定義する。candidate problem と defect への作用、identity / composition law、defect の equivariance、coherence locus の保存を証明し、obstruction vanishing が gauge quotient 上で well-defined であることを与える。

     `CoherentUpperStageRegime ctx` は obstruction-vanishing candidate problem の subtype とし、下流 G-116 の量化域を固定するためだけに用いる。これを引数にした projection を O10 の証明とは数えず、O10 の放電は任意の raw candidate に対する edge iff path iff `FiniteUpperMate`、two-cell、gauge-equivariance theorem で行う。regime からは二つの actual `TwoLayerTransportData` と、vanishing theorem が生成する lifted mate component familyを返す。root-connectedness を path theorem と root proof-use に使用し、root だけが孤立した witness を排除する。
  3. **(c) actual orbit intertwining と exactness 時の同値**: coherent regime の base / pulled `TwoLayerTransportData` に対し、既存の `InUpperReselectionOrbit` と `upperRawDefectCochain` を直接使用する。base reselection `rBase` と pulled reselection `rPulled` が各 lifted mate component と可換することを `UpperReselectionsIntertwined regime rBase rPulled` と定義する。この relation の下で raw-defect cochain の全 component が同じ mate と intertwine すること、relation が identity・vertical composition・path concatenation で閉じること、対応する actual orbit membership が paired relation として保存されることを証明する。

     `UpperStageExchangeExact regime : Prop` は全 lifted mate component が `IsIso` であることと定義する。この条件下でのみ componentwise conjugation と逆 conjugation を構成し、両側 inverse law、`upperRawDefectCochain` commuting、actual orbit の direct-image equality / equivalenceを証明する。無条件の reselection function、`Set.MapsTo`、orbit equivalence は主張しない。
  4. **(d) 正負 witness と非退化発火**: 同一係数、root-connected、少なくとも一つの nonidentity strong edge と nonidentity upper reselection を持つ named coherent problem を構成し、path / two-cell theorem と cochain intertwining が実際に発火する component を示す。また active context と両 route の nonempty qualified geometry data、全 vertex の component candidates を持ちながら、ある固定 edge の parallel pair が異なる named incoherent problem を構成し、zero-locus 非所属を具体評価する。負例は G-108 の向きが異なる `not_hGeom` fixture に依存しない。正負 witness は root component と nonidentity edge が同一 connected component にあることを示す。

- `target theorem scope`: Lean 置き場所は `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新 module。G-108〜G-110、G-114 の reviewed module は参照のみ。受理 Lean 宣言は premise / review / merge gate 通過までは static evidence に留まる。
- `target proof artifacts`: `UpperMateCandidateProblem`、edge parallel pair と `UpperMateObstructionVanishes`、`FiniteUpperMate`、edge iff path iff finite-mate、two-cell pasting、gauge action / orbit / zero-locus theorem、`CoherentUpperStageRegime`、`UpperReselectionsIntertwined`、actual raw-cochain intertwining と orbit paired preservation、`UpperStageExchangeExact` 条件付き conjugation / orbit equivalence、connected positive / incoherent negative witness、report `research/reports/G-115-aat-upper-stage-lift.md`。
- `target proof strategy`: F0 で G-114 core route object、G-109 two-layer data、`GeometryTotalHom` の射影等式、edge parallel pair の signature を固定する。K0 edge obstruction と finite mate iff、K1 path / two-cell / gauge、K2 actual cochain intertwining、K3 `IsIso` 下の conjugation equivalence、K4 正負 witness と監査。G-109 の comparator / unitor / compositor と upper cochain theorem は theorem body 内の proof-use を declaration map に残す。
- `target theorem completion criteria`: 全 artifact が sorry なしで ResearchLean に受理され、axiom / placeholder audit が clean であること。下記 ledger の `discharge-required` を放電し、premise provenance、proof-use、structure-field escape、route integrity、nonvacuity を監査すること。各実装 PR の fixed-head `$review-pr` と、completion candidate の独立 `$math-lean-review` 4査読全 `No major findings` を通過した場合だけ完了とする。Research aggregate / full build は行わず、direct dependency DAG と focused file check のみを使う。
- `target premise discharge policy`: `ActiveRefinementBCContext`、routewise G-109-qualified data、component lift candidates は残せる。ただし後二者は `direction-hypothesis` であり、component existence の証明とは数えない。edge/path/two-cell coherence、gauge zero-locus、cochain intertwining、conditional conjugation、正負 witness を premise field に移すことは禁止する。

**Target material premise ledger**

| premise | class | provenance / proof-use / discharge |
|---|---|---|
| G-114 active context | ambient | PR #4246 fixed head `8f7ad8bf`、merge `3d26d993`。二 core route、canonical mate、root component に使用する。geometry component や coherence は含まない |
| G-109 two-layer route data | direction-hypothesis | reviewed Gr3 raw datum。strong qualifications、two-cell、comparator の provenance。二 route の geometry realization は caller supply であり、存在放電とは数えない |
| vertex component lifts | direction-hypothesis | `GeometryTotalHom` family と core projection equalityだけ。edge/path/two-cell naturality、`IsIso` を含めない。component existence は本 target の外 |
| fixed coefficient / fiber edges | ambient | 全 geometry packages の係数を同一 object に固定し、edge coefficient map = identity、core projection = target fiber morphism を型で保持する |
| edge obstruction iff finite mate | discharge-required | conclusion相当。candidate field へ移さず、両方向の theorem bodyで parallel composites を使用する |
| path / two-cell / gauge coherence | discharge-required | G-109 unitor・compositor・comparator を実消費し、length-one converse、defect equivariance、quotient 上の well-definedness を含む |
| actual cochain intertwining | discharge-required | `upperRawDefectCochain` と `InUpperReselectionOrbit` を直接使用する。core-only proof を禁止する |
| conditional orbit equivalence | discharge-required | componentwise `IsIso` から conjugation と逆写像を構成する。無条件 map を premise にしない |
| connected positive / incoherent negative witnesses | discharge-required | root と nonidentity edge の connectedness、nonconstant orbit firing、固定 edge の非零 defect を具体評価する |

**受入禁止**

- candidate / regime structure に naturality、coherence、orbit law、`IsIso` を格納して projection だけで theorem を閉じる。
- G-108 の共変 push を G-114 reverse route の生成と呼ぶ。
- 非可逆 mate から一方の full automorphism group / orbit への関数を定義する。
- extent / membership iff、`Subsingleton`、empty diagram、identity-only fixture だけで O10 / O11 を放電する。
- component-supply-relative theorem を universal upper lift と記録する。

**停止条件**

- `goal-defect`: candidate problem の core projection equations または edge parallel pair が既存 category signatures で型付かない、あるいは O10/O11 をさらに conclusion-equivalent premise なしでは述べられない。
- `target-refuted`: fixed positive witness が構成不能、edge/path/two-cell iff または cochain intertwining に反例がある。
- `target-blocked`: direct dependency の未 port / 未証明により focused check が停止し、exact declaration と最小 dependency DAG を tracking Issue に固定した場合。
- `target-theorem-proved`: 全 artifact、正負 witness、監査、PR merge、台帳同期、final 4査読を完了した場合だけ。

- `stop reason`: なし(active)。
- `next action`: F0 で `UpperMateCandidateProblem` と edge parallel pair の Lean signature を固定し、component candidate に naturality field が混入していないこと、G-114 mate projection と G-109 route edge の二合成が同じ Hom 型に入ることを確認する。
