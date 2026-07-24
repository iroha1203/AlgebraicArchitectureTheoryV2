# G-aat-quality-surface-07 — law-generated conormal first-order descent theorem の証明

- `id`: `G-aat-quality-surface-07`
- `status`: `completed`
- `completion result`: `target-theorem-proved`。固定artifact、完了条件、4本の独立math / Lean査読、PR #3278のCI、report、tracking Issueの同期を完了。
- `completed at`: `2026-07-12 JST`
- `priority`: `high`
- `research mode`: `target-theorem`
- `tracking issue`: [#3246](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3246) closed as `COMPLETED`.
- `completion report`: [research/reports/G-aat-quality-surface-07.md](../reports/G-aat-quality-surface-07.md)
- `mainline distillation`: `2026-07-25` C6([#3767](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3767))で
  large-coefficient 系 statement family(G-07 対応表の reuse/generalize/specialization 全行+Boolean-circle
  zero/nonzero conormal witness 対)を `Formal/AG/SemanticRepair/Conormal/` へ本体内再構成として蒸留し、
  `unported (Research-proved)` を解消。宣言名・statement は Research 原本と同一
  (namespace root のみ `AAT.AG.SemanticRepair.Conormal` へ変更)。small-cover 版
  (`LawGeneratedConormalDescent.lean`)は R0 note §7 のとおり補助参照のまま Research 側に残る。
- `source note`: [docs/note/aat_descent_theorem_value_and_route.md](../../docs/note/aat_descent_theorem_value_and_route.md)
- `predecessor / successor relation`: G-02 / G-05 / G-06(SAGA)を証明済みの地盤として使う。G-07はlaw-generated abelian first-order descentを担当し、G-03は一般generated nerve、G-04はideal-power higher stagesとnonabelian / higher / stacky / universalityを担当する。
- `research aim`: law witnessから`I`、`O/I^2 -> O/I`、`ConDef = I/I^2`を生成し、lawful sectionごとのconnecting classがactual global first-order liftの存在をちょうど判定することをLeanで証明する。
- `core tension`: 現行SAGAではlaw satisfactionはdegree zeroに現れる。G-07では同じlawful sectionのlocal liftsの差を`I/I^2`へ戻し、class zeroから形式primitiveではなくactual global sectionを構成する。
- `rival`: 一般lifting machineryやsupplied coefficient / effectivityを持つad hoc packageとの差は、Atom / law入力から係数・class・lift witnessを生成する点に置く。ADL・静的解析・AI reviewとの比較強度はrelated-workと同一入力比較で検証する。
- `claim boundary`: finite/small atom-generated AAT site、base `W`、既存finite-poset generated cover `U`、law witness data、generated ideal / quotient / kernel sheaves、lawful sectionとlocal lifts、cover-relative additive Cech complex、actual sheaf descent、semantic first-order repair representationを対象とする。
- `capability categories`: law-generated-coefficient、conormal-sheaf、connecting-class、first-order-effectivity、actual-global-lift、lift-torsor、law-sensitive-witness、semantic-repair-representation。
- `threshold policy`: SCOREは使わない。runtime stateはtracking Issueに置き、固定statementとcompletion criteriaだけで完了判定する。
- `portfolio constraint`: generic lift descent、law-generated sheaf列、zero iff global lift、lift torsor、law-sensitive finite witness対、semantic representationの六面をLean artifactで接続する。
- `phase boundary criteria`: 未証明なら`target-proof-checkpoint`、反証なら`target-refuted`、全完了条件とfinal reviewを満たした場合だけ`target-theorem-proved`とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各cycleはproof obligation deltaで評価する。
- `dullness filter`: generic theoremだけ、objectwise `Ideal.Cotangent`だけ、defect zero section、`H^1 = 0`だけ、primitiveだけ、supplied effectivity、退化coverだけ、first-orderからfull repairへの過大化を弾く。
- `frontier`: short-exact lift descent、ideal-power sheaves、conormal sheaf、lawful-locus factorization、finite-poset cover、law-sensitive finite ring witness、semantic first-order repair representation。

- `target theorem`: **Law-Generated Conormal First-Order Descent Theorem**。law witnessから生成した
  `0 -> ConDef -> Q_1 -> Q_0 -> 0`(`Q_0 = O/I`、`Q_1 = O/I^2`、`ConDef ~= I/I^2`)とcover `U`を固定する。
  locally liftableなlawful section `s : Q_0(W)`に対し、local liftの差がchoice-independentな
  `partial_U(s) : CechH1(U, ConDef)`を定め、
  `partial_U(s) = 0 <-> exists S_1 : Q_1(W), map(S_1) = s` が成り立つ。
  lift fiberは非空なら`ConDef(W) ~= H^0(W, ConDef)`のtorsorであり、representation theoremを通じて
  semantic first-order repairへ移送する。`CechH1(U, ConDef) = 0`は局所可解な全problemに対する系とする。
- `target theorem boundary`: Lean置き場所は`research/lean/ResearchLean/AG/QualitySurface/LawGeneratedConormalDescent.lean`または同directoryのsupport file。G-07の完了面はcover-relative first-order theoremとsemantic first-order representation。ideal-power higher stagesは後続theorem family、G-04はnonabelian / higher / stacky / universality、runtime extractionはtooling PRDへ接続する。
- `target proof artifacts`: generic `ShortExactLiftProblem` / connecting-class / zero-iff-lift / torsor theorem、law-generated ideal・quotient・kernel sheafとexactness、`LawfulReadingRepresentation`、`SemanticFirstOrderRepairEquiv`、law-sensitive zero / nonzero finite witness対、`lawGeneratedConormalFirstOrderDescent_package`、`H^1 = 0`系、report `research/reports/G-aat-quality-surface-07.md`。
- `target proof strategy`: D0 generic additive lift descent -> D1 law-generated sheaf列 -> D2 existing finite-poset cover上のconormal theoremとfinite witness -> D3 semantic representation。設計根拠はsource note §2 / §5を参照し、固定statementと完了条件は本カードを正本とする。
- `target theorem completion criteria`: 全artifactがsorryなしで`ResearchLean`に受理され、axiom / placeholder auditがcleanであること。下記ledgerの`discharge-required`をinput-generated theoremまたはLean finite witnessで放電し、T3 auditでcertificate provenance、proof-use、structure-field escape、route integrityを監査すること。Lean / report / tracking Issueを同期し、final review packetを作り、`$math-lean-review research/goals/G-aat-quality-surface-07.md G-aat-quality-surface-07`の4査読がすべて`No major findings`であること。
- `target premise discharge policy`: 入力幾何とlocal solvabilityだけを残せる。exactness、sheaf effectivity、Cech adequacy、lawful reading、semantic representation、nonvacuityはcompletionまでに生成・証明する。certificateやstructure fieldを受け取るだけでは放電と数えない。
- `target material premise ledger`:
  - `site / base / Atom-law vocabulary`: `ambient-boundary`。artifactは不要、provenanceはselected AAT data。cover・restriction・section構成に使い、global liftやclass zeroを含めない。
  - `local solvability`: `direction-hypothesis`。artifactは同じ`s`へのexplicit local lift family、provenanceはtheorem input。overlap差の生成に使い、global compatibilityを含めない。
  - `ideal / quotient / kernel sheaves and exactness`: `discharge-required`。law witness由来のconstruction / naturality / kernel comparisonを証明し、kernel差とtorsor actionに使う。zero-iff-liftをfieldへ入れない。
  - `sheaf effectivity / Cech adequacy / cover provenance`: `discharge-required`。generated coverとquotient sheafから証明し、cocycle・choice-independence・actual gluingに使う。global liftをcertificate fieldへ入れない。
  - `lawful reading / semantic first-order repair representation`: `discharge-required`。Atom / law / semantic dataから両representationを構成し、semantic corollaryで使う。zero section、class zero、global repair existenceを定義へ入れない。
  - `law-sensitive nonvacuity witness`: `discharge-required`。同一cover / ambient ringでlaw idealだけが異なるzero / nonzero対をLean計算し、route integrity auditに使う。target theoremを前提にしない。
  - `class zero / global lift / H^1 zero`: `direction-hypothesis`。discharge artifactは不要、provenanceはtarget statementのantecedent / conclusion。completion premiseにしない。
- `target anti-weakening rule`: primary equivalenceをgroup vanishing、片方向、primitive、compatible-family predicate、conditional wrapperへ弱めず、結論相当dataをargument / typeclass / field / certificate / opaque membershipへ移さない。first-orderをfull semantic repairと言い換えない。
- `target route integrity gate`: ideal・cover・coefficient・section・representation・finite witnessのprovenanceをAtom / law入力、canonical construction、universal property、generated cover、review済みpredecessorへ追跡する。zero / singleton / identityだけの発火、one-way-as-equivalence、proof後のGOAL読み替えをcompletionに使わない。
- `target failure policy`: primary equivalenceまたは必須semantic representationのLean反例は`target-refuted`。別係数が必要ならGOAL改訂案を返す。同じblockerが二cycle続けば`target-blocked`。first-order成立後のfull repair失敗は後続ideal-power stageまたはG-04へ送る。
