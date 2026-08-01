# G-101-aat-atom-foundation — Atom 輸送の opcartesian lift 定理

- `id`: `G-101-aat-atom-foundation`
- `status`: `draft`
- `priority`: `high`
- `research mode`: `target-theorem`
- `tracking issue`: 未起票
- `source note`: [docs/note/atom_is_all_you_need_discussion.md](../../docs/note/atom_is_all_you_need_discussion.md)
- `research aim`: doctrine の射の圏 `Doct_U` と pointed 圏 `ExtInst_U` を立て、
  exact 射に沿う package 輸送を opcartesian lift として構成・特徴づけ、輸送データ
  (`SignedExactCoreReadingHom` の全 field)が一本の構成から供給されることを示す。
- `core tension`: 上層の輸送データ型は field としては実装済みだが、それが底の
  射から**生成される標準構成**なのか、単に手で与えられるデータの束なのかは
  未決である。opcartesian 普遍性が立てば transport は選択データから「底の射が
  誘導する canonical 構成」に変わり、「Grothendieck 的」が装置名になる。
  refinement 射では等式が包含に弱まり lift が存在しない — その失敗が要求する
  追加データ(新規 Atom の composition / equation 供給)の正体を特定できるかが
  非自明性の核。
- `rival`: institution 理論の (theoroidal) comorphism、fibred category の一般論
  (mathlib の `CategoryTheory.Fibered` 系を含む)、既存
  `SignedExactCoreReadingHom` 単体。差は「Atom 抽出 doctrine を底とする具体的
  fibration を立て、正例だけでなく refinement 負例で lift の失敗段まで特定する」
  点に置く。一般論の instantiation で済む部分は流用してよいが、`Doct_U` の射・
  transport 構成・負例は AAT 入力から生成する。
- `claim boundary`: 固定した一般 carrier `U : AtomCarrier`、`ExtractionDoctrine U`
  とその exact 射・refinement 射、pointed instance `(D, s)`、`AATCorePackage` と
  既存 core reading hom、witness 用の `FiniteModel` carrier 具体化を対象とする。
  geometry / class 段への lift、nerve 接続、ambient joint-kernel quotient `q_L`、
  descent 反例、blame coboundary、carrier を動かす主張、輸送の段横断合成
  (擬関手的整合)、doctrine 圏の fiber product(base change)は含めない。
- `capability categories`: doctrine-morphism、opcartesian-transport、
  lift-uniqueness、refinement-obstruction、component-derivation。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に置き、
  固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: 証明対象4点(構成・一意性・refinement 負例・成分供給)
  の四面がすべて Lean artifact で接続されること。正例だけ、または負例だけで
  完了扱いしない。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証なら
  `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: identity 射だけでの発火、退化 doctrine(空 `Source`・
  空 family)だけの例、opcartesian 性を伴わない transport 関数の定義だけ、既存
  `extraction_eq` の再ラベル、factor すべき hom 空間が空であることによる自明成立、
  atomMap の非全単射性(型レベル不一致)だけで成立する負例、equation index が
  空・observable が退化していて equation / detector 輸送が一度も発火しない
  witness を弾く。
- `frontier`: cartesian(引き戻し)側 lift の存在の観察(bifibration 化の本証明は
  範囲外)、refinement 負例から抽出される追加データの型仕様の一般化、
  normalize 可換性の変種。

- `target theorem`: **Atom Transport Opcartesian Lift Theorem**。
  固定した一般 carrier `U : AtomCarrier` 上で次を構成する。
  - 圏 `Doct_U`: 対象は `ExtractionDoctrine U`、射は exact 射
    `σ = (sourceMap, atomEquiv)`(normalize 可換、
    `D.extracts s a ⟺ D'.extracts (σ.sourceMap s) (σ.atomEquiv a)`)。
  - refinement 射(圏の射としては合成せず、独立のデータとして定義する):
    `σ_ref = (sourceMap, atomMap)`。`atomMap` は**全単射**、normalize 可換、
    admission は前進含意
    `D.extracts s a ⟹ D'.extracts (σ_ref.sourceMap s) (σ_ref.atomMap a)` のみで、
    反映(逆向き含意)は課さない。
  - pointed 圏 `ExtInst_U`: 対象 `(D, s)`、射は exact `σ` と `s' = σ.sourceMap s`
    の組。射影 `π` は package `P` を
    `(P.reading.doctrine, P.reading.source)` へ送る。
  - package 総圏: 対象は `AATCorePackage U`、射 `P -> Q` は `ExtInst_U` 射
    `(σ, _) : π(P) -> π(Q)` と `F : SignedExactCoreReadingHom P Q` の対で
    `F.atomEquiv = σ.atomEquiv` を満たすもの。hom equality は structure equality
    とする。`π` は関手としてこの総圏から `ExtInst_U` へ落ちる。
  この設定で次が成り立つ。
  1. **(i) transportAlong**: exact `σ : D -> D'` と `π(P) = (D, s)` なる `P` から
     `Q = transportAlong σ P` と tautological hom `P -> Q` を構成でき、
     `π(Q) = (D', σ.sourceMap s)` であり、この hom は `σ` の上の opcartesian で
     ある: 任意の exact `τ : D' -> D''` と `τ ∘ σ` の上の任意の hom `P -> R` は、
     `τ` の上の hom `Q -> R` を通して一意に factor する。
  2. **(ii) 一意性**: `σ` の上の opcartesian lift は同型を除き一意である。
     一般圏論の標準論法の instantiation でよいが、fiber 内同型
     (`atomEquiv = Equiv.refl` の hom)の具体記述まで与える。
  3. **(iii) refinement 負例**: refinement 射 `σ_ref`(`atomMap` 全単射)であって、
     underlying map が `σ_ref.atomMap` に一致する `atomEquiv` を持ち
     `extraction_eq` を満たす `SignedExactCoreReadingHom` が
     `π(Q') = (D', σ_ref.sourceMap s)` なる**任意の** `Q'` へ向けて存在しない
     ものを構成する。さらに追加仮定 `H`(新規 Atom の composition / equation
     データ供給)を抽出し、(a) `H` を仮定した lift 構成定理(十分性)と
     (b) 負例 witness 上での `¬H` の両方を証明する。
  4. **(iv) 成分供給**: tautological hom の全 field(`extraction_eq`・
     `composition_eq`・`objectMap`・`configuration_eq`・`equationTransport`・
     `detectorCode_eq` を含む)が `σ` と `P` の構成データのみから供給され、
     構成した `Q` について standalone 等式
     `(transportAlong σ P).family = P.family.transport σ.atomEquiv` および
     configuration / equation system / detector code の対応等式が theorem として
     成立する。definitional(`rfl`)に成立する場合も成功と数える — 価値は
     入力が `σ` と `P` のみであるという provenance にある。
  (i)(ii)(iv) は `U` 上の全 `D` / `s` / `P` / `σ` について証明する。witness
  (非自明性・負例)のみ `FiniteModel` の carrier へ具体化する。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/AtomFoundation/` 配下。`Formal/AG` は参照のみ。
  site / cover / coverage topology / 係数は本 target に現れない。G-101 の完了面は
  (i)–(iv) と非自明性 witness まで。bifibration・擬関手的合成、doctrine 圏の
  fiber product、runtime extraction は主張しない。
- `target proof artifacts`: `Doct_U` の exact 射の定義と圏則、refinement 射の
  定義、`ExtInst_U` と射影 `π`、package 総圏と射影 functor、atomize 自然性
  theorem(`D'.atomize (σ.sourceMap s) = (D.atomize s).transport σ.atomEquiv`)、
  **`AATCorePackage` 全体の輸送 def**(doctrine の admission 述語の共役・
  composition・objectReading・equationReading・invariant / signature /
  operation reading の輸送。既存の成分 transport には存在しない新規構成であり
  `transportAlong` の本体)、tautological hom、opcartesian 性 theorem、
  factorization 一意性 theorem、fiber 内同型記述つき lift 一意性 theorem、
  refinement 負例 witness(任意 `Q'` への非存在の Lean 証明)、追加仮定 `H` の
  十分性定理と負例上の `¬H`、成分供給の standalone 等式群、非自明性 witness
  (non-identity `σ`、family が実際に変わり、非空 equation index 上で
  equation system / detector code の輸送が発火する例)、
  report `research/reports/G-101-aat-atom-foundation.md`。
- `target proof strategy`: D0 `Doct_U` / refinement 射 / `ExtInst_U` /
  package 総圏の構築 -> D1 atomize 自然性と `AATCorePackage` 輸送・
  tautological hom -> D2 opcartesian 性と一意性 -> D3 refinement 負例と
  追加仮定 `H` の抽出・十分性・`¬H` -> D4 成分供給等式と witness。
  既存成果の利用 map: `SignedExactCoreReadingHom.refl` / `.comp`(総圏の恒等・
  合成)、`AtomFamily.transport` / `AtomConfiguration.transport` 等の成分
  transport、`EquationSystemExactTransport` の既存補題群、
  `Formal/AG/ReadingFunctoriality/FiniteExamples.lean` の既存 package
  (witness 素材)。固定 statement と完了条件は本カードのみを正本とする。
- `target theorem completion criteria`: 全 artifact が sorry なしで `ResearchLean`
  に受理され、axiom / placeholder audit が clean であること。下記 ledger の
  `discharge-required` を構成・証明・Lean finite witness で放電し、T3 audit で
  provenance、proof-use、structure-field escape、route integrity を監査すること。
  Lean / report / tracking Issue を同期し、final review packet を作り、
  `$math-lean-review research/goals/G-101-aat-atom-foundation.md G-101-aat-atom-foundation`
  の4査読がすべて `No major findings` であること。
- `target premise discharge policy`: 入力(doctrine 対、`σ` / `σ_ref` の構成
  データ、package `P`)だけを残せる。圏則、atomize 自然性、輸送の
  well-definedness、opcartesian 性、一意性、負例の非存在証明、`H` の十分性、
  成分供給、非自明性はすべて completion までに生成・証明する。lift 結論相当
  データを certificate や structure field で受け取るだけでは放電と数えない。
- `target material premise ledger`:
  - `carrier U / FiniteModel`: `ambient-boundary`。artifact は不要、provenance は
    既存 `Formal/AG/Examples/FiniteModel.lean`。定理は一般 `U` で証明し、
    FiniteModel は witness の計算のみに使う。lift の存在や一意性を含めない。
  - `上層構造(AATCorePackage / SignedExactCoreReadingHom とその refl / comp)`:
    `ambient-boundary`。review 済み `Formal/AG/ReadingFunctoriality` の参照のみ。
    hom の値の型・総圏の恒等と合成の素材として使う。opcartesian 性・輸送の
    well-definedness を field へ入れない。
  - `Doct_U 射の圏則(合成・恒等・normalize 可換)`: `discharge-required`。
    provenance は `ExtractionDoctrine` の構成データ。artifact は圏則 theorem 群。
    lift の factor 対象として proof term で使う。
  - `atomize 自然性`: `discharge-required`。exact 射の admission 同値から証明し、
    artifact は自然性 theorem。`transportAlong` の well-definedness
    (`π(Q) = (D', σ.sourceMap s)`)の proof term で使う。自然性等式を射の定義や
    field に含めない(導出する)。
  - `AATCorePackage 輸送と tautological hom`: `discharge-required`。provenance は
    exact `σ` と `P` の構成データのみ。artifact は輸送 def と tautological hom
    構成。(i)(iv) の導出源として proof term で使う。opcartesian 性を構成の
    field に入れない。
  - `opcartesian 普遍性・一意性`: `discharge-required`。provenance は総圏の定義と
    tautological hom の構成。artifact は opcartesian 性 theorem・factorization
    一意性 theorem・lift 一意性 theorem。(i)(ii) の結論として proof term で使う。
    全称域(任意の `τ ∘ σ` 上の hom)を縮めない。
  - `refinement 負例と追加仮定 H`: `discharge-required`。provenance は `σ_ref` の
    構成データと FiniteModel witness。artifact は任意 `Q'` への非存在 theorem、
    `H` の十分性 theorem、負例上の `¬H`。型不一致だけによる非存在を discharge と
    数えない。`H` に lift の存在自体やそれと同値なデータを含めない。
  - `成分供給`: `discharge-required`。provenance は (i) の構成のみ。artifact は
    standalone 等式群。独立に構成した hom との事後一致で代替しない。
  - `非自明性 witness`: `discharge-required`。provenance は FiniteModel 上の
    具体構成。artifact は non-identity `σ` の発火例(非空 equation index 上で
    equation / detector 輸送が発火)。route integrity audit で使う。
- `target anti-weakening rule`: opcartesian 性を「hom が存在する」へ弱めない。
  universal property の全称域(任意の `τ ∘ σ` 上の hom)を縮めない。総圏の
  hom equality を商・Setoid へ粗視化して一意性を自明化しない。一意性を
  自明同型・同一対象への退化で満たさない。(iv) を (i) と独立の構成の後付け一致で
  代替しない。refinement 負例を空 doctrine・空 hom 空間・atomMap の型不一致の
  vacuity で満たさない。追加仮定 `H` に lift の存在自体やそれと同値なデータを
  含めない。結論相当データ(lift の存在・普遍性・導出等式)を theorem argument、
  typeclass、structure field、certificate field、opaque membership へ移さない。
  statement を claim boundary 外(段横断合成・base change 等)の主張と
  読み替えない。
- `target route integrity gate`: `σ`・`σ_ref`・lift・witness の provenance を
  doctrine の構成データ、canonical 構成、universal property、review 済み
  predecessor へ追跡する。identity `σ` だけ・退化 doctrine だけの発火、
  one-way-as-equivalence、proof 後の GOAL 読み替えを completion に使わない。
- `target failure policy`: (i)(ii)(iv) の反例は `target-refuted` とし、`Doct_U`
  射・総圏・輸送構成の定義への改訂案を返す(hom equality の strict 性で
  factorization 一意性が破れる場合を含む)。(iii) は負例構成が成功条件であり、
  逆に「refinement 射でも常に exact lift が存在する」ことが証明された場合は
  本カードの仕様欠陥として GOAL 改訂案を返す。同じ blocker が二 cycle 続けば
  `target-blocked`。claim boundary 外の機構が必要と判明した場合は本 GOAL を
  拡張せず、GOAL 改訂提案として返す。
