# G-126：既存宣言の再利用対応表

[設計の入口](README.md)で使うAPIと追加する責務を対応させる。
実装参照はrepository commit `833f350c8b8c1083517251eb75c4de2b6fbbe2f2`、
mathlib commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`に固定する。
toolchainは`leanprover/lean4:v4.28.0`。
表中の「直接利用」は当該補題・構成の再利用を意味し、G-126の結論が既存であるという意味ではない。

## 1. ReadingとLaw

以下の名前空間は`AAT.AG.CanonicalResolution`。

| 既存宣言・ソース | 利用条件と得られるもの | G-126で追加するもの |
| --- | --- | --- |
| [`Reading`、`Reading.kernelSetoid`](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/833f350c8b8c1083517251eb75c4de2b6fbbe2f2/research/lean/ResearchLean/AG/CanonicalResolution/Reading.lean#L22-L45) | 直接利用。`Source : Type u`から`Target : Type u`への全射と核 | 修復商に操作・観測を加える。任意宇宙の商先は核の商との同型で標準化 |
| [`Reading.factors_iff_kernel`、`factorsThrough_iff_coarserThan`](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/833f350c8b8c1083517251eb75c4de2b6fbbe2f2/research/lean/ResearchLean/AG/CanonicalResolution/Reading.lean#L48-L87) | 直接利用。写像の因子化と核包含の同値。`coarse.FactorsThrough fine`は`fine → coarse` | 構造保存、射の合成、同型類の順序。逆方向の証明は古典的選択を使うため実行用代表元探索には用いない |
| [`FiniteLawFamily`、`adequate_iff_kernel`](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/833f350c8b8c1083517251eb75c4de2b6fbbe2f2/research/lean/ResearchLean/AG/CanonicalResolution/Reading.lean#L126-L172) | 直接利用。有限Law型、各値型の等号判定、全Law評価を降ろせる条件 | 依存積観測と核の同定、操作降下・要求同一視を伴うreading全体との対応 |
| [`jointKernelSetoid`、`jointKernelReading`、`jointKernel_kernel_iff`](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/833f350c8b8c1083517251eb75c4de2b6fbbe2f2/research/lean/ResearchLean/AG/CanonicalResolution/JointKernel.lean#L21-L43) | 直接利用。全Lawの現在の評価を同一視する標準商 | 将来の観測同値`behavior`との包含。両者の一致条件は操作安定性として証明 |
| [`jointKernelLawFactor`、`jointKernel_adequate`、`jointKernel_coarser_of_adequate`、`jointKernel_factorsThrough_of_adequate`](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/833f350c8b8c1083517251eb75c4de2b6fbbe2f2/research/lean/ResearchLean/AG/CanonicalResolution/JointKernel.lean#L47-L80) | 直接利用。Lawの商上の評価、adequateなreadingから標準解像度への因子化 | `qβ`がadequateであることをAから導いて適用。`qL.CoarserThan qβ`の向きを保持 |
| [`jointKernelFactor`と可換式・一意性、`jointKernel_universal`](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/833f350c8b8c1083517251eb75c4de2b6fbbe2f2/research/lean/ResearchLean/AG/CanonicalResolution/JointKernel.lean#L83-L120) | Lawにadequateなreadingからの一意の因子化。`jointKernelFactor`は`noncomputable` | Eの因子化との一致証明に利用。Dの返す写像は有限表から別途計算して同じ写像と証明 |
| [`computedClass`、`computedPartition`、`computedReading`、`computed_kernel_iff`、`computed_kernelEquivalent_jointKernel`](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/833f350c8b8c1083517251eb75c4de2b6fbbe2f2/research/lean/ResearchLean/AG/CanonicalResolution/Effective.lean#L28-L117) | `Fintype Source`と`DecidableEq Source`の下でLaw同値類を有限表示。核の一致定理を直接利用 | Dの番号付き商とG-103の有限表示の比較。`computedReading laws`だけでは操作閉包・未来観測・失敗語・費用は得られない |

`computedReading`の有限集合表示からDの費用上界を推測しない。
Dは番号付き配列で代表元とclass IDを計算し、その核が数学的な合同と一致することを証明する。
Eで標準解像度と一致する条件の下では、既存の`computedReading`と核同値を経て比較する。

## 2. mathlibの商・束

| 既存宣言・ソース | 再利用する構成 | 必要な接続 |
| --- | --- | --- |
| [`Setoid.completeLattice`、`sInf_iff`](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Data/Setoid/Basic.lean#L179-L215) | 同値関係の順序、任意の交わり | 交わりの操作安定性を証明し`OperationCongruence`に完全束を構成 |
| [`sup_eq_eqvGen`、`sSup_eq_eqvGen`、`eqvGen_le`、`eqvGen_mono`](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Data/Setoid/Basic.lean#L246-L291) | 関係の和の同値閉包とその最小性 | 同値閉包の操作安定性。要求だけの同値閉包を操作合同と取り違えない |
| [`Setoid.map_of_le`](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Data/Setoid/Basic.lean#L221-L222) | `r ≤ s`から`Quotient r → Quotient s` | 操作・観測保存、元の状態での評価式。両端間の数学的な因子化に利用 |
| [`Setoid.liftEquiv`、`lift_unique`](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Data/Setoid/Basic.lean#L316-L325) | `r ≤ ker f`から商上の全写像への対応と一意性 | Bの任意の`X`への普遍性。有限性・全射性を追加せず操作・観測を保存 |
| [`quotientKerEquivOfRightInverse`、`quotientKerEquivOfSurjective`](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Data/Setoid/Basic.lean#L374-L386) | 核の商と全射先との同型。右逆が明示されれば計算的な構成 | Bでは全射版、Dでは代表元表から右逆版。構造保存は新規証明 |
| [`Setoid.mapOfSurjective`、`comap`、`comap_eq`](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Data/Setoid/Basic.lean#L399-L419) | 前者は`ker f ≤ r`と`Surjective f`の下で像の同値関係。後者は任意の写像による引戻し | 自然性の下端は`comap`と生成の最小性を使う。生の要求の像は`Relation.Map R q q`を使い、その後で操作合同を生成 |
| [`Setoid.correspondence`](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Data/Setoid/Basic.lean#L450-L462) | `{s // r ≤ s}`と`Setoid (Quotient r)`の順序同型 | 両方向の操作安定性を証明して制限し、像の要求からの生成がjoinに対応すると示す |
| [`Setoid.quotientQuotientEquivQuotient`](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Data/Setoid/Basic.lean#L431-L443) | `r ≤ s`に対し`Quotient (ker (Quot.mapRight h)) ≃ Quotient s` | 第二段の生成合同とこの核との一致が適用前の証明義務。可換式と構造保存も追加 |
| [`Finite.of_surjective`、`Quotient.finite`](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Data/Fintype/EquivFin.lean#L197-L205) | 有限sourceの全射先・商が有限 | Bの有限性に利用。Dの計算用列挙はこれから古典的に選ばず、明示表で構成 |

## 3. 有限手続きの補助と流用しない部分

| ソース | 得られるもの | G-126での扱い |
| --- | --- | --- |
| [`DFA.evalFrom`、語の連結](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Computability/DFA.lean#L58-L113)、[`evalFrom_split`](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Computability/DFA.lean#L128-L154) | foldlによる語作用と、状態数以上の長さの経路から非空loopを取り出す補題 | 対状態`S × S`に適用して分離語を`n²`未満へ短縮する。DFAの`start : S × S`は証明対象の対から局所的に与える。基本入力に開始状態を要求しない |
| [`FiniteReading.EffectivenessProgram`](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/833f350c8b8c1083517251eb75c4de2b6fbbe2f2/research/lean/ResearchLean/AG/LocalSemanticReconstruction/FiniteEffectiveness.lean#L40-L59)、[`permutationEffectivenessProgram`](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/833f350c8b8c1083517251eb75c4de2b6fbbe2f2/research/lean/ResearchLean/AG/LocalSemanticReconstruction/FiniteEffectiveness.lean#L133-L175) | 部分読み取り表の整合判定と延長。後者は保持条件のある置換問題 | 設計の参考。修復商・分離語・費用を返す型ではなく、G-126の実行APIとしてimportしない |
| [`gLocalV1ReachabilityExpansion`](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/833f350c8b8c1083517251eb75c4de2b6fbbe2f2/research/lean/ResearchLean/AG/UniformInvariance/GLocalV1V5Reduction.lean#L1797)、[`gLocalV1_iterate_reachable`](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/833f350c8b8c1083517251eb75c4de2b6fbbe2f2/research/lean/ResearchLean/AG/UniformInvariance/GLocalV1V5Reduction.lean#L1932) | 固定presentationのpacketによる到達可能状態の展開 | 設計の参考。終了上界は固有の減少量を使い、任意の操作対グラフや語の出力には直接使えない |
| [`firstMatchingOr`と明示列挙の実装](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/833f350c8b8c1083517251eb75c4de2b6fbbe2f2/research/lean/ResearchLean/AG/UniformInvariance/FiniteComparisonPresentation.lean#L15-L67) | 明示リストの`List.find?`による代表元探索。`Finset.toList`の実行上の制約も記載 | 方式を参考にし、Dでは`Fin n`の順序付き列挙を使う。空状態を許すため、既定状態を持つpresentation全体は流用しない |
| [`Con`](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/GroupTheory/Congruence/Defs.lean#L68) | 二項乗法についての合同 | 名前付き単項操作族と型が異なる。基底の`Setoid`を直接用いる |

この対応で再利用する既存APIには、G-126の入力表から両端・分離語・費用を一緒に返す
実行関数は含まれない。その構成は[有限構成](finite-construction.md)の責務とする。
