# G-152-aat-coherent-repair-effectivity — 局所変更の大域化・余接複体・有限証明

- `id`: G-152-aat-coherent-repair-effectivity
- `status`: `draft`
- `research mode`: `target-theorem`
- 関連メモ: [#6359](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。実行用tracking Issueはactive化時に定める。
- 設計: [n1019 §6–8](../../docs/note/n1019_shigure_representability_design.md)
- 依存: G-150・G-151。G-146・G-147は有限型の特殊化。

## 固定target

### A. 原始変更とderived inverse limit

G-151の変更を実際のfinite fragmentへ制限する射を構成する。
線形lift問題では、原始operation/Lawの全syzygyから
自己同型を−1、補正を0、defectを1とする複体D_Fを作る。
元の変更の複体とRlim_F D_Fの比較を構成し、同値となる条件を
原始support・totality・cochain制限から証明する。
比較同値そのものをinput fieldに置かない。

可算cofinal towerではMilnor列を、一般の添字では高次R^p limを用いて
有限段の障害と全体の障害を比較する。
条件なしの有限段存在⇒全体存在は主張しない。
非線形な変更全体が一つの加群になるとも主張しない。

一般性の正の核として、任意の小さいadapter diagramを持つ加法作用protocolを扱う。
状態はpublic担体とhidden moduleの積、保持する操作はhidden側の全平行移動と
public側の指定された非空な推移的作用、観測はpublic成分とする。
各vertexのpublic担体・hidden module・作用と、各adapterの線形部L_eをsource/targetで固定する。
category上のdiagramにはL_fe=L_fL_eとa_fe=a_f+L_fa_eを課す。
全意味保存射がtranslationへ分類されることを証明し、
adapterの線形部・定数項から実際の補正複体を生成する。
source aからtarget bへの式はc_t−L_ec_s=b_e−a_eとする。
moduleやpublic担体も変える射はG-151の全変更に残し、このtranslation分類と混同しない。
scheme表示を使うfamilyではmoduleの表示とbase changeを明示し、任意moduleを
有限自由と置き換えない。n1019 §7はhidden moduleがℤの必須例とする。

### B. 一つのnative例の全比較

Bool×ℤ、全u_t、flip v、観測Bool、h_n^a(b,z)=(b,2z+a_n)を原始入力とする。
全native変更の分類からc_n−2c_{n+1}=a_nを導く。
全係数環のfamilyではBool_R×A¹_Rと全G_a作用を使い、u₁だけで代用しない。

次を同じ対象・写像で証明する。

- Y_a=Spec ℤ[c₀,c₁,…]/(c_n−2c_{n+1}−a_n)が全変更を表現する。
- 有限Y_{a,N}≅A¹、遷移c_N=2c_{N+1}+a_N、Y_a=lim Y_{a,N}。
- 斉次変更群G=Spec Sym_ℤ(ℤ[1/2])と、解がある場合の自由推移的作用。
- L_{B_a/ℤ}≃B_a[1/2][0]、および実Law複体
  C(R)=[∏R→∏R]、d(c)_n=c_n−2c_{n+1}とRHom_R(R[1/2],R)との比較。
- C(R)≃Rlim C_N(R)、H¹C(R)≃lim¹(R,×2)。
- 平方零liftの補正とその障害が同じ複体のkernel係数版から得られる。

原始adapterからE_a=(ℤz⊕⊕ℤe_n)/(e_n−2e_{n+1}−a_nz)を作り、
0→ℤz→E_a→ℤ[1/2]→0、全Rでのtensor後の完全性を証明する。
Y_a(R)をz↦1のR-linear retractionの全体と同定し、
B_a≅Sym(E_a)/(z−1)と、拡大類[a]の同定を構成する。
Čechの符号はretractionの差で固定し、quotientのsectionの差と混ぜない。

任意の大きな変更の存在とcotangentの微小liftを混同しない。
この例では同じaffineな原始方程式が両方を計算することを比較定理にする。

### C. 非零障害とZariski局所修復

a_even=1、a_odd=0とする。全有限段の整数解を構成し、
3c₀+1=4^m(3c_{2m}+1)から全体の整数解不存在を証明する。

D(2)ではc₀=0から再帰、D(3)では周期解(−1/3,−2/3)を構成する。
これらが全無限diagramの変更であることを検査する。
G(D2)=ℤ[1/2]、G(D3)=0、G(D6)=ℤ[1/6]を計算し、
指定Čech類[−1/3]の非零性と位数3を証明する。

複体のlocalization短完全列から接続写像を構成し、この類が
[a]∈lim¹(ℤ,×2)≅ℤ₂/ℤの同じ[−1/3]になることを証明する。
ℤ[1/6]/ℤ[1/2]≅ℤ[1/3]/ℤを経由し、ℤ[1/6]を直接ℤ₂へ埋め込まない。
ℚ上の全解とℤ₂上の唯一の解も構成する。

さらに普遍map d:A^ℕ_c→A^ℕ_a、a'_n=εa_nを持つℤ[ε]/ε²上の基底と、
mod εでの点c=0を構成する。liftがc'=εx、d(x)=aと同値であることを証明する。
relative cotangentの零点pullbackを次数−1,0のtelescope複体から計算し、
defect=a'−d(c_tilde)の規約で、同じ非零[a]が実際の平方零lift障害になると示す。
有限stageのsmoothnessと、全体のformal smoothnessの不成立を同じmapで比較する。

H⁰C(ℤ)=0とH⁰C(ℚ)=ℚから、C(ℤ)⊗ℚ→C(ℚ)および
H⁰C(ℤ)⊗ℚ→H⁰C(ℚ)が同型でないことを示す。
原因は(∏ℤ)⊗ℚ→∏ℚの非同型である。
flat tensor自体は核と交換する。schemeのbase changeとも区別する。

### D. 有限計算の十分性を証明する

Mittag–Leffler性でlim¹が消えることと、有限段階で全結論が決まることは別に証明する。
原始presentationから安定性・有限生成性・再帰的な構造を導く具体的な十分条件を与える。
条件を満たす場合に、有限の証拠から全変更の存在・不存在・自由を結論する比較を構成する。
周期的adapter族について、有限個の遷移式から全段の不変式を導くcertificateを作る。

ArchSigへは、観測Atom・LawPolicyから上のprimitive式・制限写像を与える経路、
計算する有限対象、検査するcertificate、答える問いを明示する。
既存の有限整数解・Čech類計算を新機能として数えず、実装済み・性能改善とも主張しない。

## 前提・構成台帳

| 対象 | 役割 | 構成・証拠 | 使用先 |
| --- | --- | --- | --- |
| 観測・作用・adapterの原式 | 入力 | A–Bの全射分類 | change scheme・複体 |
| 複体・制限射・cotangent・比較 | 構成義務 | A–Bの同じ原式から生成 | 大域障害・微小lift |
| 交互列aとD(2),D(3) | 指定証人 | Cの全段・局所解と非零類 | Čech・Ext・lim¹の一致 |
| ML性・有限安定性・証明規則 | 別々の放電義務 | Dの原始構造から導出 | 有限certificateの十分性 |

## 完了条件

A–Dの一般比較と指定例をLeanで証明し、native射・scheme・cotangent・Čech・lim¹の
全写像を同じprimitive入力に遡ってreportする。
Milnor列の引用だけでnative比較を、有限段の成功だけで大域的存在を済ませない。
無限個のLawを固定有限数に打ち切った定理はB・Cの代用にならない。
反証と一般比較に残る研究義務は明示し、特殊化の達成で主目標を取り消さない。

成果物はresearch/lean/ResearchLean/AG/のLean証拠と、
research/reports/G-152-aat-coherent-repair-effectivity.mdの宣言・前提対応に置く。
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。
