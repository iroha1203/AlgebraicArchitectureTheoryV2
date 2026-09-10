# G-121-aat-finite-decoder-representability — 有限decoderの対象・射の表示可能性

- `id`: `G-121-aat-finite-decoder-representability`
- `status`: `draft`
- `research mode`: `target-theorem`
- `tracking issue`: 未作成。active化時に作成する。
- `source note`: [n1010 §5・§9.4](../../docs/note/n1010_aat_post_annapurna_conjectures_research_plan.md)

## 研究目的

有限のデータで実現を表せることと、その実現の間の比較を表せることを区別し、
既存の有限decoderが保持する対象と射を分類する。有限例外コードを一点コンパクト化上の
連続写像として読み、G-112の端点同型を含むcoverageを、固定code間の射の表示可能性へ
接続する。有限carrierでは既定値が保持する情報、無限carrierでは置換のsupportが
課す条件を明らかにする。

これはn1010のS3に対応する。G-120とは底の実現圏と比較射を共有し、ここではG-101・
G-110・G-112の既存宣言から定まる有限表示とdecoderを直接の入力にする。
後続の再構成に使う表示圏について、対象の表示範囲と射の表示範囲をともに確定する。

## 固定target

任意のAtom carrier `U` とその既存宣言のuniverseを量化し、`D=U.Atom` とする。
既存codeの評価には `DecidableEq D` を用い、`D` と `Bool` には離散位相を入れる。
`D⁺=OnePoint D`、追加点を `∞` と書く。Sourceに位相を入れる場合も離散位相とする。

次の対象は既存宣言を用いる。

| 記号 | 既存宣言・所在 |
| --- | --- |
| `Code(D)`、有限support置換のcode | [Schema.lean](../lean/ResearchLean/AG/DoctrineFiberProduct/Schema.lean) の `AtomPredicateCode`、`AtomPermutationCode` |
| `P₀`、`D₀:P₀→B` | 同ファイルの `FiniteCodeCartCategory U`、`finiteCodeCartRealization`。`B=ExtractionInstance U` |
| typedな射の表示と評価 | 同ファイルの `CartPresentationBetween`、`typedPresentationToSemantic`、`FiniteCodeCartHom` |
| 端点同型を含むcoverage | [ExactBottomCoverageSchema.lean](../lean/ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageSchema.lean) の `AnchoredCoverageWitness` |
| 既存の有限／余有限codeとcoverage構成 | [ExactBottomCoverageClassification.lean](../lean/ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageClassification.lean) の `finiteOrCofiniteAtomPredicateCode`、`endpointFiniteTargetCofiniteCoverage`、`coveredObjectWitness_necessary` |

`P∈P₀` の有限Sourceを `S_P`、normalizeを `n_P`、extraction tableを `a_P` とし、
実際の評価に使うcodeを `t_P(s)=a_P(n_P(s))` と書く。`n_P` は既存の任意の有限写像であり、
冪等性を仮定しない。表す成果は固定Atom carrierに相対的な有限tableの存在・同定である。

### A. 有限例外コードと連続延長の同値

`q=(b,F)∈Code(D)` に対し、`∞` で `b`、`D` 上で既存の `q.eval` を取る連続写像を
構成し、同値

\[
E_D:Code(D)\simeq C(D^+,\mathrm{Bool}),\qquad
E_D(q)(\infty)=b,\quad E_D(q)(x)=q.\mathrm{eval}(x)
\]

を証明する。逆写像は `b=f(∞)` と有限集合 `F={x∈D | f(x)≠b}` から作り、
連続性からその有限性を示す。両逆は生のcodeと連続写像について証明する。

`q∼q'` を `D` 上の評価の一致と定義する。`Code(D)/∼` と、trueを取る集合が有限または
余有限なBool値写像全体との同値を構成する。さらに次を証明する。

- 無限の `D` では評価写像が単射であり、延長可能な述語の連続延長は一意である。
- 有限の `D` では任意の `p:D→Bool` に対し、その評価を持つcodeはちょうど
  `(false,{x | p(x)=true})` と `(true,{x | p(x)=false})` の二つである。
  対応する延長の `∞` での値は異なる。空の `D` でもこの二つを区別する。
- 既存の `finiteOrCofiniteAtomPredicateCode` の評価とこの同値を一致させ、
  有限の `D` での既定値falseの選択、無限の `D` での一意なcodeとの一致を示す。

任意のAtom置換 `σ:D≃D` を `∞` を固定する同相写像 `σ⁺:D⁺≃ₜD⁺` へ延長し、

\[
E_D(q.\mathrm{transport}(\sigma))
  = E_D(q)\circ(\sigma^+)^{-1}
\]

を証明する。code、連続写像、評価の各対応を、恒等・逆・合成と整合させる。
この輸送は有限supportに限定せず、既存の `AtomPredicateCode.transport` を使う。

### B. G-112のcoverageの位相的特徴づけ

任意の `I:CartSemanticInput U` を量化する。そのsourceとtargetを `X,Y`、それぞれのSourceを
`S_X,S_Y` とし、targetの抽出述語を `Y.extracts(y,x)` と書く。次を証明する。

\[
\begin{aligned}
&\operatorname{Nonempty}(\operatorname{AnchoredCoverageWitness}(I))\\
&\quad\iff \operatorname{Finite}(S_X)\land\operatorname{Finite}(S_Y)\ \land\\
&\qquad\bigl(\forall y\in S_Y,\ \exists f_y\in C(D^+,\mathrm{Bool}),\quad
 \forall x\in D,\quad (f_y(x)=true\iff Y.\mathrm{extracts}(y,x))\bigr).
\end{aligned}
\]

Sourceの有限性を、その離散空間のcompactnessと同値にし、上の必要十分条件を
両Sourceのcompactnessと抽出述語の連続延長によって述べる。
十分方向ではAから既存の有限／余有限条件を導き、
`endpointFiniteTargetCofiniteCoverage` のcode・端点同型・可換正方形へ接続する。
必要方向では既存witnessの実端点と抽出述語から条件を導く。

この対応で用いる表示射のsource map・Atom置換とdecoderの射を一致させる。
既存の `idTypedPresentation` と `compPresentation` を用いた恒等・合成についても、
`typedPresentationToSemantic` と `D₀` の射の評価が一致することを証明する。

### C. 固定code間の射を表示できる必要十分条件

任意の `P,Q∈P₀` と意味射 `f:D₀(P)→D₀(Q)` を量化する。
その実source mapとAtom置換を `s_f:S_P→S_Q`、`σ_f:D≃D` とし、
`supp(σ_f)={x∈D | σ_f(x)≠x}` と置く。次を証明する。

\[
\begin{aligned}
&\exists h:P\to Q\text{ in }P_0,\quad D_0(h)=f\\
&\quad\iff \operatorname{Finite}(\operatorname{supp}(\sigma_f))
 \ \land\ \forall s\in S_P,\quad
 t_Q(s_f(s)).\mathrm{defaultValue}=t_P(s).\mathrm{defaultValue}.
\end{aligned}
\]

左辺を、同じ固定端点 `P,Q` の `CartPresentationBetween P Q` で `f` をdecodeするものの
存在とも同値にする。十分方向では `s_f` と `σ_f` を有限tableへ符号化し、
normalize・codeのextraction等式・pointの三条件を `f` と右辺から証明する。
source mapとdecodeされたAtom置換が `s_f,σ_f` そのものであることを含める。

右辺の既定値条件を、Aの連続延長の `∞` での一致として同定する。
無限の `D` では `f` のextraction exactnessからこの条件を導き、
射の表示可能性と `supp(σ_f)` の有限性だけとの同値を得る。

すべての `D` について `D₀` の忠実性を、既存のdecodedな射の等しさによる商から証明する。
固定code間の射を扱い、端点の意味同型を選び直すことはこの存在量化に含めない。

### D. 有限carrierでの充満性とcodeの正規化

有限の `D` について、対象条件

\[
\forall s\in S_P,\quad t_P(s).\mathrm{defaultValue}=false
\]

で `P₀` の充満部分圏 `P₀⁰` を定める。条件はnormalizeの出力位置に置き、
それ以外のextraction tableを制限しない。制限したdecoder `D₀⁰:P₀⁰→B` が
充満忠実であることを、Cの分類と全Atom置換のsupportの有限性から証明する。

任意のcode `P` の各extraction table `a_P(z)` を

\[
\bigl(false,\ \{x\in D\mid a_P(z).\mathrm{eval}(x)=true\}\bigr)
\]

へ置き換え、Source・normalize・pointを保つ関手 `R_fin:P₀→P₀⁰` を構成する。
射ではsource mapとdecodeされたAtom置換を保ち、typed presentationの条件、
射の商での代表元独立性、恒等・合成を証明する。
source mapとAtom置換がともに恒等である成分から、自然同型

\[
D_0^0\circ R_{fin}\cong D_0
\]

を構成する。codeの構造等号とdecode後の意味同型は別の結論として扱う。

固定例として `D=Fin 1`、両codeの `sourceCard=1`、normalizeは恒等、pointは唯一の要素とする。
全Sourceでcode `(true,∅)` を持つ `P_t` と `(false,{0})` を持つ `P_f` を取る。
両者の評価がすべてtrueであること、恒等source map・恒等Atom置換による
`D₀(P_t)≅D₀(P_f)`、`R_fin(P_t)` のunderlying codeと `P_f` の等号を証明する。
同時に、どちらの向きにも元の `P₀` の射が存在しないことを既定値の不一致から証明し、
意味の同型を元のcode圏内の同型へ取り替えられないことを同じ例で示す。

### E. 無限supportと可算構文の表示限界

`D=ℕ`、`sourceCard=1`、normalizeは恒等、pointは唯一の要素、
全Sourceのextraction codeは `(true,∅)` とした `P_*∈P₀` を固定し、`X_*=D₀(P_*)` とする。
Atom置換

\[
\sigma(2n)=2n+1,\qquad \sigma(2n+1)=2n
\]

と恒等source mapから意味の自己同型 `u_σ:X_*≅X_*` を構成する。
すべてのAtomが動くことと、Cから `u_σ.hom` をdecodeする `P_*→P_*` の射の非存在を
証明する。これを `D₀` の非充満性へ接続する。Aの輸送により `σ⁺` は同相写像となる。

同じ `u_σ.hom` に対し、sourceの端点同型を恒等、targetの端点同型を `u_σ`、
表示射を `idTypedPresentation P_*` とする `AnchoredCoverageWitness` を構成し、
可換正方形を評価する。固定code間の射の非存在と、端点同型を含むcoverageを同時に示す。

さらに任意の `S⊆ℕ` に対し、`n∈S` の対 `(2n,2n+1)` だけを交換する置換 `σ_S` と
恒等source mapから `u_S∈Aut(X_*)` を構成する。
`σ_S(2n)=2n+1 ↔ n∈S` の評価から `S↦u_S` の単射性を証明し、
`Aut(X_*)` が非可算であることを示す。
任意の可算型 `T` と写像 `decode:T→Aut(X_*)` に対し、その非全射性を証明する。
可算alphabet上の有限列、可算個の表示対象と各対の可算な射構文を合わせた型へも適用する。
この下限の仮定は構文全体の可算性であり、計算可能性は要求しない。

## 前提・構成台帳

| 対象・対応条項 | 役割 | 必要な構成・証拠 | 出所・使用先 |
| --- | --- | --- | --- |
| Atom carrier、既存code・意味圏・decoder（A–E） | 入力として保持 | 各条項の実評価・同定 | G-101・G-110のsourceから対象と射の表示可能性へ |
| 離散位相・一点コンパクト化（A・B） | 入力として保持 | Aの連続性・両逆、Bのcompactnessとの対応 | 位相の定義から有限例外集合とcoverage条件へ |
| 有限／無限carrier（A・C・D） | 一般定理の仮定 | Aの二つのcode／一意性、Cの条件簡約、Dの充満性 | 同じcodeの評価と∞の値から射の分類へ |
| G-112の有限／余有限codeとcoverage（A・B） | 既存構成として使用し、接続を放電する義務 | A・Bの位相的特徴づけと実端点・射の一致 | 既存構成と必要条件から連続延長による必要十分条件へ |
| 意味射の実source map・Atom置換・法則（C） | 入力として保持 | Cの判定条件の両方向と表示射の構成 | 実写像・exactnessから同じ端点の表示へ |
| support・既定値による分類と正規化関手（C・D） | 構成・放電義務 | Cの三つのtyped条件、Dの関手と自然同型 | 有限tableと実評価から射の像の分類と意味の保持へ |
| 既定値falseの対象条件（D） | 入力として保持（対象条件） | Dの充満忠実性 | normalizeの出力上のcodeから全意味射の表示へ |
| 指定した有限例とNat上の例（D・E） | 構成・放電義務 | 各例の全条件、実写像の評価、射の非存在、coverage | 固定codeから意味の同型・有限support・可算構文の相違へ |
| 可算な構文型（E） | 一般定理の仮定 | 任意decoderの非全射性 | 同じ意味対象の非可算な自己同型族から表示限界へ |

## 完了条件

A–EをすべてLeanで構成・証明する。D・Eで固定した非存在・非充満性・非可算性は
証明すべき結論の一部とする。それ以外の固定主張への反例は共通の反証停止規則で扱う。
有限tableの存在には既存codeと同様に非計算的な構成を許し、入力からcodeを計算する
アルゴリズムの完成とは区別する。

新規Lean成果物は `research/lean/ResearchLean/AG/` に置く。条項と宣言の対応、
既存decoder・coverageからの使用経路、固定例の評価、参照する既存宣言と版を
`research/reports/G-121-aat-finite-decoder-representability.md` に記録する。

[共通基準の参照適用](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)
による監査・独立最終レビューを完了判定に適用する。
承認・適用版・放電状況・検証・査読・active化の記録はtracking Issueとreportに置く。
