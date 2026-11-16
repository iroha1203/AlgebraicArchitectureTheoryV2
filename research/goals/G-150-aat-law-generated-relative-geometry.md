# G-150-aat-law-generated-relative-geometry — 元の意味の上にLawの相対Specを構成する

- `id`: G-150-aat-law-generated-relative-geometry
- `status`: `draft`
- `research mode`: `target-theorem`
- 関連メモ: [#6359](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。実行用tracking Issueはactive化時に定める。
- 設計: [n1019 §3–4](../../docs/note/n1019_shigure_representability_design.md)
- 依存: G-149。G-139〜G-143のmodule構成は特殊化として比較する。

## 固定target

### A. 任意担体・任意個の量とLaw

構造S、quantity domain D_j(S)、Law入力E_ℓ(S)を任意の小さい集合で量化する。
quantity modelは実際の関数q_j:D_j(S)→Rと、その上の原始Lawの充足として定義する。
有限式は構造のcartesian term、quantity評価、係数、環演算から生成する。

Q_S=⊕_j C_k(D_j(S))、A_S=Sym_k Q_Sを作り、複製・操作のcoalgebra射・普遍量から
ρ_ℓ:C_k(E_ℓ(S))→A_Sを生成する。I_Sは全像の生成idealとする。
原始評価とρ_ℓの評価の一致をterm帰納法で証明し、

LawfulQuantity_S(R) ≃ Hom_k(Spec R, Spec(A_S/I_S))

を全k代数R・全環射について自然に構成する。
変数・Law・担体の有限性、idealの有限生成性を仮定しない。
左辺を環Homとして定義する方法は禁止する。

任意可換k代数Sについて、量q:S→Rに環演算保存Lawを課すことで
A_S/I_S≅SとSpec Sを回収し、全環Homの反変な射との一致を証明する。
任意module Mの線形quantityからSym Mも回収する。
一般には任意QC module Qの線形quantityがSpec Sym Qで表現される構成を使い、
copying domainとmodule domainを有限rankの仮定なしに接続する。

### B. 構造と係数と文脈を同時に動かす

G-149のsplit copying coalgebraとそのdescent forms、実際のoperation・relationから
構造のstack B_copyを構成する。被覆の種類を固定し、局所split moduleの降下と全Homの降下を
証明する。任意の内部sheaf担体がこの形であるという未証明の同定は用いない。

別にnativeの係数作用・原式からmodule M⊗R、scalar R等の係数的実現σとB_σを構成する。
Δ|M|→M⊗Rの写像、指定native定数点の回復、native基点での全Homの回復を証明する。
非連結kの追加点と、dual numbers上の新しい線形方向を保持し、
全RでB_copyとB_σを同値とはしない。点ごとのLawと全係数familyでのLawも区別する。

Q、ρ、Iを同じ同型に沿って降下し、M=Spec_{B_copy}(Sym Q/I)を構成する。
任意scheme T→B_copyへのpullbackが独立なquantity modelのaffine T-schemeになること、
基礎環変更、構造同型、文脈制限、term substitutionに自然であることを証明する。
同じ構成を、原始データからQ・ρを生成できる各B_σ上でも証明する。
構造保存射h:S→S'がquantity domainとLaw入力を運ぶ写像を原始sort mapsから生成し、
term評価との可換性からquantityの引戻しとA_S→A_S'のideal保存を証明する。
この条件を満たさない元のnative hも保持する。
quantity domainを運ぶhについて、一般にはM_S×M_S'上のq=h*q'という対応空間を構成し、
全target quantityからの射になる条件と区別する。補集合上のLawを持つ反例も証明する。
sheafificationとscalar extensionの交換には必要な仮定を実際に放電する。

### C. 係数的意味の存在・非一意性・不成立

既存ArchitecturalEquationSystemのsymbolic coordinateとobject-dependent residualを
原始データとして保持し、原式または下記拡張空間から生成したresidualとの評価一致を比較する。
既存の任意residualを有限式と仮定しない。
各native familyで次を区別する。1・2を構成し、3は下記の拡張空間の点が与える選択として構成する。

1. graphとして元のresidualをそのまま保持する。
2. 固定native値をObservable⊗_kRへ運ぶ。
3. 選択された拡張点から、変動するquantity上のregular residualを生成し、元の評価との一致を証明する。

Nat(R^n,R)≃k[t₁,…,t_n]を普遍tupleから証明する。
F_p上でtとt^pが同じnative値を持つが異なるfamilyになること、
Q上のδ₀がA¹上のregular extensionを持たないことを証明する。
有限support Lawにはzero extensionのind表示を構成し、全有限restrictionの逆極限との
非同値を証明する。これらのLawを意味圏から除去してCを達成したことにしない。

さらに任意native担体D、任意X、指定されたquantity reading q:D→k^X、
任意ε:D→kについて、全regular extensionの空間を構成する。
有限単項式集合Fごとに係数b_mを持ち、
全d∈DでΣ b_m m(q(d))=ε(d)を課すaffine scheme E_{ε,q,F}を作る。
zero extensionの閉埋込みに沿うind表示E_{ε,q}を構成し、
そのS点が全S代数Rに自然なR^X→Rでnative値に一致するものを全て分類すると証明する。
qをεへ選び直す方法や、次数・座標数の上限で切る方法は使わない。

全入力D=k^X,q=idでは、無限体で存在すれば一意であることを証明する。
有限体F_qでは評価核(t_x^q−t_x)_xと、延長存在と有限座標依存の同値を証明する。
一般の基礎環でk点不存在とschemeの空性を区別し、
ℤ上のε(n)=n(n−1)/2の次数2 chart≅Spec ℤ[1/2]を構成する。

複数context・operation・term substitutionとのcoherenceを、普遍tupleでの係数等式として
同じsupport-profile chartに課し、互換な全拡張のmoduliと普遍residualを構成する。
元のresidualのgraphと照合し、その上のLawの零点familyを構成する。
F_p上のt/t^pによる、native値の一致だけではcoherenceが出ない例を反証する。

M⊗R、Hom(M,R)、C_R(|M|)を任意module Mについて区別し、
実際の比較写像と、dualizability等を使う箇所を記す。
全native構造に係数familyを一意に割り当てるという反証された要求は採用しない。
その代わり、指定された原始係数構造を保持する比較を必須にする。

### D. 通常の代数性と有効化

原始的なevaluation/coevaluationとsnake等式を持つ有限個のmodule sortについて、
dualizabilityから局所有限自由性を導き、全局所階数成分のframe chartsを生成する。
残りの宣言が有限tensor・直和・dual・指定retract等から構成され、
操作・Law追加が相対affineになることを具体的な生成規則ごとに証明する。
構成したGL作用・torsor・同型diagramから商stackの代数性を証明する。
markingによる自己同型消滅とopen overlapが構成できる場合はschemeを接着する。

この十分条件を全AATの入力条件にはしない。
独立なline quotientの無限積P¹と、無限階数moduleの全自己同型を
同じ意味圏に保持して、それぞれの通常のalgebraic space・algebraic stackへの非有効化を証明する。
operation profileは各chartと全profile表示を区別し、無限であるだけで非有効化とはしない。
ℕの恒等写像を表すprofile S_n={n}のchartはSpec kになることも検査する。
無限moduleの接空間はtensor extensionのB_σで計算し、B_copyの零微小変形とは混同しない。
trivial inertiaだけでschemeを結論しない。

## 前提・構成台帳

| 対象 | 役割 | 構成・証拠 | 使用先 |
| --- | --- | --- | --- |
| 原始quantity、Law式、nativeのD・q・ε | 入力 | A・Cの意味を幾何と独立に与える | 評価一致・全拡張分類 |
| Q・ρ・ideal、Eの表示、coherence | 構成義務 | A–Cの生成とnative比較 | 相対表現・普遍family |
| 局所split性、moduleの係数作用 | 経路ごとの入力 | Bのcopyingとσを区別し、各原始解釈を構成 | descent・基点の全Hom |
| duality等式・有限frame生成規則 | Dの十分条件 | frame・作用・overlapを生成 | 通常の代数性 |
| 全nativeの保持・非有効化 | 構成義務 | C–Dの分類と指定反例 | 特殊化への縮小を防ぐ |

## 完了と主目標への関係

A–Dの定理、原始sourceとの対応、正例・反例をLeanで証明する。
具体的なframe構成、ρの生成、descentは結論相当の入力fieldへ移さない。
全D・q・εの拡張空間、context全体の互換性、原始係数構造とnativeの比較が
未構成なら本GOALは未達であり、報告事項へ移して完了することはできない。
有限module成分だけの達成でC・DまたはSHIGURE全体を達成したことにはしない。
任意sheafという名称だけで、通常の幾何への比較を済ませない。

成果物はresearch/lean/ResearchLean/AG/のLean証拠と、
research/reports/G-150-aat-law-generated-relative-geometry.mdの宣言・前提対応に置く。
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。
