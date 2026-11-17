# G-141-aat-coherent-repair-effectivity — 変更の障害・修復・有限判定

- `id`: G-141-aat-coherent-repair-effectivity
- `status`: `draft`
- `research mode`: `target-theorem`
- 関連メモ: [#6359](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。実行用tracking Issueはactive化時に定める。
- 設計: [n1019 §6–8](../../docs/note/n1019_shigure_representability_design.md)、[n1020 §13・15–16](../../docs/note/n1020_shigure_polynomial_specializations.md#semantic-lift)
- 依存: G-139・G-140。診断への比較はG-142が本カードの実修復から構成する。

意味を保つ変更について、その存在・組立ての障害・全修復と残る自由を同じ原始Lawから
導く。有限表示の微小liftと無限diagramの大域化を比較し、有限計算から結論してよい
条件を証明する。syzygy、cotangent、Čech、逆極限はこの一つの到達像を支える構成である。
G-140の探索fiberを使い、守る意味と目的から全候補・不存在の証拠・残る設計自由を計算する。

## 固定target

### A. 原始変更とderived inverse limit

G-140の変更を実際のfinite fragmentへ制限する射を構成する。
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
moduleやpublic担体も変える射はG-140の全変更に残し、このtranslation分類と混同しない。
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

### D. 有限計算と設計探索の十分性を証明する

Mittag–Leffler性でlim¹が消えることと、有限段階で全結論が決まることは別に証明する。
原始presentationから安定性・有限生成性・再帰的な構造を導く具体的な十分条件を与える。
条件を満たす場合に、有限の証拠から全変更の存在・不存在・自由を結論する比較を構成する。
周期的adapter族について、有限個の遷移式から全段の不変式を導くcertificateを作る。

G-140 EのF_{a,H,P}について、次の有限計算への特殊化を原始編集式から構成し、
出力の変更としての正しさ、指定した域での全解の回収、witnessの復元を証明する。

1. 有限体上の有限個の係数・有限個の編集式では、生成した保存方程式の全解を列挙する。
   保存方程式の生成は全操作語の評価定理を使い、有限長の実行試験で代用しない。
2. 整数・有理数上のaffine編集制約では、全解のparameter表示と不存在のcertificateを作り、
   許す変更域・固定部分・原始操作への復元を同じ写像で証明する。
3. ℚ上の有限多項式chartと有限個の等式・可逆条件では、ug−1=0による可逆条件の表示、
   ideal所属の検査証拠、代数閉包上の空性の判定を構成する。
   原始操作からchartと式を生成し、一般のideal包含条件を無条件に閉零点としない。
4. 同じ有限表示から目的parameterへの射について、消去と開条件の分岐から幾何点での
   実際の像を構成可能集合として計算し、各目的の全fiberと比較する。
   xy=1→xの像D(x)と閉包A¹を区別し、像の点に存在する変更witnessを保持する。

schemeの表示と指定係数域の点の探索を区別する。x²+1=0のℚ点と代数閉包の点、
無限fragmentでのB・Cを必須の識別例にする。
順序付き目的では比較する評価と順序を入力に保持し、表現だけから最適性を結論しない。

ArchSigへの経路では、観測Atomに現在の操作・編集対象の値と由来、
Law側に保存条件・許す編集規則・目的の評価規則を置き、計算側が候補・方程式・証拠を生成する。
sourceに関する抽出の正しさは観測者が確保し、有限解と操作モデルの比較を本targetが担う。
既存の有限整数解・共通修復・実像・Čech類計算を再利用し、PRの意味からの生成と
非線形・高次・無限族への比較を追加の証明義務とする。実装済み・性能改善とは主張しない。

### E. 有限表示の実現liftと合法な局所修復

可換環k、有限個の演算・Lawを持つn1020 §3の原始表示P、k代数R、独立な実現
x∈Sem_P(R)、平方零拡大R′→Rとkernel Mをこの順に量化する。Lawを忘れた
smooth ambient Yを原始表示から構成し、affine test上でのambient liftの存在を証明する。
基底chartではB=k[z₁,…,z_n]、原始Lawの全成分f₁,…,f_r、J=(f)、A=B/Jとし、
全syzygy S=ker(B^r→J)からN=J/J²の表示と次の複体を生成する。

```math
D^0=M^n\xrightarrow{\operatorname{Jac}(f)(x)}D^1=M^r
 \xrightarrow{d^1}D^2=\prod_{s\in S}M,
\qquad(d^1r)_s=\sum_i s_i(x)r_i.
```

原式の恒等式からd¹d⁰=0とker d¹≃Hom_R(N⊗_A R,M)を証明する。
有限syzygy生成族を使うときは生成性とH⁰・H¹の比較を証明する。
ambient lift z̃の残差r=f(z̃)からo_P∈H¹(D)を構成し、liftの変更則
r(z̃+δ)=r(z̃)+d⁰δ、o_P=0と実際のlawful liftの存在の同値、非空な全liftへの
H⁰(D)の自由推移作用を同じ加群・演算・Lawへ戻して証明する。

Yのideal sheafを𝒥、E_x=x*Ω_{Y/k}、N_x=x*(𝒥/𝒥²)として
D̄=[Hom_R(E_x,M)→Hom_R(N_x,M)]を構成する。単一chartに入らないxも含め、
chartのD、D̄、RHom_R(Lx*L_{M_P/k},M)の次数0・1と指定障害を同定する。
N_xのprojectivityは要求しない。Noetherian係数・有限表示の系では、有限principal
affine cover上の準連接性、Homの局所化、Čech totalizationとの比較を証明する。
この系の仮定をG-139の表現定理へ移さない。

原始代入とLaw導出u:P→P′からρ:Sem_{P′}→Sem_Pを作り、x∈Sem_{P′}(R)と
指定されたy′∈Lift_P(ρx,R′)に対するLift_u(x,y′)を独立に定義する。
ideal・conormal・微分・syzygyの比較からF_u=Cone(D̄_{P′}→D̄_P)[−1]を構成し、
Law残差とρの像の差からo_u∈H¹(F_u)を得る。o_u=0と指定liftの存在、全解の
H⁰(F_u)-torsor分類、恒等・合成・拡大の射・表示変更との自然性を証明する。

affine Law Lz−b、基準状態p、変更可能域Hについて、実修復集合の非空性を
b−Lp∈L(H)、全解をker(L|_H)のtorsorで特徴づける。非線形Lawの平方零修復は
原始Jacobianを使う。文脈ごとのHは変更可能な宣言から生成し、観測式の全参照が
所属する被覆と、その交差上で可換な原始代入から合法な修復係数を生成する。
制限、作用、matchingから実修復への組立てを証明する。T↦X+Yを{X}/{Y}だけに
分ける不適合例では、ℚ[ε]/ε²上の合法差分(ε,−ε)を局所係数0へ制限できず、
観測を落とすと(ε,0)も組み立つことを示す。全参照を含む合併被覆で適合性を回復する。

全多重交差を持つ宣言被覆から自由な変数・Law残差のČech total complex T_rawを作る。
各宣言の支持がfull simplexであることからH⁰(T_raw)≃ker d⁰、H¹(T_raw)≃coker d⁰を
導き、全大域syzygyから0→H¹(D)→H¹(T_raw)→∏_{s∈S}Mの完全性を証明する。
実残差が右写像の核へ入り、その逆像がo_Pになること、細分化との可換性も含める。
K0/K1のincidence生成とは同じ支持で比較し、微分・syzygyを持つ複体との同型を
Law値の一致だけから仮定しない。正の診断比較はG-142の同じadapter族で行う。

conormal比較では全表示の普遍ambient Bとprincipal-open siteを固定する。
G-139で構成する普遍equation systemのObservableとLaw idealをB_s、J_sへ同定し、
[Raw.shortComplex](../../Formal/AG/SemanticRepair/Conormal/LawGeneratedIdealPowerShortExact.lean)を
そのsiteへ制限して、(J²)_s=(J_s)²とZariski層化から標準conormal列へ同定する。
実現xで引き戻す前のJ/J²を保持し、lawfulな評価後の零idealへ置き換えない。
ambient lift B/J²→R′の制限κ:J/J²→Mについて、κ=0と同じliftがB/Jを経由すること、
選択差を除いた[κ]=o_Pを証明する。section liftと実現liftはこの写像で比較する。
宣言の忘却とZariski制限を混同せず、共有xを保ってxy−1を零へ送る
ℚ[x,y]→ℚ[x]の不存在を指定例として証明する。

### F. 全Artin試験・初回障害・有限上界

任意の可換環k上で、同じ型・階数・生成元を持つOへ有限の補助演算
Y_j=F_j(O,Y₁,…,Y_{j−1})と追加Law G_α=0を置いてPを作る。原始代入による消去から
残差Ḡ_α、ideal sheaf 𝒥_uを生成し、全RでSem_P(R)をその零点へ自然に同定する。
marked実現の閉埋め込み、Realのfull faithfulな関手・essential image・自己同型群の
同定を証明する。追加Lawが空なら全Rで同値になる。

体k、有限表示O・P、x∈Sem_P(k)、a=u*xについてA=𝒪_{M_O,a}、m、J=(𝒥_u)_aを作る。
剰余体k、極大ideal n_Rにn_R^{r+1}=0を課す全局所Artin k代数上のpointed deformationに
ついて、比較が自然同値 ⇔ J⊆m^{r+1} ⇔ 普遍観測変形A→A/m^{r+1}がliftする、を
全r≥0で証明する。普遍商のArtin性も有限表示から証明する。
J≠0ならν=max{n | J⊆m^n}、J=0ならν=∞とし、Krull交叉から最大値、初回失敗r=ν、
全次数での同値 ⇔ J=0 ⇔ aのあるopen近傍での同型を導く。全R上の同値は𝒥_u=0で
判定する。曲線jetや有限サンプルによる試験とは量化を区別し、係数を動かすjet functorも
含めてn1020 §10・15の先行理論と比較する。

有限νの普遍拡大A/m^{ν+1}→A/m^νとkernel I=m^ν/m^{ν+1}から、
κ_u:J/J²→I、f↦f mod m^{ν+1}を構成し、Eの指定観測liftの非零障害へ送る。
ν≥2では観測liftを変えるderivationもJを消すので、そのP実現自体のlift不存在を示す。
ν=1では指定観測方向の不成立を結論し、基点の定値liftと区別する。
原始tensor残差と同型の共有演算Z_αを持つ二文脈Z_α=Ḡ_α / Z_α=0を作り、
任意の指定観測liftで局所liftを構成する。全syzygyからHom_{A/J}(J/J²,I)→I^qの
単射と像を構成し、κ_uを実際の共有部の差へ送り、その零性と合法修復をEへ同定する。

chart、改名、相互導出を持つ冗長Law、定義だけの補助演算の追加・消去に対して
J、ν、κ_uと比較を自然にする。F冒頭の型のreading u,vの合成について、追加idealの
逆像からν(vu)=min{ν(u),ν(v)}を対応する点の局所環で証明する。
pointed Realは還元同型を持つgroupoidとして定義し、Artin環上の生成元のliftから
同じ検出次数を比較する。生成元数m_v≥n_vと選択を変えてもνとpointed Realの判定は
一致し、指定観測liftの相対fiberは空またはcontractibleになることを証明する。

自由観測chart k[z₁,…,z_d]では原始式の積で加算、和で最大を取り、補助定義順に
代入して消去残差の次数上界Dを生成し、J≠0⇒ν≤Dを証明する。
augmentation B₀→k₀、m₀、J₀⊆m₀を持つ一般係数版では、二つの冪零商
B₀/m₀^{r+1}、B₀/(J₀+m₀^{r+1})の任意base changeとの交換を証明する。
両者の射のkernel D_rについて変更後のkernelをD_r⊗k₁の像へ同定し、flatなときの
同型とfaithfully flatなときの零性反映を証明する。これは剰余体kのArtin判定と分ける。

### G. 有限graphの実adapter・SAGA・全修復

可換環R、一辺以上を持つ有限連結単純graph Γ、その向き、μ∈R、offset b_e∈Rを
量化する。各頂点の台帳R²・公開状態Rについて、原始加群演算とLawから
p=(1,1)、v=(1,−1)ᵀ、i_λ=(λ,1−λ)ᵀ、j_μ=μv、g_b=I+bvpを構成する。
固定pの族はG-140 Pの一型の係数表示とのmarked同型を使い、p i=id、p j=0から
apply_u(x)=x+i(u)、compact_t(x)=x+j(t)、read=pの全有限語の公開意味保存を証明する。
入力u,tは比較の両側で同じ外部入力とする。
g_b^{-1}=g_{−b}、p g_b=p、g_bv=v、g_bi_λ=i_{λ+b}、g_bj_μ=j_μ、g_cg_b=g_{b+c}
から、実操作のadapter整合がλ_j−λ_i=b_eと同値になることを示す。

Γの頂点と辺を点とし、U_i={iと接続辺}を最小開集合とする有限Alexandrov空間を作る。
U_iの非空連結性、二重交差が辺一点または空、相異なる三重交差が空であることを証明し、
全実交差、AAT site、topologyに属する被覆、MonomorphicOrderedCover、K1支持を生成する。
g_bのdescentから局所自由・局所定数の層E_bと0→R̲v→E_b→R̲→0を構成する。
ker p≃Rv、Ob(V)=Γ(V,R̲v)、State(V)={s∈Γ(V,E_b) | p(s)=1}と層条件を導き、
State(X_Γ)と実大域操作i(a)=asを同定する。E_bのdescentとiの存在を分ける。

[SAGA EquationLift](../../Formal/AG/SemanticRepair/Saga/EquationLift.lean)のLiftFiberDataを
上のsectionとbase=1から生成し、exact_at_middle、restriction、単射性を放電する。
liftSystemからAffineCoefficientLiftSystem、局所実現からCoefficientLiftAtlasを作り、
residualClass_isZero_iff_matching_correctionを同じ入力へ適用する。
空交差・対角・順序反転とStateの層条件から全pairの一致を実sectionへ戻す。
[PartIVBridge](../../Formal/AG/SemanticRepair/Saga/PartIVBridge.lean)の
SitePresheafData.ofObstructionSheaf、incToCoverRelativeH1を同じObへ適用し、
omitted pair/tripleの零係数を実交差から証明して指定IncH1類とCoverRelativeHn 1を同定する。
全siteのAtomOccurrenceReadingをこの有限空間から仮定しない。

SAGAの増加pairから指定向きへ、次数0は恒等、次数1は向きの符号を掛けるTを作り、
Tδ⁰_SAGA=d⁰_Γを証明する。三角形ではT(c₀₁,c₀₂,c₁₂)=(c₀₁,c₁₂,−c₀₂)。
交差をj側で読み、r_e=λ_j−λ_i−b_e、o_b=[r]=[−b]=δ(1)を同定する。
State(X_Γ)≠∅ ⇔ o_b=0 ⇔ b∈im d⁰を証明し、非空な全解をOb(X_Γ)≃Rのtorsorとする。

頂点の変更可能集合からH_V⊆R^Vを生成した場合はb−d⁰λ∈d⁰(H_V)で存在を判定し、
全解をker(d⁰|_{H_V})のtorsorとする。SAGAの引く補正とはa=−c_SAGAで比較する。
辺の変更可能集合からH_E⊆R^Eを生成した場合は[b]+[Δb]=0でoffset修復を判定し、
全解をker(H_E→H¹(Γ;R))のtorsorとする。各修復後の操作のH⁰の自由も保持する。
この同じOb、State、r、o_bをG-142の診断・Atlas比較へ渡す。

### H. 同じ構成を通す指定例

以下をE–Gの原始生成・比較へ通す。係数を記さない有限表示例ではkを任意の体とする。

1. ℚ上のc+d=1を基準c=d=0から修復し、全域、Δd=0、全固定で解集合が順に直線、
   単点、空となることを示す。局所Law・観測を保つ部分加群も同じデータで計算する。
2. Law t²=0のt=εはk[ε]/ε²上で成立しk[ε]/ε³へlift不能となる。
   比較用のLaw t=0では同じ基準点の一次自由度が零であることを示す。
   残差(t²,t³)のsyzygy(t,−1)と、ℤ上の(z²,2z²)のsyzygy(−2,1)から、冗長Lawを
   除いたH⁰・H¹・障害との同定を証明する。後者はF₂への特殊化も同じ比較へ通す。
3. k=ℚ[t]、三文脈のx₁−x₀、x₂−x₁、x₀−x₂を、R=k/(t)、基点0で読む。
   syzygy(1,1,1)によりH¹(T_raw)≃ℚ、H¹(D)=0となる。一方、最後のLawからtを引くと
   各文脈はk/(t²)へliftできるが、大域ではH¹(D)≃ℚの非零障害が残る。
   両入力で基点のLaw値・支持が一致することも示す。
4. 二文脈Y=T² / Y=0、共有T,Yで、T=ε、Y=0をk[ε]/ε²からk[ε]/ε³へ比較する。
   任意の観測lift T=ε+aε²に対して局所liftは存在し、合法修復係数C⁰=0、C¹=(ε²)に
   κ_uと同じ非零[ε²]が残ること、ν=2を証明する。
5. 全N≥1でY₁=T²、Y_{j+1}=Y_j²、Y_N=0を消去し、J=(t^{2^N})、ν=2^N、
   構文上界の鋭さと初回lift不能を示す。観測Law Y=T^Nと追加Law Y=0ではν=Nとなり、
   表示上の一次式だけでは検出次数が決まらないことを示す。
6. ℤ[t]、J=(2t²+t³)、t↦0で、orderはℤ・ℚ上で2、F₂上で3となる。
   D₂=2ℤt²のtensorは非零でも変更後のkernelは零となり、Fの像の比較と一致する。
7. 任意の体k上の無限表示T_i=T_{i+1}²ではA_∞=colim k[t_i]を原式から作る。原点局所環でm=m²、
   t₀≠0、全有限Artin変形は定値と証明する。T₀=0を追加しても全次数の比較は同値だが、
   A_∞は整域、A_∞/(t₀)のt₁は非零平方零なので両schemeは同型でないことを示す。
8. Gの三角形0→1→2→0で、負のoriented sumによりo_bをΣb_eへ同定し、holonomyの
   大域操作固定条件もΣb_e=0とする。ℤ・ℚでb=(1,2,−3)の全解は(t,t+1,t+3)、
   b=(1,0,0)は局所実現とE_bがあっても大域操作を持たない。
   ℚ上で後者のoffset修復域を全辺、一辺、空とした全解は平面、単点、空となり、
   各修復後に一自由度が残る。λ=0、b=(1,2,−3)では全頂点固定の場合だけ修復不能となる。

さらにG-140 Pの同じsnapshot protocolと、その意味保存条件μδ=0を用いる。
原始追加E=μδ、E=0をFの消去へ通し、同じ意味保存係数fiberをV(μδ)へ同定する。
体上の原点の特異性、ν=2、各軸方向の全次数lift、δ=μ=εの二次lift不能を証明する。
任意の候補δ=ε+aε²、μ=ε+bε²の残差ε²、実read差−ε²、Eの相対障害、
二文脈E=μδ / E=0の合法修復係数C⁰=0、C¹=(ε²)を同じ写像で比較する。
固定pの族と一型の係数表示のmarked同型を用い、unmarkedな同型へ自動移送しない。

G-140 Pのfinish_snapへの修正ではこの障害が消えることを、同じ観測と状態比較で示す。
さらにbefore・p・語翻訳を固定し、目的D(μ),D(δ)をG-140 Eの探索fiberとして構成する。
旧式のV(μδ)では一方の目的だけならG_m、両方なら空であることを全R点で比較する。
許容編集式finish_ρ(B,C,h)=(B+μh,C−μ((1−ρ)C+ρh))から
g_ρ=μ(1−ρ)(h−C)を生成し、BusyをV(g_ρ)とする。
begin・applyのg_ρへの代入、finishのread差、begin; apply_1; finishから、
全語の意味保存とμδ(1−ρ)=0を同値にする。
目的D(μδ)の下でρ=1が強制され、全解がG_m²、状態が全R³、
選ばれる式がfinish_snapになることを原始編集族から導く。
旧Busy Lawを固定する編集域では、同じ目的の解が空のままであることも証明する。
体上の非零目的と全R上の単元条件を区別し、この編集族における全解の比較をDへ通す。

ℚ上でGのg₁はλ=μ=1をλ′=2,μ′=1へ運ぶが、後者ではIdle(0,0)から
begin; apply_1; finishのreadが2となることを証明する。
同じμ=1でg₁(compact_all(1,0))=(2,−1)とcompact_all(g₁(1,0))=(1,0)を比較し、
原子操作のadapter保存を拡張した観測言語へそのまま移せないことを証明する。

## 前提・構成台帳

| 対象 | 役割 | 構成・証拠 | 使用先 |
| --- | --- | --- | --- |
| 観測・作用・adapterの原式 | 入力 | A–Bの全射分類 | change scheme・複体 |
| 複体・制限射・cotangent・比較 | 構成義務 | A–Bの同じ原式から生成 | 大域障害・微小lift |
| 交互列aとD(2),D(3) | 指定証人 | Cの全段・局所解と非零類 | Čech・Ext・lim¹の一致 |
| ML性・有限安定性・証明規則 | 別々の放電義務 | Dの原始構造から導出 | 有限certificateの十分性 |
| 許容編集・目的・係数域と探索fiber | 入力と先行構成 | G-140 E、Dの生成・全解回収・復元 | 目的を満たす設計候補と不存在 |
| 有限表示、平方零拡大、原始reading、指定観測lift | Eの入力 | 独立Sem、全syzygy、残差、合法修復を生成 | 実lift・相対fiber・conormal比較 |
| 体、有限表示、実現点／自由観測chart | Fの各系の仮定 | Noetherian性・Artin商／構文上界を別々に導く | 全Artin検出・有限上界 |
| 有限graph、μ、offset、許可変更集合 | Gの入力 | 実adapter・全交差・State・LiftFiberDataを生成 | SAGAの零性と実操作、G-142の診断比較 |
| Hの原始表示・phase・試験環 | 指定証人 | E–Gと同じ生成・比較へ通す | syzygy・検出次数・修復・操作輸送の検査 |

## 完了条件

A–Hの一般比較と指定例をLeanで証明し、native射・scheme・cotangent・Čech・lim¹の
全写像を同じprimitive入力に遡ってreportする。
Milnor列の引用だけでnative比較を、有限段の成功だけで大域的存在を済ませない。
無限個のLawを固定有限数に打ち切った定理はB・Cの代用にならない。
反証と一般比較に残る研究義務は明示し、特殊化の達成で主目標を取り消さない。
Gの実操作・Ob・State・指定障害は同じ入力から生成し、SAGAのmatchingから実sectionへ
戻す比較を完了対象に含める。Hの無限Artin例はFの有限表示定理への反例とは扱わない。
固定主張への反証は、その量化に属する原始入力と破れる比較・存在判定を示して記録する。

成果物はresearch/lean/ResearchLean/AG/のLean証拠と、
research/reports/G-141-aat-coherent-repair-effectivity.mdの宣言・前提対応に置く。
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。
