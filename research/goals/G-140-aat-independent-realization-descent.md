# G-140-aat-independent-realization-descent — 実現の独立構成とdescent

- `id`: `G-140-aat-independent-realization-descent`
- `status`: `draft`
- `research mode`: `target-theorem`
- `tracking issue`: [#6359（設計）](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。個別のResearch Loop Issueはactive化時に定める。
- 設計: [多項式特殊化ノート §2–3](../../docs/note/n1020_shigure_polynomial_specializations.md#2-既存成果との接続)
- 依存: [G-139 A](G-139-aat-law-coefficient-extension.md#a-式の係数自然性)

主経路は[n1019](../../docs/note/n1019_shigure_representability_design.md)のG-149〜G-152にある。
本カードは多項式特殊化を構成する。主経路と同じ対象・射・Law評価への比較を要し、
本カードの達成だけでSHIGURE全体の達成とはしない。

## 研究目的

Atom / Lawから、schemeへの射と独立な実現を構成する。AATの文脈上の組立てと、
係数代数上の加群・演算のdescentを接続し、局所座標を持つ実現の族を研究対象にする。

## 固定target

### A. 原始表示と意味の一致

任意の可換環k、ノート§3.1の表示P、k代数Rについて、同§3.2のSem_P(R)、
qを持たず非可逆射も持つ演算保存写像の圏、最大部分groupoid Real_P(R)を構成する。
加群・演算・Lawの解釈を先に定義し、schemeやHom(Spec R,−)を定義に使わない。

同じ原始表示から、Atomの五座標・configuration・各実現の`ArchitectureObject`を
構成し、型・生成元・演算・Lawの有限式を読み戻す写像を与える。
基底chartごとに、Lawをまだ課さない構造定数の族RawCoeff(P,K)とambient B=k[z]を構成する。
原始係数Atom (座標,値)のfamilyを値のgraphとして、encode_K:RawCoeff(P,K)→ArchitectureObjectと
coeffOf_Kを生成し、coeffOf_K(encode_K(c))=cを証明する。各座標の値が一意に読めないobjectの
decodeは固定した零tupleとする。演算の型・式・出現は別の宣言Atomから読み戻す。
Lawfulな実現だけをencodeして充足同値を循環させず、任意の既存objectの分類も要求しない。

Spec Bの点とLaw成分のmarkerからAAT contextと係数site S_Pを生成し、
j_B:PrincipalOpen(Spec B)→S_P.categoryを点支持・局所化・実際のrestrictionから構成する。
普遍係数のobjectをa_univとする。普遍equation system E_Bではj_B上のObservableをB_s、
symbolic violationを原式の全残差成分f_iの制限とする。object residualはcoeffOf_Bを使った
同じ原式の評価から構成し、a_univでf_i/1に一致することを証明する。成分marker以外のAtomでの
violationとresidualは零とする。open被覆、交差、環・生成idealの比較と自然性を含める。
これはBから生成する係数siteであり、入力Pの宣言siteとは分ける。

任意のraw ambient点x:B→Rについて、a_x=encode_R(x(z))と別のequation system E_xを作る。
E_xの係数siteはSpec Rの点と同じLaw成分markerから生成する。同じprincipal-open添字から
j_xでD(x(s))のcontextへ送り、そのObservableをR_{x(s)}とする。
E_xのsymbolic violationはf_i(x)/1、任意object Aのresidualは原式をcoeffOf_R(A)で評価して
R_{x(s)}へ局所化した値とする。評価射と指定objectの比較を次で固定する。

```math
\mathrm{ev}_{x,s}:B_s\longrightarrow R_{x(s)},\quad b/s^n\longmapsto x(b)/x(s)^n,
\qquad
\mathrm{ev}_{x,s}\bigl(\mathrm{res}_{E_B}(a_{\rm univ})\bigr)
 =\mathrm{res}_{E_x}(a_x).
```

全contextでの定義は、その点Atomの支持の内部U_Wを取り、ObservableをΓ(U_W,O)として作る。
raw係数の原式評価をglobal sectionからU_Wへ制限してresidualを定義する。readable morphismが
U_source⊆U_targetを与えることを支持から証明し、j_B・j_x上で上の局所化へ同定する。
従ってEquationLawfulが量化する像外contextも同じ定義で扱う。
全required Lawについてrestrictionとの可換性を証明する。係数変更自然性はencoded raw tupleと
指定object a_x上で述べ、malformed objectのdecode全体へは要求しない。D(1)を含むことから
E_x.EquationLawful(a_x) ⇔ 全f_i(x)=0 ⇔ 独立な原式解釈で全Lawが成立、をraw ambient点全体で
証明する。E_Bの残差の零性をこの評価後の零性へ同一視しない。x(t)=0では評価先R_0は零環であり、
これは逆像open D(x(t))が空であることに対応する。一般のtest schemeでは同じ逆像open上の層へ延長する。
全contextからΓ(T,⊤)への評価を要求する既存`EquationArchitecturePoint.evaluation`は使わず、
この逆像open上の評価を新規構成する。conormalはE_Bのidealを先に生成してからxで引き戻す。

### B. 係数関手と生成元

全てのk代数射R→Sに対し、tensor積による作用を構成する。
SemではKの像、商、演算の移送と恒等・合成を証明し、CAlg_k→Setの関手を得る。
Realではtensor積の単位・結合同型を与え、単位図式とpentagonを証明する。
flatnessを加えず、projective quotientの分裂をKの移送に使う。

生成元を持つ実現のgroupoidからSemへの同値を構成する。各qを保つ射の一意性、
同型類とK表示の対応、係数変更との整合を含める。生成元を忘れる
Sem_P(R)_disc→Real_P(R)も同じ加群・演算から作る。

### C. 二種類のdescent

原始宣言の任意の文脈とその合併被覆について、Semの制限とmatching familyからの
一意な組立てを構成する。型を含む文脈はその階数と全生成元を含み、Lawと演算の
全参照が同じ局所文脈にあるというノート§3.1の条件を使用する。
非可逆な演算保存写像についても分離と組立てを証明する。

任意のZariski被覆Spec R=⋃D(f_i)について、Semの等化子条件とRealのdescent圏への
同値を証明する。Realについてはfppf被覆にも拡張し、局所加群・演算・同型cocycleから
実現を生成する。局所自由性、指定階数、Lawの成立が降下することを示す。
AAT文脈制限と係数側制限が可換で、二つの組立て順序が同じ実現を与えることも示す。

### D. 既存再構成との接続と指定例

新しい原始readingと局所モデル圏を定め、CからHomの分離・組立てと対象の組立てを
得る。既存の`LocalReading.homEquiv`等を使う場合は、そのΛ・値の圏・matching条件と
生成した前提を特定する。G-124の`Parameter`の既存各分岐との同一視は入力にしない。
scalar式については`IndependentPolynomialExpressions`および係数点の`points_iff_map`
へ接続し、元の多項式の評価が変わっていないことを証明する。

ノートW1–W3・W8をA–Cの同じ構成へ通す。W1で合法・非合法な操作、W2で二つの局所基底と
大域のq、W3で0とεの区別を示す。W8では二つの文脈にそれぞれの往復Lawと全参照を置き、
共有表示が一致する族の組立てと、共有kernelが異なる族の組立て不能を証明する。
Lawをどの文脈にも置かずに局所Lawfulnessから全体のLawfulnessを導かない。

### E. 操作意味論への忠実な接続と射程

ノート[§11](../../docs/note/n1020_shigure_polynomial_specializations.md#representation-scope)の
有限状態・単項操作表を、任意の非零可換環R上の自由加群へ線形化する。
基底状態の埋め込み、操作合成の保存、基底状態の識別の反映を証明する。
固定基底でのmatrixの像を、field上では各列のidempotence・相互直交・和1で特徴づける。
一般の環では直交idempotentによる局所的な集合写像になることを示し、
R=R₁×R₂で一つの集合写像へ戻らない例を構成する。
Bool ANDをℚ上へ多重線形化したとき、2e_trueで冪等Lawが失われる例も証明する。

ノート[§12](../../docs/note/n1020_shigure_polynomial_specializations.md#development-change)の
加群上の名前付き状態作用と観測を原始演算・加法から構成し、G-126の
`OperationSystem` / `behavior`へ同じ対象・評価を接続する。
affine更新は加法と単項演算で生成し、二引数加法をtensor上の双線形写像にしない。
この対象へのArchSigの純粋affine Termの解釈では、元式評価と加群上の式評価の一致を
証明する。FactPointer上の写像との対応は、型付き解釈を構成した場合にだけ述べる。

有限phase graphを持つprotocolでは、各phaseのambient加群に状態を表す0引数演算と
多項式不変量を加え、合法状態をその実現fiberとして構成する。合法状態の集合自体に
局所自由性を仮定しない。各遷移式が不変量を保つことから全許可経路の意味を生成し、
元の全域操作系との接続は同じcontrolと不正操作の扱いを固定して行う。

### F. 台帳移行の同一入力上の実現

ノート[§16](../../docs/note/n1020_shigure_polynomial_specializations.md#ledger-example)の
before/after・比較p・apply・compact・readを同じAtom生成から構成する。
初期状態対応とpi=id,pj=0から、指定した原子操作の全有限語で観測保存を証明する。
R=ℚでwriteB/writeC間にもreadを許すλ=1/2,u=2の反例を証明し、観測言語の違いを明記する。
固定p=(1,1)の設計係数fiberと、固定実現の状態fiber p⁻¹(x)を別々に構成する。
rank 1・生成元数1の一型と単項λ,μだけの係数表示Oを別に作り、名前付き生成元が与える
Rとの同型から三型のコピーとp,i,jを復元する。Sem_Oと固定pのmarked fiberの自然同型を証明する。
異なる型のp_B,p_Cをidに等置するLawは使わず、unmarkedの同値はこの同型から推論しない。
同じ台帳にsnapshot・busy apply・atomic finishのphaseを加え、ノート§16.4の
不変量μ(h−C)=0と公開readの保存を実現fiberから構成する。任意の許可された有限経路での
保存とμ(1−λ)=0の同値、begin; apply_1; finishによる必要性を証明する。
固定pのコピー同定の下で、compact_all(B,C)=compact_t(B,C)|_{t=C}を派生原子操作として作る。
applyを挟まないbegin; finishとの一致を証明し、固定引数compact_tの一つとは同一視しない。
finish_snapへの修正ではBusyの状態Lawも除き、全ambient R³を状態とする。比較関係x=B+Cで
全係数の操作列を保存すること、旧合法状態の包含が旧・新の遷移と可換であることを証明する。

## 前提・構成台帳

| 対象 | 役割 | 出所・構成義務 | 使用先 |
| --- | --- | --- | --- |
| 原始表示P・任意のR | 入力として保持 | ノート§3.1。有限型・階数と小さい演算 / Law族 | A–D |
| 加群が有限局所自由で指定階数 | 実現の定義条件 | 局所基底からのdescentとbase change保存は証明義務 | B・C |
| Atom解釈、equation system、評価一致 | 構成・証明義務 | 原始宣言・式から生成 | A・D、G-141のLaw ideal |
| 多項式係数自然性 | 先行構成 | G-139 A | A・B |
| tensor積のcoherence・descent | 構成・証明義務 | 加群・写像の標準descentを同じ実現へ適用 | B・C、G-143 |
| 局所読み取りとassembly | 構成・証明義務 | 宣言の制限・合併、共有型の一致 | C・D |
| G-124の既存圏・同値 | 比較対象 | ノート§2の実際の型。適用できる前提だけを生成して使う | D |
| W1–W3・W8 | 構成・証明義務 | 同じAtom / Law生成経路 | D |
| 状態作用・観測・原子操作の選択 | 入力と構成 | 原始式の評価。原子性を式同値から導出しない | E・F |
| 有限状態の線形化・像・反例 | 構成・証明義務 | 固定基底と実演算表 | E |
| Term解釈・台帳移行 | 構成・証明義務 | 同じ式・source ref・Law | E・F、G-142・G-146 |

## 完了条件

A–Fの構成・関手則・descent・意味保存・射程の反例をLeanで証明し、
`research/reports/G-140-aat-independent-realization-descent.md`に元の意味、構成、
既存宣言への接続を記す。証拠は`research/lean/ResearchLean/AG/`に置き、
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。

固定主張が偽なら、原始表示と実現またはmatching familyから反例を構成し、
不成立の式・延長不能を証明して`target-refuted`として決着させる。
再構成やdescentそのものを入力に加える改訂は、このtargetの成功には数えない。
