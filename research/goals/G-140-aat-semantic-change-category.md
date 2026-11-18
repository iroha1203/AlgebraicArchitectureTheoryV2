# G-140-aat-semantic-change-category — 意味を保つ全変更とその局所性

- `id`: G-140-aat-semantic-change-category
- `status`: `draft`
- `research mode`: `target-theorem`
- 関連メモ: [#6359](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。実行用tracking Issueはactive化時に定める。
- 設計: [n1019 §5–6・8](../../docs/note/n1019_shigure_representability_design.md)
- 依存: G-139の意味再構成・Law幾何。

## 研究目的

元の意味を保つ非可逆な変更、その合成、整合する局所変更の組立てを同じ幾何で回復する。
始域の実現・保存条件・許容変換仕様・評価条件から、全変更を分類するfiberを生成する。
局所変更を整合させる補正とその障害はG-141、指定障害と診断の比較はG-142が扱う。

## 固定target

### A. 非可逆射と観測

原始signatureのmodel圏において、実際のsort mapsからoperation/relation保存射を作る。
観測$`o`$と各operationを保つ$`h:A\to B`$の全体を$`\mathop{\mathrm{Chg}}\nolimits_o(A,B)`$と定義する。
元の状態mapからこの条件を検査し、全有限操作語の観測保存を帰納的に証明する。
非単射・非全射を含む全ての保存射を対象とする。

固定語彙の構造保存と、traceだけのbehavioral equivalenceを区別する。
操作語翻訳を持つ変更は、原始term substitutionと状態mapで定義して合成を構成する。
phase・stutteringを使うときはその翻訳と許可経路を明示する。
観測を強くするとChgがどう変わるかを同じ写像で比較する。

### B. 射の幾何と合成

G-139 Nの全Homのprofile表示と同A–Dのquantity引戻し・対応空間から、
各係数的実現$`\sigma`$の独立な変更modelと幾何的表示の全$`R`$での自然な同値を構成する。
さらにnative基点で元のChgの全Homを回復し、指定native点の係数移送と比較する。
copying familyとlinear familyは、それぞれの係数的実現に沿って全$`R`$で比較する。
各射を、その源・標的・quantity保存等式とともに表現する。
$`M_{\mathrm{before}}\times_{M_{\mathrm{obs}}}M_{\mathrm{after}}`$の点に加え、状態比較$`h`$とその保存条件を保持する。

$`N_n`$を$`n`$個の合成可能な実際の変更とその可逆な比較のgroupoidとして作る。
Segal同値、恒等、合成、coherenceとnativeの合成との一致を証明する。
groupoidの対象は非可逆な変更を含む列であり、射はその列の可逆な比較とする。
同型な原始表示、definitionalな補助演算の追加・消去について、この全構造を比較する。

状態射を$`h_{01}:X_1\to X_0`$、$`h_{12}:X_2\to X_1`$と取る場合の
$`h_{02}=h_{01}h_{12}`$と語翻訳の合成を証明する。逆向きの添字図式は反対圏のnerveで表す。
状態schemeのchart $`X_i=\mathop{\mathrm{Spec}}\nolimits(A_i/I_i)`$では原始式から$`H^\#:A_0\to A_1`$を生成し、
$`H^\#(I_0)\subseteq I_1`$とlawfulな状態への一意因子分解を同値にする。
操作・観測の残差も同じ商環で評価し、全許可語保存と合成へ接続する。
一般のideal所属条件とambient恒等式を分け、$`R[y]/(ay)`$内の$`y=0`$が$`D(a)`$を与える例を含める。
導出witnessを使う表示では選択差を同一視し、元の全Homとの全単射を証明する。
状態射、quantityの反変引戻し、比較moduli上の点、両端へのspanを別々に同定する。

### C. 文脈と係数のdescent

原始宣言・witness・Law supportからAAT文脈coverを生成する。
別に係数schemeの被覆を固定する。二つの制限の可換性を構成し、
対象・全Hom・観測保存・合成のdescentを同じprimitive mapsから証明する。
被覆はLaw supportを含めて生成し、totalityと有限supportも制限・組立てに保つ。

平方零lift、文脈に沿う組立て、fragmentの延長を、それぞれどのfiberの問題か定義する。
matching familyから対象・状態比較・観測保存を持つ実際の変更を組み立て、その一意性を証明する。
原始宣言から被覆・全制限・matching条件を作り、sheaf条件を証明する。
局所変更をmatchingへ補正する存在問題はG-141へ接続する。

### D. 同じ意味を保持していることの試験

全lens Hom、全protocol自然変換、G-124の同じHom query、
G-126のquotient repairを比較対象にする。
非可逆な必須例として、$`V=\mathrm{Bool}`$、hidden担体$`K`$を持つlensの射$`K\times V\to V`$を、
get/put保存・全Hom分類・合成とともに幾何へ運ぶ。$`\lvert K\rvert>1`$なら同型ではないことを示す。
G-126の共通behavior上端を保つ商修復と、指定adapter間の変更が別fiberであることを示す。
前者の組立て原理の仮定と後者のfiberの入力を照合し、各fiberの存在条件を比較する。

### E. 評価条件を満たす全変更のfiber

固定source $`a:\mathop{\mathrm{Spec}}\nolimits R\to M`$と原始表示の許容変換仕様$`H`$を入力とする。
$`H`$は変換可能な宣言、固定する部分表示、許す型付きterm代入、係数・補助sort・演算・phaseの
導入と忘却の規則を指定する。各規則のsort・入出力・Law支持・固定宣言の像を保持し、
規則族は任意の濃度を許す。全候補族$`E_H`$を原始構文から生成する。
状態比較$`h`$は実際のsort maps全体で量化し、termで定義できる射も含めた全Homを保持する。
候補に$`h`$・語翻訳$`\tau`$を保持し、
保存条件から$`C_H`$とsource/target射$`s,t`$を構成する。集合値の評価対象$`T`$とその部分関手$`P\hookrightarrow T`$を
評価条件として指定し、式とquantityの評価規則から自然変換$`v:C_H\to T`$を構成する。

```math
F_{a,H,P}=(C_H\times_{s,M,a}\mathop{\mathrm{Spec}}\nolimits R)\times_{T_R}P_R
```

を構成する。
全係数拡大に自然に、独立に定義した「$`a`$から$`H`$に属し、意味を保ち、評価条件を満たす変更」への同値を証明する。
sourceの変更、許容変換域の包含、評価条件の引戻しとの可換性を含める。
同型比較を持つ場合は$`P,T`$を離散groupoidとして2-fiberを使い、
評価条件へのliftが空またはcontractibleになることから、条件を満たす変更そのものを分類すると証明する。
候補族は任意の濃度を許し、表示系も同じ比較で扱う。

$`H`$の変換規則から解集合を生成する。優劣の順序は選んだ係数域の解の上で指定し、
その順序を保つ比較について評価と順位を保持する。
返した点から状態比較・操作・targetを回復する。保存する意味Lawと変更可能な表示のLawを
区別し、候補は固定と宣言されたLawを全て保持する。
共通sourceからの二変更の併用と、合成可能な二射の合成を別のfiberとして構成する。
有限な計算手続きの正しさ・完全性と障害の計算はG-141がこのfiberに対して証明する。

### P. 階数変更と操作言語を持つ多項式特殊化

[n1020 §12・16](../../docs/note/n1020_shigure_polynomial_specializations.md#development-change)
のbefore/after・状態比較$`h`$・観測・操作語翻訳$`\tau`$からcomparison presentationを作り、
G-139 Pのschemeと独立なmodelの同値へ通す。両端の状態階数が違う場合も量化する。
原始式から両端へのspanとそのfiber、合成可能な比較のfiber productから合成比較への射を
生成し、Bのnerveへ同定する。unmarked版では同型を保持した2-fiber productを使う。

加法・単項演算から状態作用を作り、G-126のOperationSystem / behaviorへ同じ評価で接続する。
加法・定数・単項線形演算から生成した任意の型付きaffine termについて、
原始構文の評価と加群上の式評価の一致を証明する。
二引数加法は直和上の線形写像として扱う。有限phase graphでは各phaseの状態を
0引数演算と不変量の実現fiberとして作り、遷移後の不変量と観測差が元のidealに属することを
原始式から証明する。この比較から全許可有限経路の観測保存を導く。

台帳の同じAtom・apply・compact・read・比較$`p`$・初期状態対応を使い、次を必須例とする。

1. $`pi=\mathop{\mathrm{id}}\nolimits`$、$`pj=0`$から全原子操作語の保存を証明し、係数実現を$`\mathop{\mathrm{SL}}\nolimits_2\times\mathbb A^1`$に同定する。
   $`p=(1,1)`$のmarked fiberは$`\mathbb A^2_{(\lambda,\mu)}`$、固定状態のfiberは$`p^{-1}(x)`$として区別する。
   rank1・一生成元・unary $`\lambda,\mu`$の表示から各型のコピーと$`p,i,j`$を回復し、marked fiberとの
   自然同型を構成する。この比較は各型のコピーを明示したmarked fiberの同型とする。
2. writeB/writeCの途中にもreadを許す場合、$`R=\mathbb Q`$、$`\lambda=1/2`$、$`u=2`$で保存が失われることを示す。
   原子操作語の保存と、観測言語を広げた場合の保存を同じ状態・評価で比較する。
3. snapshotではBusyの不変量$`\mu(h-C)=0`$を保持し、全許可経路の保存と$`\mu(1-\lambda)=0`$の同値を
   $`\mathop{\mathrm{begin}}\nolimits;\mathop{\mathrm{apply}}\nolimits_1;\mathop{\mathrm{finish}}\nolimits`$の必要性を含めて証明する。意味保存の像を$`V(\mu\delta)`$、$`\delta=1-\lambda`$へ同定する。
   Busyの全ambient $`R^3`$上で同じ保存を要求した場合の条件$`\mu=0`$を、$`(B,C,h)=(0,0,1)`$から導く。
   $`\lambda=\mu=1`$では合法状態上の全語保存が成立することも、同じ$`R=\mathbb Q`$で示す。
4. $`\mathop{\mathrm{compact}}\nolimits_{\mathrm{all}}`$を固定引数$`\mathop{\mathrm{compact}}\nolimits_t`$への$`t=C`$の代入として生成し、applyなしの$`\mathop{\mathrm{begin}}\nolimits;\mathop{\mathrm{finish}}\nolimits`$と
   一致することを示す。修正版$`\mathop{\mathrm{finish}}\nolimits_{\mathrm{snap}}`$ではBusyの状態Lawを除いて全$`R^3`$を状態とし、
   $`x=B+C`$で全係数の操作列を保存すること、$`\mu\delta=0`$上で旧合法状態の包含が遷移と可換になることを証明する。
   $`R=\mathbb Q`$で旧状態Lawを残した$`\delta=\mu=1`$では$`\mathop{\mathrm{begin}}\nolimits;\mathop{\mathrm{apply}}\nolimits_1`$が閉じないことを示す。
   $`\mu=1`$の$`\mathop{\mathrm{compact}}\nolimits_{\mathrm{all}}`$は非単射で、固定引数$`\mathop{\mathrm{compact}}\nolimits_t`$とその有限語はtranslationであることも検査する。

同時変形のliftと、合成可能な意味保存射の合成は別のfiber問題として定義する。
Pの同じsnapshotを使った高次liftの存在・失敗はG-141の固定targetとする。
Eの必須例には、同じ比較$`p`$・語翻訳を固定した$`V(\mu\delta)`$と評価条件$`D(\mu),D(\delta)`$を用いる。
$`\mathop{\mathrm{begin}}\nolimits^*(\mu(h-C))=0`$、$`\mathop{\mathrm{apply}}\nolimits_u^*(\mu(h-C))=\mu(h-C)-\mu\delta u`$とfinishのread差からBの因子分解を導く。
型・操作署名だけを読む$`q_{\mathrm{type}}`$で旧finishと$`\mathop{\mathrm{finish}}\nolimits_{\mathrm{snap}}`$の像が一致する一方、
$`\mathbb Q`$上の$`\delta=\mu=1`$で同じ経路のread差が$`-1`$と$`0`$になることを示し、その評価への不十分性を証明する。

## 前提・構成台帳

| 対象 | 役割 | 構成・証拠 | 使用先 |
| --- | --- | --- | --- |
| 指定観測・操作・語の翻訳 | 入力 | Aの状態mapと可換式 | 全語の意味保存 |
| 係数的実現・そのnative比較 | 先行構成 | G-139 | Bの射と合成の幾何 |
| 文脈support・witness・係数被覆 | 入力と構成義務 | Cの二種類のdescentを区別 | 組立て比較 |
| matchingな変更・全制限・組立て | 構成義務 | Cの同じ原始maps | 局所から大域への射と合成 |
| 許容変換・固定部分・評価 | 入力と構成義務 | Eの構文生成、評価同値、source固定 | 全変更の探索fiber |
| 台帳・phase・状態比較・語翻訳 | 原始入力と構成 | Pの操作と不変量 | 一般の変更構成への同定 |

## 完了条件

A–E・Pの構成、全Homと合成の比較、descent、評価条件に相対的な探索fiber、指定例をLeanで証明する。
G-124・G-126への同一対象上の比較と必要仮定の放電をreportに記す。
比較の対象には、原始意味圏の全射と指定witnessを保持する。
固定targetへの反証は、同じ原始入力と破れる比較を示して記録する。

成果物はresearch/lean/ResearchLean/AG/のLean証拠と、
research/reports/G-140-aat-semantic-change-category.mdの宣言・前提対応に置く。
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。
