# G-131：実修復方程式から観測十分性と出力別最適値を得る構成

[固定target A–E](../../goals/G-131-aat-repair-observation-duality.md)の証明方針を定める。
入力・出力・費用モデルはGOALに従う。G-130の同じ実操作・行列・候補名・復元を使い、
G-128への対応と数値出力の証明を接続する。

## 1. 一次仕様と依存

| GOAL | [n1017](../../../docs/note/n1017_aat_relative_boundary_repair_and_observation.md) | 構成の要点 |
| --- | --- | --- |
| A | §3.5・6.1 | 全実現、原始評価、実defectからのアフィン右辺、全範囲の修復との同値 |
| B | §6.2 | 双対・核包含・点安定化群、同じ問い合わせと述語の対応 |
| C | §6.4–6.5 | 既知情報fiber、出力条件、応答列の再現、下限と達成 |
| D | §6.3・6.5 | 同じ不能証拠の引き戻し・取得、観測計画、更新時の再利用 |
| E | §5.3・5.8 | 同じ実入力で全実現・最適値・数値出力・参照式を検査 |

G-130への依存は、Aの実修復・補正対応、Cの局所生成・復元、Dの候補方向と商、
Eの記号的右辺・更新、FとW1のアフィン実現である。
B・Cの線形代数と問い合わせ一般論はその入力型を用いて構成でき、実操作との最終的な
接続には、これらのG-130の対応を用いる。

## 2. 既存宣言の再利用と新しい対応

Research pathは `research/lean/ResearchLean/AG/` からの相対である。
G-130の宣言は同GOALの成果から参照し、宣言名と参照版を実装時のreport・Issueに記録する。
有限列挙・行列・実核の共通基盤は[G-130設計 §2](../G-130-aat-relative-repair-composition/README.md#2-既存宣言の再利用と新しい対応)に対応させる。

### 2.1 同じ観測・述語・問い合わせ手続き

| 既存path・宣言 | 再利用する結論と入力条件 | 新しく構成・証明するもの |
| --- | --- | --- |
| `MinimalCompatibilityObservations/PointObservation.lean` の `observe`、`pointStabilizer`、`exists_predicate_iff_sufficient` | 任意の群作用と部分群に対する、同じ点観測による所属判定と安定化群包含 | B：加法群の作用、原始評価との一致、同じ実修復述語、線形双対への対応 |
| 同ファイルの `minObservations`、`minObservations_attained`、`minObservations_eq_top_iff` | 最小十分集合と無限大の場合 | B・C：問い合わせindex集合との濃度の対応、既知情報の核への制限 |
| `ComparisonInformationLoss/ObservationKernel.lean` の `exists_observation_predicate_iff_ker_le`、`PointObservation.lean` の `hom_predicate_iff_original`、`hom_predicate_apply` | 群準同型の観測と部分群述語の因子化、実際の述語と各入力での評価の移送 | B：$`O_J`$ を加法群準同型として適用する。各原始問い合わせの回数は別途点作用へ対応させ、ベクトル観測全体を一回と数えない |
| `MinimalCompatibilityObservations/AdaptiveLowerBound.lean` の `QueryProcedure`、`QueryRun.replay_identity`、`identity_queries_sufficient` | Boolを返す判定手続きの応答列再現と下限 | B・C：アフィンfiberの成功基準点からの平行移動、原始問い合わせとの同一応答・回数、数値出力側の再現 |
| `MinimalCompatibilityObservations/QueryOptimum.lean` の `optimalQueries_eq_minObservations`、`finiteFixedProcedure_executable_optimal` | 判定の適応的最悪時最適値と、明示した群・点の列挙を用いる固定観測手続き | B・C：点 $`(j,a)`$ と原始問い合わせの相互シミュレーション、固定集合でのindex重複の除去 |
| G-130 A・C–F | 同じ実修復・候補・defect・記号的行列・復元 | A・D・E：未知値を全実現する族、既知情報と原始観測の取得経路 |

数値出力ではG-128のBool出力の判定定理だけで終えず、返された補正値が同じ右辺を
決定することを用いた下限を作る。G-128の既存の手続き型と対応させるのは判定側とし、
数値側は同じ質問・応答規則と補正または不能という出力を持つ型を構成する。

### 2.2 有限探索・双対・数値復元

| 既存path・宣言 | 再利用する部分と残る接続 |
| --- | --- |
| `ProtocolHolonomy/FiniteDirectDecision.lean` の `ExplicitEnumeration.toFintype`、`pi`、`product`、`MinimalCompatibilityObservations/FiniteAmbientTable.lean` の `ExplicitEnumeration.sigma`、`sum` | 有限体・基底・原始indexから $`\operatorname{Multiplicative}N`$ と点の直和の完全な列挙を作る。等値判定と、$`\ker((q_SB)\vert_N)`$ または $`\ker(B\vert_N)`$ への所属判定を明示する |
| `MinimalCompatibilityObservations/FiniteMinimum.lean` の `candidateSets`、`mem_candidateSets`、`minimumObservation`、`minimumOrWitness_correct` | 入力表から候補集合を生成して最小十分集合を選ぶ。線形核条件との対応と、点集合から原始index集合への変換を証明する |
| 同ファイルの `minimumOrWitness_optimalProcedure`、`minimumOrWitness_invisible` | 探索が実際に返した集合を最適な判定手続きへ渡す経路と、失敗時の識別不能証拠を使う。後者を成功基準点とAの全実現で元の二つの実入力へ戻す |
| Mathlib `LinearAlgebra/Dual/Lemmas.lean` の `Submodule.dualQuotEquivDualAnnihilator`、`LinearMap.range_dualMap_eq_dualAnnihilator_ker`、`mem_span_of_iInf_ker_le_ker` | B・D：商の双対、核包含と評価spanの対応。$`N=\ker L`$ 上へ制限し、同じ不能証拠の値を取得する線形結合へ戻す |
| Mathlib `LinearAlgebra/Isomorphisms.lean` の `LinearMap.quotKerEquivRange`、`Submodule.quotientQuotientEquivQuotient` | A・B：$`\operatorname{coker}D_S\cong\mathsf O/\mathsf R_S`$、$`\mathsf V/\ker(q_SB)\cong\operatorname{im}(q_SB)`$。同じ $`D_S,q_S,B`$ を代入し、代表元での評価一致を示す |
| `Formal/AG/Measurement/FiniteRegime.lean` の `FiniteLinearSystemSolver.ofFiniteField` | C・D：既知情報と修復条件の連立、観測取得後の求解に使える有限探索の定義。`solve_isSome_iff` だけでは返却値が解であることは得られないため、具体的な探索の返却値の正確性と明示入力での実行可能性を追加検証する |

判定側では $`\Gamma=\ker((q_SB)\vert_N)`$ に最小集合探索を適用する。
数値側の十分集合の探索には $`\ker(B\vert_N)`$ を使えるが、そこで得るBool手続きは
修復の数値出力そのものではない。同じ最小集合から右辺を復元し、正しい補正を求めて、
G-130の同じ復元へ渡す手続きを構成する。これはCの数値出力の達成証明である。

`LocalSemanticReconstruction/CSFiniteValueQueryBridge.lean` は有限値表によるHomの識別を
扱うため、この数値修復出力の最適値には入力・出力の対応が別途必要になる。
`ObstructionDiagnosticBridge` のČech障害と診断の比較も、今回の同じ実defect・候補列・
原始問い合わせへの対応を自動的に与えない。AはG-130の実操作への往復から構成する。

## 3. 原始入力からのアフィン方程式

構造と核輸送を固定し、各基準辺・比較の未知成分のパラメータ表示から実経路を合成する。
各面の負号付きdefectを計算して $`b_0,B`$ を生成し、全実入力に対する評価等式を証明する。
実修復の存在は、G-130の同じ復元によって $`q_S(b_0+Bv)=0`$ と対応させる。

識別不能な二点を入力空間で得た後には必ず $`X_v`$ へ戻す。一般族の全実現条件と、
Eの平行移動による具体的な全実現を区別する。
問い合わせの実評価との一致も全 $`X`$ に対する等式として持ち、入力座標だけの証明を
元の操作の観測へ移せるようにする。

## 4. 線形観測と点作用

修復可能点から平行移動し、部分空間 $`\ker(q_SB)`$ を修復述語にする。
線形写像の核と双対の像の対応から、核包含と評価spanの条件を対応させる。
実現される障害方向は $`\operatorname{im}(q_SB)`$ として扱い、Aの商同型と同じ写像で追う。

点作用は $`j`$ ごとの $`k`$ のコピー上の平行移動であり、作用則を評価の線形性から示す。
$`(j,a)`$ の返答は $`a+\lambda_j(v)`$ なので、原始問い合わせ一回と既知の加算で
点観測一回を模倣できる。逆向きは $`(j,0)`$ を使う。
複数の点が同じ $`j`$ を持つ固定集合では、index重複を除いても情報が増減しないことを示し、
最小点数と最小index数を一致させる。手続きの再問い合わせはGOALどおり回数に含める。

## 5. 既知情報、出力、適応的下限

既知情報が一般の内容の場合は、残る実入力族上の観測fiberごとに判定・数値出力の
十分性を特徴づける。線形な情報の場合は $`Lv=s`$ と修復方程式の連立から、
修復可能な基準点の有無を有限に決める。
基準点があれば $`v=v_*+n`$、$`n\in N=\ker L`$ と移し、同じ問題を $`N`$ 上で扱う。

基準点での実行の質問集合を $`J`$ とする。$`n\in N\cap\ker O_J`$ なら、
$`v_*+n`$ は適応的な手続きでも同じ質問・返答列を再現する。
判定では成功を保つ条件が $`q_SB n=0`$、数値出力では同じ $`h`$ が返るため
$`D_Sh=b_0+Bv_*=b_0+B(v_*+n)`$ から $`Bn=0`$ を得る。
繰り返しを含む実行回数は質問集合の濃度以上なので、両出力の最悪時下限を得る。

上限では十分な固定集合を全て読み、判定側は残存障害、数値側は右辺を復元する。
後者は有限線形求解で補正を作り、禁止辺へ零を補い、G-130の復元で実操作へ戻す。
局所の具体的修復や値付き関係が既に伝えた値は、最初から既知情報へ含める。

## 6. 不能証拠と有限観測計画

G-130 Dの証拠が許容列上で零であることから残存商上の評価を得る。
その入力側の線形成分を $`\ell q_SB`$ とし、$`N`$ 上の制限が許された評価のspanに
入る条件を核包含と対応させる。既知の定数項と $`Lv=s`$ の寄与を合わせて実評価を復元する。
変更方向の有効性を検査する支持集合と、値を取得する問い合わせ集合は同じ評価から導く。

有限な $`J_0`$ の部分集合を列挙し、Cの核包含を行列で判定して最小集合を求める。
値取得後の線形求解と実修復への復元までを、停止と出力の正確性の対象に含める。
十分集合がない場合は核包含の反例 $`n`$ と修復可能点から二つの実入力を生成する。
構造が変わらない更新では、消去・復元の線形部分をG-130 Eから共用し、残る未知方向を更新する。

## 7. 指定例と証明の依存順

Eの主例はG-130 W1の同じデータを用い、二重に別の入力表示を作らない。
G-130の一般定理が与える補正と、Eの直接的な実関数合成を照合する。
$`S\ne\varnothing`$ で全入力が修復可能でも、具体的補正から $`x,y`$ が復元されるため、
数値出力には両値が必要であることを確認する。
入力更新・内部辺分割では、何が既知で、どの原始問い合わせが保持されるかを同じ操作で追う。
分割時の回数の一致は、この例で $`r_x,r_y`$ が変わらないことから示す。

| 数学的な段階 | 依存 | 終了時に対応させるもの |
| --- | --- | --- |
| 線形評価と観測作用 | G-128 | Bの十分性・双対・手続き対応 |
| 原始入力族と同じ方程式 | G-130の記号的生成・アフィン実現 | Aの全実現・実評価・修復述語 |
| 情報fiberと出力別の最適値 | A・B | Cの有限値・無限大・全不能と達成手続き |
| 不能証拠の取得・有限計画 | G-130 D・A–C | Dの実入力証拠と観測から実補正までの構成 |
| 同じ変換網・更新・出力言語 | G-130 W1・A–D | Eの全ケースと一般定理への接続 |

Leanの検証は[AAT guideline](../../../docs/aat/guideline.md#lean-build-運用hard-rule)に従い、
親が指定する単一の非aggregate fileのfocused checkと、必要な依存moduleだけの親による
targeted checkを使う。Research package全体のbuildは実行しない。
完了のreportには、実入力・観測表・述語・数値出力の各対応と、既知情報ごとの最適値を記録する。
