# G-125-aat-obstruction-diagnostic-bridge — 障害類と診断を結ぶ比較

- `id`: `G-125-aat-obstruction-diagnostic-bridge`
- `status`: `draft`
- `research mode`: `target-theorem`
- `tracking issue`: 未起票（active化時に設定）
- `paper`: [Rising Sea 構成マスター第2・3章](../../outreach/paper/rising-sea/paper-structure.md)、[数学棚卸し第2・3章](../../outreach/paper/rising-sea/mathematics-inventory.md)、[執筆準備](../../outreach/paper/rising-sea/TODO.md)

## 研究目的

第2章で局所データから生成する障害類と、第3章のLaw評価から生成する診断を、
同じAAT入力に由来する比較写像で結ぶ。指定障害類の対応と零性の保存・反映を示し、
既存のAtlasの診断不変性を、その障害の判定へ適用する。

対象は論文に採用する一つの入力族と、その入力族で扱うreading変更とする。
必要な成果はこの接続のLean証明であり、係数系全体の同型・統合や係数環の統一は
完了条件に含めない。既存の障害・SAGA・診断比較は、それぞれの定義と証明を再利用する。

## 固定target

A–Cを一つの接続定理の構成部分とする。量化順は、Aの入力族と構造条件の構成、
その条件を満たす任意の入力、その入力で許される任意の局所データ・reading変更とする。
入力族の定義と構造条件は、Atom・Law評価、係数の生成子・関係式、被覆・制限の
データから記述し、以下の比較・類の対応・零性判定を結論として導く。

### A. 共通入力と複体の比較

有限なSource・有限Law族・adequate reading・被覆とそのnerve・選択係数・局所データを指定する
一つの入力族を定める。第2章側は既存の `Ob` または `Q_E` による障害の構成を
一つ選び、選んだ構成の局所データと指定障害類を用いる。
第3章側は同じLaw評価と台からK0・K1のlaw-value係数と診断複体を生成する。
両側の係数、被覆・nerve、次数0–2の対応を特定する。

reading `q` における両複体を `C_ob(q)`、`C_diag(q)` と書く。
生成子・関係式と被覆・制限の比較から加法的な写像

\[
 \phi_q^n:C_{\mathrm{ob}}^n(q)\longrightarrow C_{\mathrm{diag}}^n(q)
 \quad(n=0,1,2),\qquad
 \phi_q^{n+1}d_{\mathrm{ob}}^n=d_{\mathrm{diag}}^n\phi_q^n
 \quad(n=0,1)
 \tag{A1}
\]

を構成・証明し、誘導準同型 `Φ_q:H¹_ob(q)→H¹_diag(q)` を得る。
第2章側には選んだ既存の障害複体、第3章側には
`TargetSupportedNerve.lawGeneratedComplex` を使い、既存の実体との対応を示す。

### B. 指定障害類と零性の判定

Aの任意の局所データ `x` から、第2章の指定障害cocycle `o_q(x)` と、
同じ局所データのLaw評価による診断cocycle `a_q(x)` を生成し、

\[
 \Phi_q([o_q(x)])=[a_q(x)],\qquad
 [o_q(x)]=0\ \Longrightarrow\ [a_q(x)]=0
 \tag{B1}
\]

を証明する。対応は、両cocycleの生成式と(A1)から示す。
さらに、採用する入力の生成子・関係式・制限に関する明示的な構造条件 `R_q`
を与え、その条件から

\[
 R_q\ \Longrightarrow\
 \bigl([a_q(x)]=0\ \Longleftrightarrow\ [o_q(x)]=0\bigr)
 \tag{B2}
\]

を任意の許される `x` について証明する。`R_q` 自体に(B2)や `Φ_q` の単射性を
入れず、零性の反映を局所の構造条件から導く。反映の対象はこの入力族の指定障害類とする。

### C. reading変更とAtlasへの接続

Aで許される粗いreading `q_c` から細かいreading `q_f` への変更について、
局所データ・係数・被覆の比較から準同型 `T_ob:H¹_ob(q_c)→H¹_ob(q_f)` を構成する。
診断側には同じ入力から生成される既存の `generatedComparisonH1Map` を `T_diag`
として用い、

\[
 \Phi_{q_f}\,T_{\mathrm{ob}}=T_{\mathrm{diag}}\,\Phi_{q_c}
 \tag{C1}
\]

を証明する。対応する局所データ `x_c,x_f` について
`T_ob([o_{q_c}(x_c)])=[o_{q_f}(x_f)]` も示す。
両readingの(B2)の構造条件と、既存のAtlasの `ConditionC` が成立するとき、
`T_diag` の既存の全単射定理を使って

\[
 [o_{q_c}(x_c)]=0\ \Longleftrightarrow\ [o_{q_f}(x_f)]=0
 \tag{C2}
\]

を導く。許容するreading変更と `ConditionC` の役割はAの入力族で明記する。

## 前提・構成台帳

| 対象・条項 | 役割 | 必要な構成・証拠 | 出所・使用先 |
| --- | --- | --- | --- |
| 入力族と許容する局所データ・reading変更：A | 構成義務。確定した族の各データは入力として保持 | Aの対象範囲と局所の構造条件 | 論文第2・3章の接続に用いる族を定め、A–Cへ |
| `Ob` または `Q_E` とその障害：A・B | 一つの既存構成を選択し再利用 | 係数・複体・指定障害類の既存実体との対応 | 第2章から(A1)・(B1)へ |
| law-value係数・診断複体・reading比較：A・C | 既存構成を再利用。共通入力からの接続は構成義務 | AのK0・K1入力と(C1)の実比較 | 第3章から(A1)・(B1)・(C1)へ |
| `φ_q`、`Φ_q`、cocycle対応、`T_ob`：A–C | 構成・証明義務 | (A1)・(B1)・(C1) | 生成子・関係式・制限の比較から零性判定へ |
| 反映条件 `R_q`：B | 局所の構造条件を定め、そこから反映を証明する義務 | (B2)。下記有限例では条件自体も証明 | 採用入力の構造から指定障害類の判定へ |
| `ConditionC`：C | (C2)の十分条件として保持 | 既存の `generatedComparisonH1Map_bijective` を適用 | 診断比較の全単射と(B2)から(C2)へ |

## 既存構成の参照

- 第2章の一般の障害：[ObstructionSheaf.lean](../../Formal/AG/Cohomology/ObstructionSheaf.lean)、[GluingMismatch.lean](../../Formal/AG/Cohomology/GluingMismatch.lean)、[CechComplex.lean](../../Formal/AG/Cohomology/CechComplex.lean)。
- SAGA側を採用する場合の係数・類の比較：[EquationRealization.lean](../../Formal/AG/SemanticRepair/Saga/EquationRealization.lean)、[KappaComparison.lean](../../Formal/AG/SemanticRepair/Saga/KappaComparison.lean)、[PartIVBridge.lean](../../Formal/AG/SemanticRepair/Saga/PartIVBridge.lean)。
- 第3章の実生成複体と比較：[LawGeneratedComplex.lean](../lean/ResearchLean/AG/ResolutionInvariance/LawGeneratedComplex.lean)、[GeneratedComparisonMap.lean](../lean/ResearchLean/AG/ResolutionInvariance/GeneratedComparisonMap.lean)。
- Atlasの十分条件と全単射：[ResolutionInvarianceConditions.lean](../lean/ResearchLean/AG/ResolutionInvariance/ResolutionInvarianceConditions.lean)、[LawValueBlockComparisonBijectivity.lean](../lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonBijectivity.lean)。

## 完了条件

1. 一つの入力族についてA–CをLeanで証明する。達成として認める結果は
   `target-theorem-proved` とする。論文への対応範囲は、この入力族と各条件で特定する。
2. 一つの小さな有限入力を選び、同じ係数・被覆・Law評価で零障害を生む局所データと
   非零障害を生む局所データを与える。両者について `R_q` と(B1)・(B2)を適用し、
   診断類がそれぞれ零・非零であることを証明する。入力値の選択は構成時に行い、
   reportに固定する。reading変更は既存のAtlasの条件と定理を再利用する。
3. Lean成果を `research/lean/ResearchLean/AG/` に置き、
   `research/reports/G-125-aat-obstruction-diagnostic-bridge.md` にA–Cと宣言、
   前提の出所・使用先、有限例、論文第3章・付録Aとの対応を記録する。
4. [共通基準の参照適用](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)
   に従って完了を判定する。適用版、検証、査読、実行状態はIssue・reportへ置く。
