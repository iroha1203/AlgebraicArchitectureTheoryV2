# PRD: StandardGeometryReference/Geometry.lean の計測駆動分割・高速化(Issue #3872)

- 作成: 2026-08-01
- tracking Issue: #3872
- 一次仕様: Issue #3872(受け入れ要件・失敗ケース)。削減 target は R1 計測後に
  Issue コメントで固定し、人間承認を得る
- 品質基準: `AGENTS.md`、`docs/workflow/guideline.md`、`docs/aat/guideline.md`、
  `docs/aat/lean_quality_standard.md`
- 実行単位: Codex prd-loop、`1 Issue = 1 PR` を基本とし、P2(分割)と P3(削減)の
  2 PR へ分けてよい

## 問い

**標準幾何参照モデル(SD0–SD1)の定理内容を一切弱めずに、その elaboration 費用を
測定可能に分解し、「触った部分だけの支払い」に変えられるか。**

採否の判定規律: 本 PRD の各要求は、この問いを「はい」にするものだけを採る。
内容を弱めて速くする変更(actual Scheme の supplied certificate 化、`HasSheafify`
導出の公理化、fixture の退化)と、計測に基づかない構造変更は採らない。

## 現状診断(2026-08-01 実測、run 30590058108)

- `Formal/AG/Examples/StandardGeometryReference/Geometry.lean`(5,129 行、108 宣言:
  def 26 / noncomputable def 35 / noncomputable instance 2 / theorem 45)の elaboration が
  **38.33 分**。Lean CI フルビルド CPU 時間 82.5 分の 46% を単独で占め、
  1 module 内の逐次処理のため wall clock 40.9 分の臨界路になっている。
  2 位以下は LerayComparison 2.1 分、LargeLerayComparison 1.7 分と一桁小さい。
- 同 file は SD0–SD1 を一手に所有する: context preorder と overlap package、raw sections /
  restriction、principal-open gluing による raw sheaf theorem、localization presentations、
  2 つの `HasSheafify` インスタンス(small cover+有限 multiequalizer+under category の
  極限挙動から導出)、chart-domain isomorphisms、`leftChart` / `rightChart` /
  `referenceAtlas` / `referenceOverlapPresentation` / `referenceScheme` / `actualOverlapIso`。
  重い区間の宣言別内訳は**未計測**。
- 上流は `FiniteModel` / `AffineChart` / `StandardScheme` +重量級 mathlib
  (`AlgebraicGeometry.*`、`Sites.LeftExact`、`EssentiallySmall` 等)。上流のどの編集でも
  全 5,129 行が再 elaborate される(`StandardScheme` 編集が 40 分級になる既知の再現)。
- 下流は `EquationGeometry` と `StandardGeometryReferenceModels`(aggregate)経由で
  `ClosedEquationalGeometry`、`RepresentationAnalysisPart7`、`LegacyConsolidation`、
  `AxiomAudit` まで波及する。
- 本 file は equation 層(`LawEquation` / `ClosedEquationalGeometry`)を意図的に import
  しない安定設計であり、#3736 の legacy 処分と並走できる。
- 先例の教訓: `AxiomAudit.lean` のファイル分割は計測でボトルネックが elaboration では
  ないと判明し不採用だった(#3511)。本件は逐次 elaboration が支配的で条件が異なるが、
  同じ轍を踏まないために計測固定を最初の要求にする。

## 要求

### R1 — before 計測と target の固定

- `set_option trace.profiler true` 等で Geometry.lean の宣言別 elaboration 時間を取得し、
  上位犯人一覧(宣言名、時間、支配項が typeclass 探索 / defeq / kernel いずれか)を
  Issue コメントに固定する。
- CI 実測(38.33 分)を before 基準として記録する。
- 計測に基づき削減 target(最長単一 module の上限時間、および総 CPU 時間の目標)を
  Issue コメントで提案し、**人間承認を得てから** P2 以降へ進む。
- 計測は本体 build 一式を伴うため、実行環境と所要時間の見積りを先に Issue へ書く。

### R2 — module 分割(増分再ビルドの構造改善)

- 計測結果に従い、最長 module を最小化する境界で分割する。候補境界
  (SD0 site / raw sheaf、sheafification インスタンス、localization、SD1 charts /
  scheme / overlap iso)は目安であり、宣言別時間が示す実際の重心を優先する。
- 分割の狙いは次の 3 点を構造として成立させることにある。
  1. 上流(`StandardScheme` 等)の編集で再 elaborate される範囲が、依存する
     module 群だけに縮む。
  2. 相互独立な module が `lake` の並列 build に乗る。
  3. 下流(`EquationGeometry` 等)が必要な部分だけを import できる。
- 全 108 宣言の statement を保存する。namespace / 宣言名の変更は対応表を実装 PR に
  記録する。証明スクリプトの機械的修正(import / open の追随)は statement 保存の
  範囲内とする。
- aggregate(`StandardGeometryReferenceModels`)と `AxiomAudit` の参照を新構成へ同期する。

### R3 — elaboration 削減(profile 駆動)

- R1 の上位犯人に対し、内容を変えない削減手段を適用する: インスタンスの明示供給、
  `local instance` / priority による typeclass 探索の限定、重い defeq を切る
  `def` / `abbrev` 境界の見直し、中間項の型注釈固定、`simp` 集合の限定等。
- 各適用は宣言単位で before / after を計測し、効果のなかった変更は残さない。
- 削減 target(R1 で承認済み)を満たしたら打ち切ってよい。追加削減は別 Issue に送る。

### R4 — 検証と記録

- after 計測(宣言別+CI module 時間)を Issue に記録し、target 達成を確認する。
- 対象 module の focused 検証(`lake env lean`)、hidden / bidi scan、placeholder scan、
  PR CI の full `lake build`、`math-lean-review` 4 本を記録する。
- `AxiomAudit.lean` の標準公理監査が新構成で pass することを確認する。

## Non-goals

- 定理内容・例の実在性の変更(actual Mathlib `Scheme`、`HasSheafify` 導出、
  非自明 fixture の維持は前提)
- CI workflow(`lean.yml`)の変更。検証を CI から外す・週次へ送る等の扱い変更は、
  必要と判明した場合に人間の明示承認を得て別 Issue で扱う
- `EquationGeometry.lean`(5,669 行、0.52 分)等、他 file の性能改善
- #3736(legacy 処分)・#3792(AxiomAudit 分割)のスコープ
- mathlib 本体への変更

## Failure Contract

次のいずれかに該当する場合、本 PRD の完了とは認めない。

1. 定理・インスタンスの statement を弱めた、または actual Scheme を supplied
   certificate へ差し替えて速くした。
2. R1 の計測と target 承認を経ずに分割・削減を実装した。
3. rename だけの水増し分割で、再 elaborate 範囲も計測値も改善していない。
4. 例の検証を CI から外して速く見せた(人間の明示承認なしの検証弱化)。
5. target 未達を計測記録なしに完了扱いにした。
6. 要求の一部を後続 Issue へ送るスコープ縮小をユーザー承認なしに行った
   (R3 の「target 達成後の追加削減」の別 Issue 送りは承認済みの例外)。

## Acceptance Criteria

- [ ] before 計測(宣言別 profile+CI module 時間 38.33 分)が Issue に固定されている。
- [ ] 削減 target が計測に基づき Issue で固定され、人間承認の記録がある。
- [ ] Geometry.lean が複数 module へ分割され、全 108 宣言の statement 保存が
      対応表で確認できる。
- [ ] 最長単一 module の elaboration 時間が target を満たし、after 計測が記録されている。
- [ ] 上流編集時の再 elaborate 範囲が module 単位に縮むことが import graph で示されている。
- [ ] 下流(EquationGeometry / Models / ClosedEquationalGeometry /
      RepresentationAnalysisPart7 / LegacyConsolidation / AxiomAudit)が新構成で green。
- [ ] `math-lean-review` 4 本、focused 検証、hidden / bidi scan、placeholder scan、
      PR CI full `lake build` の記録がある。

## 実装計画

1. **P1 計測**: R1 の profile 取得と犯人一覧・target 提案を Issue に固定し、人間承認を待つ。
2. **P2 分割**: R2 の module 分割と参照同期を 1 PR で実装する。
3. **P3 削減**: R3 の profile 駆動削減を実装する。P2 と別 PR にしてよい。
4. **P4 記録**: R4 の after 計測と検証記録で close する。

## 停止条件

- R1 の計測で、支配項が statement 保存の下では削減できない mathlib 側の構造
  (例: 避けられない instance 探索や sheafification の本質的費用)と判明し、
  現実的な target を提案できない場合は、計測記録を添えて停止しユーザー裁定を仰ぐ
  (選択肢: target の緩和、CI 側の扱い変更の別 Issue 化)。
- 分割によって `maxHeartbeats` 超過や universe 制約の破綻など、statement 保存と
  両立しない技術的障害が出た場合は停止する。
- 保護ファイルの編集が必要と判明した場合は停止する。
