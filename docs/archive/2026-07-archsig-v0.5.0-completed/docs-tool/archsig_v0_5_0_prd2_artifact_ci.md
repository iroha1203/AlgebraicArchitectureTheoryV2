# ArchSig v0.5.0 PRD-2 — measurement packet 新形と CI 面(gate / compare)

対象は ArchSig の出力 artifact 体系の v0.5.0 新形(ロードマップ P3〜P4):
measurement packet の拡張、FieldSig handoff の行レベル化、そして CI 合否面
`archsig gate` と計測間比較 `archsig compare` の新設。
v0.5.0 PRD 5 本の第 2 弾(前提: PRD-1 の契約基盤 — 単一契約版数・`inputDigests` /
`siteCoverDigest` / 決定的 runId — が受け入れ済みであること)。

関連(設計の正本):

- [ArchSig v0.5.0 再設計ノート](../note/archsig_v0_5_0_redesign_note.md) — §5(artifact / CI)、
  §8 裁定1(compare / gate 一本化)・裁定2(gate、boundaryKindOverrides)・裁定5(比較系 artifact)・
  裁定6(verdict ref / conclusionCode registry)・裁定7(単一契約版数)・裁定10(互換ゼロ)
- [design_artifacts](../note/archsig_v0_5_0/design_artifacts.md) — schema 全文と validation 規則
- [design_legacy-triage](../note/archsig_v0_5_0/design_legacy-triage.md) — §3.4(verdict 遷移と
  cover 変更行の扱い。本 PRD の compare に吸収)
- [責務憲章](archmap_lawpolicy_archsig_responsibility_charter.md)、第VIII部(verdict discipline)、
  第X部 §8(境界定理)

## 問い

**計測の結論は、packet から CI exit code まで「丸められず」、かつ「記録を超えて主張されない」か。**

この複合の問いを採否の判定規律として使う。

- **(丸め禁止)** verdict 5 値(`measured_zero / measured_nonzero / unmeasured / unknown / not_computed`)の
  **非可逆な縮約点をどの層にも作らない**。gate の 3 値写像は appliedMapping の全行記録で可逆に保ち、
  非終端 verdict の写像先は `pass_with_boundary` / `block` の 2 値に schema 水準で制限する
  (「unmeasured を黙って pass に丸める」は制度選択としても選べない)。FieldSig は violated assumption を
  依存行だけに波及させ、packet 全体を丸めて捨てない。candidate reading は headline に昇格しない。
  vacuous な measured_zero は packet validation が機械的に拒否する。
- **(過剰主張禁止)** 二つの計測の差分は **record であって transport ではない**。conclusionCode は
  record 水準名(`…_RECORDED_AFTER_CHANGE` 系)に固定し、class の同一視・「同じ障害が直った/残った」は
  comparison data が供給・検査されるまで語らない(第X部 定理8.4 / 8.5「比較可能性はデータ」)。
  **v0.5.0 の compare は identical / verdict-row 水準のみを実装するため、
  transport を語る経路がコード上存在しないこと自体が受け入れ条件になる。**
- **(却下条件)** verdict を exit code に直接埋める変更、analytic 値の閾値 gate、
  comparison data なしの cross-run 主張を生む一切の便利機能、および互換機構の追加(裁定10)は、
  たとえ有益でも本 PRD では却下する。

## Core Thesis

v0.4.0 の CI 面は「計測」と「制度的合否」が `--strict-distance` フラグ 1 本に畳み込まれ、
packet の 5 値 verdict は exit code の 2 値に非可逆に落ちている。また比較面(pr-review)は v1 専用で、
理論的裏付け(定理8.4 / 8.5)を持つ比較 artifact が存在しない。

本 PRD は次の分離で両方を解く。

```text
analyze  = 計測。計測が走った以上、成功(verdict の内容は exit code に現れない)
gate     = 制度的判断。verdict → 合否の写像は組織の選択なので gate-policy として author される
compare  = 二計測の記録差分。comparability は digest で機械判定し、record 水準までしか語らない
```

## 現状診断(証拠)

1. `--strict-distance` は v2 経路で「非終端 verdict が 1 行でもあれば exit 1」(main.rs:905-1036 実測)。
   5 値 → 2 値の非可逆な縮約点であり、丸めの痕跡も残らない。
2. FieldSig は `dependsOnAssumptions`(行レベル assumption 依存、実装済み)を読まず、
   violated assumption と measured 行の併存を packet 全体の contradiction として fail-fast する
   (fieldsig/src/archmap.rs:1046- 実測)。行が丸めて捨てられている。
3. `computed_invariants: Vec<Value>` が untyped(schema/measurement.rs:13)。CI・FieldSig・viewer が
   invariant を機械参照できず、verdict と計算の双方向参照がない。
4. analytic reading に certified / candidate の型区別がなく、measured_zero の非 vacuous 性
   (選択 scope 非空 + 支える計算への参照)が packet 上で機械検証できない。
5. 比較面: `pr-review` は v1 専用(削除は PRD-3)。v2 の二計測を比較する surface が存在せず、
   将来「前回より改善/悪化」を安易に語る設計事故が起きやすい。

## Design Principles

1. **5 値・6 区画の保存**(第VIII部 定義11.1 / 原則3.1-3.2): packet は 6 区画を保持したまま拡張する。
   どの下流 artifact も 5 値語彙のまま運ぶ。
2. **concrete class 規律**(第IV部 原則4.4): verdict 行は「どの cover のどの class を測ったか」を
   構造化して指す。measured_nonzero は代表 cocycle への参照を必須とする。
3. **supplied / generated 規律**(第X部): 供給されたデータは suppliedData 台帳に適合検査結果と共に記録し、
   結論は入力に格納させない(anti-weakening hard error)。
4. **比較可能性はデータ**(定理8.4 / 8.5): comparability は宣言や名前でなく digest
   (profileFingerprint + siteCoverDigest)で機械判定する。v0.5.0 は transport 水準を実装しない。
5. **verdict ref は既存安定形式**(裁定6): `structuralVerdict/{evaluator}/{law}/{method_status}`。
   行 index 形式・新 verdictId 形式は導入しない。compare / gate の行対応は
   (evaluator, law, target) の組で取る。
6. **互換ゼロ**(裁定10): FieldSig は atomic 切替(両受理窓・dual-emit なし)。
7. **profile 凍結**: packet の `profile` 区画は解決済み MeasurementProfileV1 の埋め込みコピー +
   `profileFingerprint`。PRD-4 の LawPolicy 形状変更は fingerprint の算出元が変わるだけで
   packet schema に波及しない。

## 改修(本体)

### P3 群 — packet 新形と handoff

- **R1(packet 新形)** `archsig-measurement-packet/v0.5.0`: 6 区画を保持したまま次を追加する
  (schema 全文は design_artifacts §3.1 が正)。
  (a) 行の `target` ブロック(kind / coverRef / coefficient / classRef / scopeSize)、
  (b) `evidence.computedInvariantRefs`(verdict とそれを確立した計算の双方向参照)、
  (c) `computedInvariants` の typed 化(invariantId + 閉語彙 kind + value + representation。
  SAGA 系 3 kind は予約のみ)、
  (d) `assumptions[].assumptionId` の安定 id 化と `dependsOnAssumptions` の id 解決、
  (e) `analyticReadings[].claimStatus`(certified / candidate)と `fidelity`(faithful / proxy)、
  (f) `suppliedData[]` 台帳(kind / sourceArtifactRef / conformance)。
- **R2(packet validation 新形)** 次の 5 検査を必須化する:
  (1) measured_zero 純度 invariant(`verdict == measured_zero` ⇒ scopeSize 該当成分 > 0 かつ
  computedInvariantRefs 非空。vacuous zero を schema 水準で排除)、
  (2) dependsOnAssumptions の全 id 解決 + violated 依存行の not_computed 正規化、
  (3) candidate reading が structuralVerdictRef を持たない(candidate を verdict の根拠にしない)、
  (4) measured_nonzero 行の target.classRef 解決必須(concrete class)、
  (5) boundaryStatements kind の 6 値語彙検査。
- **R3(summary / insight 新形)** conclusion-first を維持し、`conclusionCode` を
  **単一 Rust const registry + schema catalog 掲載 + fixture lock** の三点で固定する(裁定6)。
  初期収載は現行 v2 語彙 + 本 PRD の gate / compare 語彙(SAGA 系は PRD-4 で追加)。
  candidate reading・非終端行を headline に昇格しない検査を summary 生成テストで固定する。
- **R4(FieldSig handoff)** 新 packet の受理(atomic 切替、旧受理は同一 PR で削除 — ただし
  v1 `--analysis-packet` 受理は PRD-3 の管轄で本 PRD では触らない)。
  **行レベル propagation**: violated assumption は `dependsOnAssumptions` でそれに依存する行だけを
  影響範囲とし、無関係な measured 行は取り込む。packet-level fail-fast は
  「violated 依存行が measured のまま残っている packet」(= R2-(2) 違反)のみに縮小する。
  boundaryStatements を typed のまま SFT input へ写す。lean.yml の v2 handoff 断言を同期する。

### P4 群 — CI 面

- **R5(gate-policy)** `archsig-gate-policy/v0.5.0`(CI 管理者が author): rule ごとに
  `scope: "absolute" | "introduced-by-change"`。
  absolute は verdict 5 値 + violated-assumption 依存の **6 写像すべて明示必須**(省略は validation fail)。
  introduced-by-change は閉じた 5 カテゴリ(new / cleared / preexisting / removed / other)への
  写像すべて明示必須。写像語彙は `pass / pass_with_boundary / block` の 3 値のみ(`fail` という語を使わない)。
  **非終端 verdict(unmeasured / unknown / not_computed / violated 依存)と removed / other の写像先は
  `pass_with_boundary` / `block` の 2 値に schema 制限**(plain pass は validation fail)。
  rule に任意の `boundaryKindOverrides`(例: `{ "silence_by_design": "pass_with_boundary" }`)を許す —
  裁定2 の carve-out 表現。override の写像先も同じ 2 値制限に従う。
  保守的既定の starter テンプレート + docs/tool の authoring ガイドを同梱する(専用 SKILL は作らない)。
- **R6(gate-report と exit code)** `archsig-gate-report/v0.5.0`: decision は
  `PASS_WITHIN_GATE_POLICY / BLOCKED_BY_GATE_POLICY / NOT_EVALUABLE` の 3 値。
  `ruleOutcomes[].appliedMapping` に全行の(verdict → action)を記録する(丸めの痕跡が常に残る)。
  exit code 体系: analyze = 0(計測完了。verdict 内容に依らず)/ 2(入力 contract 違反)/ 3(内部エラー)、
  gate = 0(PASS)/ 1(BLOCKED)/ 2(入力不正・digest 不一致)/ 3(内部エラー)。
  analyze の validation 失敗を exit 1 → 2 に変更するのは breaking change であり、
  lean.yml を同一 PR で更新する。
- **R7(compare)** `archsig compare --base-run <dir> --head-run <dir>`:
  比較可能性は 2 段階のみ実装する。
  `identical` = archmapDigest + profileFingerprint + toolVersion 一致。
  `verdict-row` = profileFingerprint + siteCoverDigest + toolVersion 一致(同名 target の verdict 行を
  記録として並置し transition をラベルする。class の同一性・transport は主張しない)。
  toolVersion 不一致は boundary statement を付して verdict-row 水準に落とさない(裁定7)。
  不成立時は両 run の独立な結論を並記し `RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA` +
  typed boundary 1 行で沈黙する。**class-transport 水準(measurement-comparison 供給)は実装しない**
  (0.5.x。schema 予約もしない — 実装時に catalog へ登録する)。
- **R8(archmap-diff)** compare は両 run の normalized archmap から `archmap-diff/v0.5.0`
  (sources / atoms / contexts / covers の added / removed / modified、決定的 JSON 比較)を**計算して**出力する
  (二つの supplied artifact の差分計算は観測ではなく計算 — 裁定1)。
  covers / contexts に差分がある profile 行の transition には boundary
  `cover_changed_between_runs` を付し、gate の introduced-by-change 分類では `other_transition` に落とす
  (測定面の変更を architecture 劣化に丸めない)。
- **R9(comparison-report)** `archsig-comparison-report/v0.5.0`: conclusionCode は record 水準名のみ
  (`NO_NEW_MEASURED_OBSTRUCTION_RECORDED` / `MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE` /
  `MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE` / `RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA`)。
  `verdictTransitions[].deltaRefs` は archmap-diff の op 対象 id と verdict 行の参照 id の
  **機械的交差**(空なら `[]`。因果帰属ではない)。claim 形と非因果性は `discipline` 文字列として
  artifact に焼き込み、fixture で lock する。
- **R10(gate × compare 接続)** `archsig gate --comparison <report>` で introduced-by-change rule が
  有効になる。comparison 不在時の introduced-by-change rule は `not_applicable` として skip
  (黙って pass にしない)。lean.yml の push 側 e2e を「analyze → gate → fieldsig handoff → catalog diff」の
  形に置換する(v1 e2e 区間 :49-201 は本 PRD では不変。削除は PRD-3)。

## Changed / Removed Fields

- **Changed**: measurement packet(6 区画保持 + R1 の追加)、summary / insight(conclusionCode registry 化)、
  FieldSig の assumptions 検証(packet-level fail-fast → 行レベル propagation)。
- **Added**: gate-policy / gate-report / comparison-report / archmap-diff(いずれも `/v0.5.0`)。
- **Not changed**: archmap / law-policy / measurement-profile の形状(PRD-4)、`pr-review` コマンドと
  `--strict-distance`(削除は PRD-3。gate 導入後も v1 経路が残る間は共存させ、意味変更しない)、
  viewer data(投影追加は 0.5.x ArchView マイルストーン)。

## Failure Contract

- gate: gate-policy の写像省略・非終端への plain pass・未知 verdict 語彙は validation fail。
  packet 不在・digest 不一致は `NOT_EVALUABLE`(exit 2)であり、pass にも block にも丸めない。
- compare: comparability 不成立は fail ではなく「並記 + typed boundary + record 水準 conclusionCode」。
  transport を求める入力(存在しないフラグ・schema)は受け取らない(経路が存在しない)。

## Implementation Plan

各 PR の完了条件: archsig / fieldsig の cargo test green、lean.yml green、`git diff --check` +
hidden Unicode scan、および **PR 説明に「丸め禁止 / 過剰主張禁止のどちらの規律の実装か」を 1 行**。

| PR | 内容 | 対応 R |
| --- | --- | --- |
| PR-1 | packet 新形 + packet validation + summary / insight 新形 + conclusionCode registry | R1-R3 |
| PR-2 | FieldSig 行レベル propagation + 新 packet 受理(atomic)+ lean.yml handoff 同期 | R4 |
| PR-3 | gate(policy / report / exit code 体系)+ starter テンプレート + authoring ガイド + lean.yml push e2e 置換 | R5-R6, R10 前半 |
| PR-4 | compare + archmap-diff + comparison-report + gate 接続 + e2e fixture | R7-R9, R10 後半 |

順序は PR-1 → PR-2 → PR-3 → PR-4(PR-3 と PR-4 は入れ替え可)。

## Acceptance Criteria

1. **丸め経路の不在(機構)**: 非終端 verdict へ plain pass を割り当てた gate-policy が
   validation fail する負系 fixture。写像を 1 つでも省略した gate-policy が fail する負系 fixture。
2. **丸めの痕跡(記録)**: 全 gate 判定が appliedMapping に verdict 語彙のまま残る(fixture lock)。
   `fail` という語が gate の写像語彙・出力に存在しない(rg 検査)。
3. **measured_zero 純度**: 選択 scope 空で measured_zero を主張する packet が validation fail する負系 fixture。
4. **candidate 非昇格**: candidate reading が structuralVerdictRef を持つ packet、および candidate が
   summary headline に現れる生成が、それぞれ検査で fail する。
5. **行レベル propagation**: violated assumption を含む fixture で、依存行のみが影響を受け、
   無関係な measured 行が FieldSig の SFT input に取り込まれることをテストで固定。
6. **transport 経路の不在**: comparison-report の conclusionCode enum に transport 系
   (`ZERO_PRESERVED…` 等)が存在しない(rg + registry 検査)。cover を変更した fixture 対で
   `RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA` + 並記 + boundary 1 行になることを e2e で固定。
   cover 変更行の transition が gate で `other_transition` に落ちることを固定。
7. **record 名称の固定**: conclusionCode / discipline 文字列が fixture lock され、
   `…_INTRODUCED_BY_CHANGE` / `…_CLEARED_BY_CHANGE` 型の因果・transport 読みを誘発する名称が存在しない。
8. **exit code**: analyze が measured_nonzero を含む run でも exit 0。gate の 0/1/2 が
   gate-report の decision と一致。lean.yml が新 exit code 体系で green。
9. **決定論**: 同一入力での gate / compare の再実行が byte 同一の report を生む。
10. **registry 三点固定**: conclusionCode の const / catalog / fixture が一致する drift 検査。

## Non-Goals

- class-transport 水準の compare(measurement-comparison、kind 別 license)— 0.5.x。
- `pr-review` と `--strict-distance` の削除 — PRD-3(v1 path と同時)。
- SAGA 系 verdict / conclusionCode / suppliedData kind の実装 — PRD-4(packet 側は予約のみ)。
- observation-frontier — 0.5.x 任意(次元6 支援)。
- viewer data への投影追加 — 0.5.x ArchView マイルストーン。
- analytic 値の閾値 gate、SARIF 等の外部 CI フォーマット変換 — 見送り(丸めの温床)。
- 互換機構の追加(両受理窓・dual-emit)— 裁定10 により恒久非目標。
