# PRD: 旧 Law.holds API の廃止と暗黒コード処分(Issue #3736)

- 作成: 2026-08-01
- tracking Issue: #3736(親 #3716 の Phase 4)。依存 #3733・#3734・#3735 は close 済み
- 一次仕様: Issue #3736(受け入れ要件・失敗ケース)+ #3728 の固定設計 packet。本 PRD は
  2026-08-01 実査で判明した追加事実(暗黒コード)とその処分を要求へ統合する
- 数学的正典: `docs/aat/algebraic_geometric_theory/part_1_atoms_objects_laws.md` 定義 7.1〜7.3
- 品質基準: `AGENTS.md`、`docs/workflow/guideline.md`、`docs/aat/guideline.md`、
  `docs/aat/lean_quality_standard.md`
- 実行単位: Codex prd-loop、`1 Issue = 1 PR`(#3736 一本)

## 問い

**Atom 基礎論ループが結合できる law 語彙は、equation system ただ一つか。**

採否の判定規律: 本 PRD の各要求は、この問いを「はい」にするものだけを採る。
新規 Lean 実装(Atom 基礎論 GOAL ループを含む)が自由述語 law へ結合できる経路
(公開 structure、reverse bridge、CI が見ていない残存コード)を一つでも残す変更、
および経路を消さずに名前だけ変える変更は採らない。

## 現状診断(2026-08-01 実査)

### 移行の到達点

- Phase 1〜3 は完了。`ArchitecturalEquationSystem`(`Formal/AG/Equation/Basic.lean`)が
  violationCoordinate / equationResidual の二族分離で稼働している。
- `holds_defect_mem`・裸の `coverageAssumptions` / `exactnessAssumptions` は全消滅(検索 0 件)。
- bridge は `Formal/AG/Equation/Legacy.lean` の `toLegacyLaw` / `toLegacyLawUniverse` の
  一方向のみで、設計原則に適合している。

### 残債 1: 自由述語がまだ公開 API にいる

`structure Law`(自由な `holds : ArchitectureObject U -> Prop` field)と `LawUniverse` が
`Formal/AG/Atom/Law.lean` に現存し、通常 aggregate(`Formal/AG.lean`)へ配線されている。
改訂済み正典の定義 7.2 は law universe を equation system `E` からの導出表示と規定し、
「追加の truth predicate や別の mathematical field ではない」と明言しているため、
自由述語 structure は現行本文に対して過剰な API である。import 元は aggregate と
`Equation/Legacy.lean` の 2 箇所に縮退済みで、削除の構造的影響は限定的である。

### 残債 2: 暗黒コード(CI が見ていない残存 legacy)

次の orphan 連鎖はどのファイルからも import されず、CI(`lake build +Formal.AG` と
`AxiomAudit.lean` 直接実行のみ)でビルドも公理監査もされていない。

```text
Atom/ObstructionLegacy.lean
  -> Atom/LawfulnessZeroLegacy.lean
  -> Examples/FiniteModelLegacy.lean / LawAlgebra/ClosedEquationalGeometryLegacy.lean
  -> LawAlgebra/RingedSiteFiniteExampleLegacy.lean
  -> LawAlgebra/ClosedEquationalGeometryFiniteExample.lean(4,032 行、最上位 orphan)
```

各 leaf 内の `#assert_standard_axioms_only` は一度も実行されていない。#3735 の
「compatibility 監査を leaf へ移す」(commit 29f04459)以降、leaf が全ビルド経路から外れた。
放置すれば toolchain / mathlib 更新で静かに壊れ、#3736 の最終監査の前提が崩れる。

### 残債 3: research 側の bridge 依存 → G-06 成果物の退役で解消(2026-08-01 裁定)

`research/lean/ResearchLean/AG/QualitySurface/SemanticRepairLawEquationRealization.lean`(6 箇所)と
同 `SemanticRepairCechGrounding.lean`(246 箇所)が、導出 bridge `toLegacyLawUniverse` の
`Index` / `Required` 表示を参照している。両 file は GOAL `G-aat-quality-surface-06`
(status: completed)の主要成果物であり、`docs/note/aat_saga_theorem_proof_record.md` §6 に
研究価値が記録済みである。

ユーザー裁定(2026-08-01): G-06 は SAGA 系であり、蒸留完了として退役させる。
一部 conjunct が AG 本体に存在しない場合も、AG 本体が必要とする内容ではないため、
unported 起票なしで退役してよい。処置は `research/README.md`「Lean 成果物の退役」の
規律(#3870)に従い、R3 で実行する。これにより 252 箇所の同時移行は不要になり、
`LawUniverse` 型は完全削除できる。

### 対象外と分類する語彙 residue(構造非依存)

- `Formal/AG/Derived/LawfulLoci.lean` の `abbrev LawUniverseReading`(実体は
  `SelectedLawWitnessIdealFamily`、ideal ベース)
- `Formal/AG/SingularityMonodromyStack/OperationCategory.lean` の
  `operationRespectsLawUniverse` field 名

いずれも自由述語への構造的依存ではない。#3736 備考の「同名 identifier として分類済みの
N 群は対象外」に従い、rename は本 PRD の対象外とする(最終検索の除外一覧に明記する)。

## 要求

### R1 — 自由述語 primary API の廃止

- `structure Law`(自由 `holds` field)と `LawUniverse` を、bridge
  (`Equation/Legacy.lean` の `toLegacyLaw` / `toLegacyLawUniverse`)ごと完全削除する。
  R3 の退役完了後は bridge の生きた消費者が存在しないため、表示型の残置は不要である。
  任意の `ArchitectureObject -> Prop` を AAT の primary law として構成できる公開 structure を残さない。
- 一般の旧 `Law` から equation system を復元する API を追加しない(G-06 no-go)。
- `LawRole` / `LawWitnessFamily` / `Lawfulness` / `SemanticLawful` 等の随伴宣言は、
  equation 側で役割が引き継がれているかを実読で確認し、残存必要性のないものを削除する。
- 正典定義 7.2 の law universe 表示は本文の記法であり、Lean 側に表示型を要求しない。

### R2 — 暗黒コード処分(既定 = 削除)

- orphan 連鎖 6 file の削除を既定処置とする。
- 削除前に各 file の検証内容を実読し、equation 側に等価 fixture が存在しない検証だけを
  非 legacy 語彙で equation 側 fixture へ移設する。移設対象と equation 側対応の一覧を
  実装 PR に記録する(等価物が既にあるものは削除のみでよい)。
- 削除ではなく保持を選ぶ file は、CI が実際にビルドする公式 target への配線と公理監査到達を
  同時に満たす場合に限る。compatibility leaf を通常 `Formal.AG` aggregate へ戻す処置は
  #3792 の監査構造設計と衝突するため認めない。
- 完了時、`Formal/` 配下に CI がビルドしない `.lean` file が存在しないことを import 走査で示す
  (`AxiomAudit.lean` は CI 直接実行のため例外)。走査手順を PR に記録する。

### R3 — G-06 research 成果物の退役(退役規律の適用第 1 号)

`research/README.md`「Lean 成果物の退役」の 3 手順に従い、G-06 の成果物 6 file を退役する。

```text
ResearchLean/AG/QualitySurface/SemanticRepairCechGrounding.lean
ResearchLean/AG/QualitySurface/SemanticRepairLawEquationRealization.lean
ResearchLean/AG/QualitySurface/SemanticRepairLawEquationWitnessInstance.lean
ResearchLean/AG/QualitySurface/SemanticRepairLawEquationGroundedPacket.lean
ResearchLean/AG/QualitySurface/SemanticRepairLawEquationEndToEndInstance.lean
ResearchLean/AG/QualitySurface/SemanticRepairLawEquationNonzeroClassInstance.lean
```

- 6 file は閉クラスタである(importer は相互と `ResearchLean/AG.lean` aggregate のみ、
  他 GOAL の file からの依存なし。2026-08-01 実査)。想定外の依存が見つかった場合は停止する。
- 手順 1 の証拠固定は `research/reports/G-aat-quality-surface-06.md` へ、最終検証 head の
  commit hash と退役 file 一覧を追記して行う。
- `docs/note/aat_saga_theorem_proof_record.md` §6 の置き場所記載へ、退役済みであることと
  参照用 commit hash を追記する(path 参照の hash 付き置換)。
  `docs/note/aat_saga_part10_lean_r0_input_structure_design.md` の path 参照も同様に扱う。
- `research/lean/research-modules.txt` と `ResearchLean/AG.lean` から 6 module を除去し、
  file を削除する。
- ビルド対象から外すだけで file を tree に残す凍結は退役として認めない。

### R4 — AxiomAudit・台帳同期

- 削除宣言の監査 alias(`AxiomAudit.lean` 内の legacy 系 alias を含む)を除去し、
  監査対象を最終宣言集合と一致させる。
- standard axioms のみ、`sorry` / `admit` / custom `axiom` / `unsafe` 追加なしを維持する。

### R5 — 最終監査と close

- #3728 packet の 7 symbol search を固定 head で再実行し、旧 semantic / equational seam が
  0 件であることを記録する(同名 identifier N 群は除外一覧として明記)。
- 親 Issue #3716 の各受け入れ要件を宣言名・fixture・CI・review URL で確認し、
  #3736 と #3716 を close する。

## Non-goals

- 語彙 residue の rename(上記 N 群)
- `Evolution/TemporalLaw` の自由述語 field(正典第 IX 部の語彙。equation system 化の要否は
  Atom 基礎論 GOAL の理論論点として扱う)
- `AxiomAudit.lean` の責務分割と cold build 再現性(#3792)
- `StandardGeometryReference/Geometry.lean` のビルド時間対策(別 Issue)
- G-06 以外の completed GOAL 成果物の退役 sweep(別作業として起票する)
- `docs/aat/algebraic_geometric_theory/**` の編集(保護ファイル)

## Failure Contract

次のいずれかに該当する場合、本 PRD の完了とは認めない。

1. `Law` を残したまま別名の wrapper を追加しただけ。
2. 自由述語 structure を private 化や rename で温存しただけ。
3. 旧 `Law` から equation data を復元する経路を新設した。
4. orphan file を通常 aggregate へ再導入して「ビルドされている」ことにした。
5. 移設判断なしの一括削除で、equation 側に等価物のない検証を黙って失った。
6. 検索証拠が固定 head に紐付かない、または statement 実読を省略した。
7. 要求の一部を後続 Issue へ送るスコープ縮小をユーザー承認なしに行った。
8. 退役をビルド対象からの除外だけで済ませ、file を tree に残した(凍結の禁止)。
9. 退役の証拠固定(report への最終 head 追記・proof record の hash 付き注記)を省略した。

## Acceptance Criteria

- [ ] 任意の `ArchitectureObject -> Prop` を primary law として構成できる公開 structure が
      `Formal/` に存在しない。
- [ ] 旧 `Law` から equation system を復元する API が存在しない(逆向き構成の禁止)。
- [ ] `holds_defect_mem` 同値の membership certificate input が標準 route に存在しない
      (現状 0 件を最終 head で再確認)。
- [ ] orphan 連鎖 6 file が削除済み(例外裁定時は公式 build target へ配線済み)で、
      `Formal/` に CI 未ビルド `.lean` が存在しないことの走査記録がある。
- [ ] equation 側に等価物のない検証の移設対応表が実装 PR に記録されている。
- [ ] G-06 成果物 6 file が退役済みである: report への最終検証 head と file 一覧の追記、
      proof record・r0 設計 note の hash 付き注記、`research-modules.txt` と
      `ResearchLean/AG.lean` からの除去、file 削除がすべて確認できる。
- [ ] `toLegacyLaw` / `toLegacyLawUniverse` を含む `Law` / `LawUniverse` 系 API の残存が
      0 件である(bridge 完全削除の確認。N 群の同名 identifier は除外一覧に従い対象外)。
- [ ] `AxiomAudit.lean` が最終宣言集合と一致し、standard axioms のみ、
      `sorry` / `admit` / custom `axiom` / `unsafe` 追加がない。
- [ ] 7 symbol search の固定 head での再実行結果 0 件と除外一覧(N 群)の記録がある。
- [ ] 対象非 aggregate file の focused 検証(`lake env lean`)、hidden / bidi scan、
      placeholder scan、PR CI の full `lake build`、`math-lean-review` 4 本の記録がある。
- [ ] #3716 の各受け入れ要件が宣言名・fixture・CI・review URL で確認され、
      #3736・#3716 が close されている。

## 実装計画

1. **P1 実読分類**: orphan 連鎖 6 file の検証内容を実読し、equation 側対応表
   (等価あり = 削除のみ / 等価なし = 移設先)を Issue コメントに固定する。
2. **P2 廃止と処分**: R1 の API 廃止(bridge 含む完全削除)、R2 の移設と削除、
   R3 の G-06 成果物退役を単一 PR で実装する。
3. **P3 監査同期と close**: R4 の alias 同期、R5 の最終検索・acceptance audit、
   両 Issue の close。P2 と同一 PR に同梱してよい。

## 停止条件

- equation 側で等価に立て直せない検証があり、かつ legacy 語彙なしで表現できない場合は
  停止してユーザー裁定を仰ぐ(Formal 側 orphan 連鎖の移設判断に限る。G-06 成果物は
  裁定済みのため該当しない)。
- 処分の過程で正典本文の編集が必要と判明した場合は停止する(保護ファイル 3 条件)。
- 削除・退役対象に、R2 の orphan 連鎖と R3 の閉クラスタ以外からの外部依存
  (research/lean の他 GOAL file・tools からの参照)が見つかった場合は停止する。
