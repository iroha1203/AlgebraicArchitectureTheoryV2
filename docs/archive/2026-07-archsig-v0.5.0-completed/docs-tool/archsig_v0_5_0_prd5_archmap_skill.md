# ArchSig v0.5.0 PRD-5 — ArchMap 抽出 SKILL の再設計(漏れなく・再現性高く)

対象は `tools/archsig/skills/archmap-creater` の再設計(M1: SKILL 本体と references)と、
それを支える ArchSig 側の authoring 支援面(M2: authoring CLI 3 面 + authoring artifact 4 種 +
層1 lint)。ロードマップ P9、v0.5.0 PRD 5 本の最終弾。
**前提: PRD-1(digest 基盤・単一契約版数)の実装が受け入れ済みであること。**
PRD-4 の `aliasWitnesses`(計測側フィードバック)と接続するが、実装依存はない。

関連(設計の正本):

- [ArchSig v0.5.0 再設計ノート](../note/archsig_v0_5_0_redesign_note.md) — §7、§8 裁定9(語彙 manifest /
  ArchMap 鮮度)・裁定10(互換ゼロ)、目標アウトカム O3
- [design_archmap-skill](../note/archsig_v0_5_0/design_archmap-skill.md) — 新 4 schema・CLI 3 面・
  9 段階 Workflow・語彙カタログの全文が正
- [責務憲章](archmap_lawpolicy_archsig_responsibility_charter.md) 原則2(観測の主観は守る)、
  [Archived 観測純化 PRD](../archive/2026-07-07-archsig-v0-legacy-prds/archmap_observation_purity_prd.md)(却下条件の手本)

## 問い

**抽出の再現性と網羅性を、観測の主観を一切機械化せずに得られるか。**

この問いを採否の判定規律として使う。

- **(採用条件 — 機械層)** 機械層に許すのは **列挙・ハッシュ・突合・参照整合の 4 操作のみ**。
  これらを決定的にする作業だけを機械側に採用する: byte 辞書順 + sha256 の決定的 worklist、
  二重抽出の正規化キー突合、自己申告ゲートの機械監査への昇格、判定語 lint の候補段階への前倒し。
- **(採用条件 — bounded claim)** 網羅性の主張は「記録された revision における、選択スコープ内の
  走査記録」まで。extraction completeness(スコープ外を含む完全抽出)はどの artifact・どの文言でも
  主張しない。スコープ判断は承認ゲート(ユーザー + author)に一括し、pass 実行中の sub-agent /
  integrator に分散させない(round-trip 規則)。
- **(却下条件 — 読解層の機械化)** atom の生成・採否・意味付けを機械化する変更は、
  たとえ再現性が上がってもすべて却下する: keyword による semantic 判定、類似度マージ、
  多数決・自動採択、matchRate の閾値 verdict 化、`meaning` 自由記述の正規化・lint。
  突合の unmatched は**誤りの証拠ではなく再読解のキュー**であり、裁定は必ず該当 source の
  再読解で行う。「観測の主観はバグではなく機能」(憲章 原則2)— これを痩せさせたら ArchMap は
  静的解析に堕ち、AAT が上に載せる計算の土台が消える。

## Core Thesis

現状の archmap-creater には再現性を測る計器がなく(golden corpus は手書き fixture → binary の
lock のみ)、品質ゲートは自己申告ブール 4 個、スコープと走査の記録は artifact を持たず、
語彙は自由文字列の字面 dedup である。「検出精度が課題」という認識に対して、改善を測る装置がない。

中核の設計は一行に集約される:

> **機械層(列挙・ハッシュ・突合・参照整合)と読解層(atom の生成・採否・意味付け)を明示的に分離し、
> 機械層を決定的にし、読解層を二重化して突合する。**

ArchMap 本体(schema)は**変更しない**。新設 artifact はすべて authoring workspace の sibling であり、
計測経路(analyze)は一切読まない(観測の質の問題を観測層で解き、ArchSig に観測ヘッジを持ち込まない
— 一括払い)。

## 現状診断(証拠)

design_archmap-skill §2 の W1〜W9 が正。主要 4 点:

1. **W1**: 同一スコープでの再抽出を突合する装置が存在しない。
2. **W4**: 語彙が自由文字列で dedup が字面一致。`sectionValue` の object 字面揺れは cech mismatch
   計算に直接効く(`cech_section_values` は BTreeSet\<String\> の字面比較)。
3. **W7**: alias 保存の規律がない。同一 component に射影される相異なる semantic atom(Λ/K 二層)を
   潰す抽出は、SAGA の faithfulness 判定(十分性方向)の入力を退化させる — PRD-4 の
   `aliasWitnesses` はこの退化の計測側検出器であり、本 PRD の alias 保存規律が観測側の対。
4. **語彙とカタログの乖離リスク**: AG 経路は特定の axis / predicate しか読まない
   (実フィルタは `ag_measurement.rs` に散在)。カタログが実フィルタと乖離すると、
   「AG 経路が読まない atom を量産する ArchMap」を推奨してしまう。

## Design Principles

1. **機械層の許容 4 操作を SKILL に明文列挙**し、それ以外の機械操作を禁止する。
   extraction-diff は候補の内容を解釈しない(キー字面のみ)。
2. **裁定は再読解**: `onlyInPassA/B` の各項目は、integrator が該当 source を再読解して
   `adjudications` に採否(`adopted | merged | not-adopted`)と根拠を書く。CLI は裁定を提案しない
   (決定フィールドを自動生成する機能を持たない)。
3. **数値は記録であって verdict ではない**: matchRate に閾値を置かない。報告文面に
   「記録であり合否ではない」の定型を置く。
4. **統制語彙は手続き理由のみ**: 走査 skip の理由は `private | binary | unreadable | tooling-error`。
   `out-of-scope` はスコープ確定・再承認時(exclusions)の語彙であり、pass 実行中には使えない
   (スコープ判断の一括払い)。
5. **doctrine 固定の維持**: カタログは固定 doctrine 内の recommended token 表(語の使い方の統一装置)で
   あり、closed enum にしない。カタログ外 predicate の使用は「適用判断」として integrator 裁定記録を
   要件とする。**新 axis の導入は authoring run 内で裁定しない** — doctrine / registry 側変更への
   escalation(受け皿は 0.5.x の registry manifest 化と同時判断 — 裁定9)。
6. **鮮度は authoring 側**: git revision / contentHash は scope-manifest が記録する。
   archmap/v2 本体に revision フィールドは足さない(裁定9。計測側の鮮度は PRD-1 の
   `inputDigests.archmap` が既に担う)。

## 改修(本体)

### M1 群 — SKILL 本体と references(binary 変更なし。手書き運用で先行可能)

- **R1(SKILL.md 全面改稿)** Workflow を 9 段階に(preflight / scope manifest 承認 / pass A /
  pass B / consistency / integrate / coverage ledger / validate / deliver)。
  停止条件の明文列挙(binary 無し・スコープ未承認・読めない source・スコープ外判明時の round-trip・
  LawPolicy 無しの analyze 依頼)。運用モード 3 種: `full-dual`(既定)/ `incremental-dual`
  (`--baseline` 増分のみ dual)/ `single-pass`(ユーザーが明示選択した場合のみ。縮退形として正直に記録)。
  **スコープ round-trip 規則**: 読解中に「スコープ外」と判明した source は skip せず、
  exclusions 更新 + ユーザー再承認へ回送する。skill 名は `archmap-creater` を継続(トリガー資産)。
- **R2(references 再編)**
  (a) `extraction-protocol.md` 新設: 決定的走査・固定幅 chunk 分割・二重抽出・integrator 裁定・
  round-trip の手順。`repository-survey.md` は本文書に吸収して削除(survey surface の目安と
  既知 gap 類型 — per-file semantic 走査 / 供給された runtime trace / 供給された permission 証拠 —
  を「Survey surface」節へ移設)。
  (b) `coverage-and-consistency.md` 新設: ledger / consistency の書式・読み方・裁定語彙。
  (c) `vocabulary-catalog.md` 新設: **kind / axis / predicate の 3 層を別表で分離**。
  axis 表は `ag_measurement.rs` の実フィルタから**機械採録**し、AG 経路が読む axis と記述用 axis を
  別列で区別(`support` は axis ではなく生値 predicate — axis 表に載せない)。
  **axis × predicate の AG 消費対応表**(`cech × sectionValue`、`square-free × support|cooccurrence` 等)を
  1 表に収録。semantic kind の **object 必須規約**(意味内容を object に載せ、alias の意味差を
  match key の担持フィールドに載せる)。subject 命名・atom id 規約・atom-match-key の定義と
  `matchRate = matched / (matched + |onlyInPassA| + |onlyInPassB|)` の定義式。
  (d) `mapping-guide.md` 追補: **alias 保存規律**(同一 subject に相異なる use-evidence が観測されたら
  semantic atom を別々に保持。「同じ component を指すから 1 個にまとめる」統合の明示禁止。
  key 完全一致・refs 相違の semantic 対の統合は機械で確定せず integrator が意味の同一性を確認)、
  restrictsTo の操作的手掛かり集(fixture 実測: 包含側 → 共有側)、cover 選択規準
  (cover 1 個 = 測定面 1 個。重なりの無い cover は Čech 系で退化する良悪対例)。
  (e) `examples.md` 追補: alias 潰し / ledger の書き方 / chunk 境界での context 分断の良悪対例。
  (f) `prompt-pack.md` 改稿: candidate packet を schema 付きで指示、self-review gate を 6 項に
  (新規: `worklistChunkFullyRead` / `aliasPreservingSemantics`)。
- **R3(schema-cheatsheet)** v2 schema + 新 4 schema の形状を references に収録。

### M2 群 — authoring CLI 3 面と機械層(atom を生成しない)

- **R4(新 4 schema)** serde 型と validation(いずれも `/v0.5.0`、authoring workspace の sibling。
  schema 全文は design_archmap-skill §3.2 が正):
  `archmap-scope-manifest`(repository revision / dirty、scopeSpec、決定的 worklist、exclusions)、
  `archmap-candidate-packet`(reviewedSources / candidateAtoms / surveyRows(read | partial | skipped +
  手続き理由)/ privateUnavailableNotes / selfReview 6 項)、
  `archmap-extraction-consistency`(atom-match-key 突合、matched / onlyIn、matchRate、contextDiff、
  adjudications)、`archmap-coverage-ledger`(rows は worklist と 1:1、claimBoundary 定数 1 文)。
  **analyze はこれらを読まない**(計測経路の挙動不変)。
- **R5(`archsig scope-manifest`)** ファイル走査 → byte 辞書順ソート → sha256 → worklist 採番。
  git revision / dirty を記録(git 不在なら `revision: null` を記録して続行。補完しない)。
  `--add-evidence <kind>:<name>=<repo相対path>`(author 証拠はファイル供給必須、spec に記録され
  再実行・増分で再現)。`--baseline <old>` で contentHash 差分の増分 manifest(`baselineRef` 付き)。
  exclusions の統制語彙(`user-excluded | private | generated | binary | out-of-scope`)。
- **R6(`archsig extraction-diff`)** atom-match-key
  (`kind | NFC(trim(subject)) | axis | predicate? | object?`。refs / id はキーに含めない —
  pass 間で行参照が揺れても意味的同一を match させ、refs は統合時に和集合)による pass A/B 突合。
  context の match key は member atom keys + restrictsTo 先 keys の sorted 組。
  **判定語 lint の前倒し**(候補 atoms に archmap R3 相当の diagnostic-shortcut 検査。統合前に fail)と
  **semantic object lint**(object を持たない semantic 候補は fail)。
  `--pass-b` 省略時は縮退形を正直に記録(`passBRefs: []`。黙って dual と同形にしない)。
  出力に採否の決定フィールドを自動生成しない(adjudications は integrator が追記する構造)。
- **R7(`archsig archmap` の authoring 監査フラグ)** `--scope-manifest / --candidate-packets /
  --coverage-ledger` は**任意**(従来の単体検証は不変)。与えられた場合の監査 5 check:
  `authoring-sources-resolve`(解決規則 4 項: src: 直接一致 / doc: の path 部解決 / authorAdded 直接一致 /
  **grounding sources の kind ベース免除** — `ctx:*` キーや policy 文書節の現行慣行を壊さない)、
  `authoring-provenance-closure`(採用 atom は surveyRow または adjudications から追跡可能)、
  `authoring-ledger-spans-worklist`(1:1。余剰行も欠落行も fail)、
  `authoring-read-before-cite`、`authoring-revision-recorded`(dirty は報告のみ)。
  結論は肯定形先頭: `AUTHORING_SURVEY_TRACEABLE_WITHIN_SCOPE`。不通過は該当対象のみ列挙
  (non-conclusion の羅列をしない)。これにより自己申告 6 項のうち `worklistChunkFullyRead` /
  `noDiagnosticShortcutAtoms` / provenance 実在が機械検証に昇格する。
  `notScriptGenerated` と semantic の use-evidence 判断は自己申告 + integrator 裁定のまま残す
  (機械化すると読解層を侵す)。
- **R8(依存)** `unicode-normalization`(NFC)と `globset`(include / exclude と
  `--candidate-packets 'authoring/candidates/*.json'` の binary 内 glob 展開。shell 展開に依存しない)を
  追加(いずれも pure Rust。`sha2` は PRD-1 で導入済み)。
- **R9(層1 golden lock)** CI(cargo test)で固定:
  (a) scope-manifest の決定性(fixture ツリー → worklist ビット同一。revision / id は
  テスト用 override フラグまたはマスクで固定)、
  (b) extraction-diff の突合正負系(matchRate は定義式で期待値固定。判定語入り候補 fail、
  object 無し semantic fail の負系)、
  (c) 監査 5 check の正負系(worklist 未張り / 余剰行 ledger、provenance 無し atom、read 前 cite、
  grounding 免除)、
  (d) **vocabulary-catalog 突合 lint**: カタログの機械可読抜粋(fixture)と `ag_measurement.rs` の
  実フィルタ文字列を突合し、乖離を CI で検出する。

## Changed / Removed Fields

- **Added**: authoring artifact 4 種、`scope-manifest` / `extraction-diff` サブコマンド、
  `archsig archmap` の監査フラグ 3 種、references 3 文書新設 + 3 文書改稿、依存 2 crate。
- **Removed**: `references/repository-survey.md`(extraction-protocol へ吸収)。
- **Not changed**: archmap/v2 の schema(フィールド追加なし)、`analyze` の挙動
  (authoring artifact を読まない)、golden corpus の既存 per-evaluator lock、
  doctrine(`doctrine:aat-canonical@1` 固定のまま)。

## Failure Contract

- 監査 check の不通過・判定語入り候補・object 無し semantic 候補・未承認スコープでの続行は fail
  (修理して再実行 — complete-first)。
- 読めない source は fail ではなく手続き理由付きの記録(推測・補完しない)。
  スコープ外判明は round-trip(裁定保留)。

## Implementation Plan

各 PR の完了条件: cargo test(archsig)green、lean.yml green(analyze 挙動不変の確認込み)、
`git diff --check` + hidden Unicode scan、**PR 説明に「機械層 / 読解層のどちら側の規律の実装か」を 1 行**。

| PR | 内容 | 対応 R |
| --- | --- | --- |
| PR-1 | references 再編 + SKILL.md 9 段階 + prompt-pack(手書き運用で成立する形) | R1-R3 |
| PR-2 | 新 4 schema serde + `scope-manifest` コマンド + 決定性 lock + 依存追加 | R4-R5, R8, R9(a) |
| PR-3 | `extraction-diff` + lint 前倒し + 突合正負系 | R6, R9(b) |
| PR-4 | `archsig archmap` 監査 5 check + 正負系 | R7, R9(c) |
| PR-5 | vocabulary-catalog 突合 lint + SKILL.md の CLI 呼び出し最終化 + golden corpus 文書追記 | R9(d) 仕上げ |

順序は PR-1 → PR-2 → PR-3 → PR-4 → PR-5。

## Acceptance Criteria

1. **決定性**: 同一ツリー・同一 spec からの `scope-manifest` 2 回実行がビット同一の worklist を生む。
2. **機械層の限定**: extraction-diff の出力に採否・裁定の自動生成フィールドが存在しない
   (adjudications は空で出力され、integrator が追記する構造であることを fixture で固定)。
   SKILL 本文に機械層の許容 4 操作と、多数決・類似度マージ・自動採択・閾値 verdict の禁止が
   明文列挙されている。
3. **判定語の前倒し遮断**: 判定語 predicate を持つ候補 packet が extraction-diff で fail する負系。
   object の無い semantic 候補が fail する負系。
4. **監査 5 check**: 正負系 fixture が通る(1:1 違反・provenance 欠落・read 前 cite・grounding 免除)。
   全通過時の結論が `AUTHORING_SURVEY_TRACEABLE_WITHIN_SCOPE` 先頭で出る。
5. **bounded claim**: coverage ledger の `claimBoundary` 定数文が fixture lock され、
   `out-of-scope` が surveyRows / ledger の理由語彙として受理されない(統制語彙の負系)。
   extraction completeness を主張する文言がどの artifact / SKILL 文面にも存在しない(rg 検査)。
6. **matchRate の非 verdict 性**: 定義式どおりの期待値 fixture。閾値による分岐がコード上存在しない。
   報告定型「記録であり合否ではない」が SKILL の Output Shape に固定されている。
7. **語彙退化の防止**: vocabulary-catalog 突合 lint が CI green(`support` が axis 表に無い、
   AG 消費 axis の列が実フィルタと一致)。
8. **計測経路の不変**: authoring フラグ無しの `archsig archmap` と `analyze` の挙動・出力が
   本 PRD 前後で byte 同一(既存 e2e / golden が無変更で green)。
9. **alias 接続**: mapping-guide の alias 保存規律に、PRD-4 の `aliasWitnesses` が観測側の対で
   あることが明記され、良悪対例が examples にある。
10. **問いへの遡及**: 各 PR の説明に機械層 / 読解層どちら側の規律の実装かが 1 行で書かれている。

## Non-Goals

- 抽出 golden corpus(教材ミニリポ + expected)の新設と初回実測 — 0.5.x(M3)。
- vocabulary-catalog の registry manifest 化・新 axis escalation の受け皿 — 0.5.x
  (LawPolicy Stage 2 の binding kind registry と同時判断 — 裁定9)。
- archmap/v2 本体への revision / content hash フィールド追加 — 裁定9 により見送り
  (鮮度は scope-manifest と `inputDigests.archmap` が担う)。
- archsig-reader / archsig-pr-reviewer の改稿 — PRD-3 で実施済み。
- skill 名の改名(`creater` → `archmap-author` 等)— 見送り(トリガー資産)。
- 読解層の機械化の一切(semantic keyword lint / 類似度マージ / 自動採択 / matchRate 閾値)—
  本 PRD の問いにより恒久非目標。
- 互換機構の追加 — 裁定10 により恒久非目標。
