---
name: math-lean-review
description: 数学本文、research/GOALS.md、docs/note、PRD、Lean theorem/lemma/definition、または定理・命題テキストを入力に、その数学的主張と Lean 実装を、仮定放電・certificate provenance・anti-weakening まで含めて論文査読する数学者レベルで厳格レビューする。Use when the user says "$math-lean-review", "数学とLEANのレビュー", "この定理をLean実装込みで査読して", "GOALS.mdの命題をLean上で厳しく見て", "大定理モードの証明完了を査読して", or asks for parallel subagent review of theorem/proposition claims against Lean proofs.
---

# Math Lean Review

数学本文・GOAL・命題テキストと Lean 実装の対応を、研究論文の査読として扱う。目的は実装や修正ではなく、主張、仮定、証明依存、形式化境界、台帳状態が本当に一致しているかを厳しく判定することである。

特に `research/GOALS.md` の大定理モードでは、この skill は「大定理が証明されたこと」を完了条件にするループの査読 gate である。過去に、仮定が放電されていないまま大定理が弱い形で Lean 上は通ってしまう事例があったため、証明完了判定は fail-closed に行う。

## 基本方針

- ユーザーへの報告は日本語で行う。
- 判定は可能な限り厳しくする。数学者の論文査読レベルを基準にし、合格判定は例外的にしか出さない。迷う場合は `No major findings` ではなく、証拠不足・仮定不足・弱化可能性として `Major revisions`、`Reject / 証明として不十分`、または `Blocked / cannot determine` に倒す。
- Findings first で書く。証明として不完全、主張過大、仮定依存、未放電、`axiom` / `sorry` / `admit` / `unsafe` / `by trivial` 風の薄い証明、台帳 drift を優先して出す。
- 対象 theorem だけを眺めて完了扱いにしない。定義、補題、instance、import 元、依存 theorem、example、index / proof obligation / GOAL claim まで、主張の成立に必要な境界を読む。
- Lean が通ることは十分条件ではない。仮定が主張を丸ごと含んでいる、`Prop` が弱すぎる、 witness が選択済みすぎる、非空性や decidability や finite universe を hidden assumption にしている、`True` wrapper / marker theorem になっている場合は finding とする。
- explicit certificate はそれだけでは放電ではない。certificate / class membership / structure field / theorem argument が material premise を透明に保持しているだけなら、未放電 premise として扱う。必ずその certificate 自体を生成する theorem / construction / finite witness / instance chain を追う。
- theorem statement に現れる premise が proof term で実質的に使われているかを確認する。未使用の `sheafCondition`、`faithfulness`、`exactness`、`descent` などは、主張補強ではなく ledger/package への添付にすぎない可能性が高い。
- 大定理モードでは、「大定理名の theorem が存在する」「main theorem が build する」「候補カードが proved と言っている」だけでは完了にしない。本文 / GOAL が要求する強さ、主要仮定の放電、依存補題の健全性、台帳の rigor label が揃って初めて証明完了候補とする。
- 数学本文と Lean のどちらも勝手に編集しない。ユーザーが明示的に修正を依頼した場合だけ実装作業へ移る。
- `docs/aat/algebraic_geometric_theory/`、`docs/sft/software_field_theory.md`、`docs/sft/aat_interface.md` は保護対象。レビュー目的で読んでよいが、明示的な本文編集依頼なしに変更しない。
- AAT / GOAL / Lean theorem の claim boundary 外にある事項を未達 finding にしない。たとえば ArchMap の抽出完全性、実プロジェクトからの evidence completeness、tooling の observation completeness、runtime measurement exhaustiveness は、対象 claim が明示的に要求していない限りレビュー対象外とする。
- coverage を明示する。読んだ本文、読んだ Lean 宣言、依存として追った範囲、未確認範囲、実行した検証を分ける。

## 入力解釈

1. ユーザー指定を対象にする。
   - 数学本文: `docs/aat/algebraic_geometric_theory/...`、`docs/note/...`、Markdown 節、命題文。
   - 研究 GOAL: `research/GOALS.md` の GOAL card、frontier、spine、target theorem、大定理モードの完了条件。
   - Lean: `Formal/.../*.lean` の theorem / lemma / def / example 名、またはファイル範囲。
   - PR / diff: 指定 PR、branch、commit range、local diff に含まれる theorem claim。
2. 指定が曖昧なら、対象ファイルと命題名を `rg` で探す。合理的に一意でなければ短く確認する。
3. 入力が本文だけの場合は、対応する Lean 候補を探索する。見つからない場合は「Lean 実装なし / 未確認」ではなく「該当実装未発見」として報告し、判定は原則 `Reject / Lean implementation not found for claim` に寄せる。
4. 入力が Lean だけの場合は、docs / GOAL / theorem index / proof obligations に対応 claim があるかを探索する。

## 初期調査

必ず先にローカル状態と対象範囲を把握する。

```bash
git status --short --branch
rg -n "<命題名|定理名|主要語>" docs research Formal
```

必要に応じて読む。

- `docs/aat/lean_theorem_index.md`
- `docs/aat/proof_obligations.md`
- `research/GOALS.md`
- 対象 Lean ファイルと、その import 先 / 依存補題
- 対象数学本文。ただし保護対象の本文はレビューのみで編集しない

## GOALS.md 大定理モード

`research/GOALS.md` の大定理モード、target theorem、spine theorem、または「この大定理が証明されたら完了」というループをレビューするときは、次を完了 gate にする。

1. GOAL claim を正確に抽出する。
   - 大定理名、本文の自然言語 claim、必要な仮定、対象 universe、係数、site / topology、量化範囲、結論の強さを分ける。
   - GOAL card と supporting note / candidate card / report がある場合は、どれが完了条件で、どれが背景説明かを区別する。

2. Lean statement が GOAL claim を弱めていないか確認する。
   - 一方向だけ、有限例だけ、選択済み witness だけ、特殊 universe だけ、追加 compatibility 仮定つき、構成ではなく存在だけ、存在ではなく marker だけ、という弱化を finding にする。
   - 弱化がある場合は、`No major findings` を出さない。少なくとも `Major revisions`、主張の中心が失われていれば `Reject / 証明として不十分` にする。

3. 仮定放電を theorem family 単位で追う。
   - 大定理の各主要仮定が、GOAL の前提として許されたものか、別 theorem / construction / instance で放電済みか、未放電の仮定として残っているかを分類する。
   - 結論相当の lawfulness、certificate、compatibility、gluing、nonempty witness、repair witness、transport data を仮定に入れている場合は、証明ではなく assumption package として扱う。
   - `discharge-required` な premise は、明示引数に出ているだけでは放電済みにしない。certificate を受け取る theorem ではなく、その certificate を対象境界から構成する theorem / finite witness / concrete construction を探す。見つからなければ `undischarged` とする。
   - theorem argument、typeclass、structure field、certificate field、opaque class membership に material premise が移されていないか確認する。特に sheaf condition、semantic faithfulness、exactness、effectivity、descent、global coherence、obstruction vanishing、representation adequacy、finite-shadow adequacy は通常 `discharge-required` として扱う。
   - proof term / `#print` / declaration body で主要 premise が実際に使われているかを見る。未使用 premise が main theorem の外観だけを強くしている場合は finding とする。

4. 依存補題と台帳を照合する。
   - main theorem だけでなく、主張を支える spine theorem、bridge theorem、finite example、witness construction、candidate card、`lean_theorem_index.md`、`proof_obligations.md` を読む。
   - 依存補題に未放電 obligation があれば、大定理の完了判定へ伝播させる。

5. 完了判定を fail-closed にする。
   - 強さ一致、仮定放電、依存補題、`#print axioms`、台帳整合のどれかが確認不能なら `未確認` または `Blocked / cannot determine` とする。
   - 仮定未放電または弱い形の証明が確認されたら、`Reject / 証明として不十分` とする。
   - `No major findings` は、数学査読 A/B と Lean 査読 A/B の 4 本すべてで強さ一致、仮定放電、依存補題、axiom audit、台帳整合が確認でき、かつ残リスクが大定理の中心 claim に影響しない場合だけ使う。

## Lean 検証

対象に応じて最小限から広げる。

- focused check: `lake env lean <target-file>`
- package / module check: `lake build <module>` または `lake build`
- theorem dependency audit: 対象 Lean declaration ごとに `#print axioms <DeclarationName>` を一時確認する。複数 declaration が対象なら全件必須とし、未実行の declaration 名は最終報告の coverage に列挙する。確認用 scratch は `.tmp/` に置き、成果物に混ぜない。
- placeholder scan: `rg -n "\b(axiom|admit|sorry|unsafe)\b|by\\s+trivial|by\\s+simp\\s*$" Formal`
- hidden / bidi scan when reporting changed artifacts: `rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-or-reviewed-files>`

`#print axioms` の解釈では、Lean/mathlib の通常依存と、この repo が導入した `axiom`、未証明 placeholder、選択公理依存、証明の薄さを分けて報告する。`Classical.choice` だけで即失格にはしないが、存在・一意性・構成性を主張する本文と矛盾する場合は finding にする。

## 厳格判定ポイント

次を疑う。パターン語彙(結論射影 / `True` 充足 / instance 実在 / 非退化発火)は
`prd-completion-review` の Lean 反証チェックリストと共有し、判定基準を skill 間でずらさない。

- 主張一致: 本文 theorem / GOAL claim が Lean theorem statement と同じ強さか。Lean が片方向、弱い predicate、選択済み witness、有限例、特殊ケースだけになっていないか。
- 仮定過多: theorem の仮定に結論相当の情報、ready-made certificate、lawfulness、nonempty witness、decidable equality、finite support、compatibility が埋め込まれていないか。
- 未放電: proof obligation、index、TODO、placeholder、`axiom`、`sorry`、abstract parameter、opaque witness が本質的な穴を隠していないか。
- certificate provenance: certificate が主張の入力境界から Lean theorem / construction / finite witness で作られているか。単に explicit argument として渡されているだけなら放電ではない。
- unused premise: theorem statement の material premise が proof body で使われているか。未使用 premise は、同値や構成を支える条件ではなく、近傍 package の飾りになっている可能性がある。
- 定義の薄さ: predicate が `True`、structure field が実質 marker、theorem が definitional unfolding だけ、example が実 witness ではなく wrapper になっていないか。
- 未発火: 主張された theorem / package の非退化 instance / witness がリポジトリに実在するか。`(E : …)` 前提の条件文だけで `E` の concrete instance が無い場合は未発火として扱う。発火例の係数・担体が PUnit、自明群、singleton site、`True` 充填なら、本文が退化例を明示的に許容しない限り発火と認めない。
- structure-field escape: quotient relation、exactness、descent、effectivity、compatibility、naturality、comparison、global coherence の主要部分が structure field として供給されていないか。供給 field から accessor theorem を出しているだけなら、構成証明ではなく conditional surface と判定する。
- 依存補題: 対象 theorem は clean でも、依存補題が未証明、過大仮定、特殊化、または本文 claim と違う universe / coefficient / topology / site / category を使っていないか。
- 反例可能性: 本文主張に必要な separatedness、base change、descent、cover stability、functoriality、cohomology coefficient、stack quotient、finite/infinite distinctionが抜けていないか。
- 台帳整合: `lean_theorem_index.md`、`proof_obligations.md`、GOAL card、candidate card、report が Lean 実体と同じ rigor label を持つか。theorem 系 status は三分化語彙(`proved` / `packaged (assumption-relative)` / `statement-only`)と整合するか。仮定パッケージの帰結が `proved` を名乗っていないか。
- 範囲外の切り分け: AAT の theorem claim が要求していない ArchMap 抽出完全性、source coverage、tooling evidence completeness、外部実証 completeness を、証明未達の finding と混同していないか。

## Material Premise Discharge Audit

大定理 / target theorem の最終 gate では、次を独立した必須監査にする。

1. **Premise ledger extraction**
   - GOAL card の `target premise discharge policy`、`target material premise ledger`、completion criteria、report の final packet から material premise を列挙する。
   - 各 premise を `ambient-boundary`、`direction-hypothesis`、`discharge-required`、`conclusion-equivalent-risk` に分類する。

2. **Certificate provenance**
   - `discharge-required` premise ごとに、対応 certificate / class membership / instance / structure field の生成元を探す。
   - 生成元が theorem argument、opaque field、hand-supplied compatibility、selected comparison data に止まる場合は未放電とする。
   - 放電済みと呼べるのは、対象境界の入力 data から certificate を作る theorem、有限 witness、構成、または既に査読済みの predecessor theorem が確認できる場合だけである。

3. **Proof-use check**
   - main theorem の proof term、`#print`、補題呼び出しを見て、material premise が主結論の証明に使われているか確認する。
   - premise が package の別成分として出力されるだけ、または `_premise` として未使用なら、主張の放電ではなく添付証拠として finding にする。

4. **Field-content audit**
   - structure / certificate の field 名だけで安心しない。field の型が `H1Zero`、boundary membership、global coherence、effectivity token、vanishing、comparison equivalence、exactness implication、descent conclusion、semantic closure などを直接保持していないか読む。
   - 結論の一部を field が供給している場合は、field が透明でも hidden premise と同等に扱う。

5. **Fail condition**
   - `discharge-required` premise が theorem argument / certificate field / structure field に残る場合、`No major findings` は禁止する。
   - その theorem は `target-theorem-proved` ではなく、`target-proof-checkpoint`、conditional theorem、support surface、または boundary-narrowed theorem として報告する。

## Multi-Agent Review

正式な `$math-lean-review` 判定では、数学査読 2 本と Lean 査読 2 本の multi-agent review を必須とする。ユーザーが `$math-lean-review` と同時に「4 体」「parallel」「subagent」「並列レビュー」などを明示した場合は、live tool contract が許す限り 4 体を並列起動する。

ユーザーが `$math-lean-review` だけを指定し、subagent / parallel work の明示承認がない場合は、レビューを開始する前に 4 体並列査読の承認を短く求める。承認なしに single-thread だけで正式合格判定を出してはいけない。

multi-agent tool が使えない環境、または live tool contract が subagent 起動を許さない環境では、親 Codex が同じ 4 本を順番に実行できる場合だけ provisional review として報告する。この場合も `No major findings` や証明完了判定は出さず、coverage limit に `multi-agent review not run` を明記する。対象本文、候補 Lean 宣言、依存補題、または `#print axioms` のいずれかが確認不能で、4 本の代替レビューも実施できない場合は、最終判定を `Blocked / cannot determine` に落とす。

親 Codex が先に対象命題、候補 Lean 宣言、関連ファイル、検証済みコマンドを整理してから、次の 4 本に分ける。役割は「4つの違う薄い観点」ではなく、数学査読 2 本と Lean 査読 2 本の重複独立レビューにする。同じ査読を 2 本走らせ、片方が見落とした弱化・未放電・境界違反をもう片方で拾う。

1. **数学査読 A**
   - 本文 / GOAL の theorem claim と必要仮定を、研究論文の査読者として全体から読む。
   - 主張の強さ、量化、係数、site / topology、反例方向、欠けている仮定、範囲外要求の混入を独立に判定する。

2. **数学査読 B**
   - 数学査読 A と同じ claim を、別の独立査読として再読する。
   - A の補助ではなく、同じ合格基準で弱化、未放電前提、反例、定義不足、claim boundary の誤りを探す。

3. **Lean 査読 A**
   - 候補 Lean declaration、statement、定義、型、universe、instance、仮定リスト、proof term、依存補題、`#print axioms`、placeholder scan、focused build を一通り追う。
   - Lean statement が数学 claim を弱めていないか、仮定・certificate・structure field に結論を逃がしていないか、未放電 obligation がないかを独立に判定する。
   - material premise の certificate provenance、proof-use、field-content を追い、explicit certificate を放電済みと即断しない。

4. **Lean 査読 B**
   - Lean 査読 A と同じ declaration 群と依存補題を、別の独立査読として再検査する。
   - A の補助ではなく、同じ合格基準で statement 弱化、仮定過多、thin certificate、unused premise、structure-field escape、axiom 依存、台帳 / proof obligation drift を探す。

親 Codex は 4 本の結果を統合するとき、数学 A/B の不一致、Lean A/B の不一致、数学査読と Lean 査読の claim mapping 不一致を finding 候補として扱う。片方だけが見つけた懸念も、根拠があれば落とさない。

## Sub-Agent Prompt

```text
Use the math-lean-review skill context. Review only the assigned reviewer lane.
Target mathematical claim: <quoted theorem/proposition/GOAL claim or file section>
Candidate Lean declarations: <names and files, or "not found yet">
Relevant files: <paths>
Reviewer lane: <数学査読 A | 数学査読 B | Lean 査読 A | Lean 査読 B>

Report in Japanese:
1. Findings, ordered by severity, with file/line/theorem references when available.
2. Evidence checked.
3. Material premise discharge audit: which premises are ambient, direction hypotheses, discharged, or still certificate/field assumptions.
4. Certificate provenance / proof-use concerns, especially unused premises and structure-field escape.
5. Commands or Lean queries that should be run for this lane.
6. Coverage limits.

Do not edit files. Do not implement fixes. The parent must not pass expected findings or a provisional verdict to you. If you are assigned A or B, act as an independent reviewer, not as a helper for the other reviewer. Do not issue the final integrated verdict. Do not assume that a passing Lean file or an explicit certificate proves the prose claim. Stay anchored in the assigned lane, but report any obvious proof-breaking issue you directly see.
```

## 親 Codex の統合判定

sub-agent の結果をそのまま貼らず、親 Codex が重複、矛盾、過剰指摘、coverage gap を整理する。最終報告は次の形にする。

1. 判定: `Reject / 証明として不十分`, `Major revisions`, `Minor issues`, `No major findings`, `Blocked / cannot determine`
2. Findings: 重大度順。各 finding は数学 claim、Lean declaration、根拠、影響、必要な修正方針を含める。
3. Claim mapping: 本文 / GOAL claim と Lean declaration の対応表。
4. Material premise audit: 結論相当の条件、ready-made witness、certificate、lawfulness、compatibility を仮定に逃がしていないか。
5. Certificate provenance audit: material premise ごとに、certificate / field / class membership の生成 theorem、finite witness、construction、または未放電 status を明記する。
6. Proof-use / field-content audit: main theorem の proof term で premise が使われているか、structure field が結論成分を供給していないかを明記する。
7. Premise discharge status: 各主要仮定が本文 theorem の前提として正当か、別 theorem / construction で放電済みか、未放電か。
8. Anti-weakening verdict: Lean statement が本文 claim を弱めていないか。弱い場合は、どの方向・量化・対象・係数・site・universe・witness で弱いかを明記する。
9. Undischarged obligations: proof obligation、TODO、axiom、sorry、opaque witness、未確認依存補題の一覧。
10. Axiom / dependency audit: `#print axioms`、placeholder scan、依存補題確認の結果。対象 declaration ごとに実施 / 未実施を明記する。
11. 査読別まとめ: 数学査読 A/B と Lean 査読 A/B の結論、不一致、重複 finding、片方だけが見つけた懸念。
12. 実行した検証: コマンドと結果。
13. Coverage / residual risk: 読んだ範囲、未確認範囲、subagent 使用可否、未実行検証。

`No major findings` は rare pass として扱う。数学的 claim の中心に触れる未確認、弱化、未放電、台帳不一致が少しでも残るなら使わない。explicit certificate があるだけで provenance / proof-use / field-content audit が閉じていない場合も使わない。

重大な穴がある場合は、婉曲にしない。Lean 実装が数学本文の theorem を証明していないなら、そのまま「この Lean theorem は当該命題の形式化・証明としては不足」と書く。ただし、対象 claim が要求していない ArchMap 抽出完全性や tooling completeness を理由に不合格へしない。
