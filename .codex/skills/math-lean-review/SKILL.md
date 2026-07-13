---
name: math-lean-review
description: PR作成後のレビューゲートと大定理のcompletion candidateで、最終スナップショットのAATの数学本文・GOAL・固定statementとLean実装を、仮定放電、certificate provenance、proof-use、依存、台帳まで4本の独立査読で判定する。"$math-lean-review"、review-prの最終ゲートで使う。
---

# Math Lean Review

数学本文・GOAL・命題テキストと Lean 実装の対応を、研究論文の査読として扱う。目的は実装や修正ではなく、主張、仮定、証明依存、形式化scope、台帳状態が本当に一致しているかを厳しく判定することである。

特に `research/goals/<goal-id>.md` の大定理モードでは、この skill は「大定理が証明されたこと」を完了条件にするループの査読 gate である。過去に、仮定が放電されていないまま大定理が弱い形で Lean 上は通ってしまう事例があったため、証明完了判定は fail-closed に行う。

この skill は、入力として渡された AAT / Lean の数学 claim と Lean 実装を査読する。PR や差分が AAT / Lean 分野レビューに該当するかどうかは、この skill の外側で決まる。この skill に Lean 実装と `docs/aat/` 台帳差分が一緒に渡された場合は、statement と台帳記載の一致を一体で監査する。

## 必須契約

`.codex/skills/_shared/review-protocol.md` と
`.codex/skills/_shared/refutation-checklist.md`、
`.codex/skills/_shared/lean-refutation-checklist.md`を読み、非編集・独立査読・
fail-closed・反証試行・証拠資格・報告形式をそのまま適用する。

## 基本方針

- 判定は可能な限り厳しくする。数学者の論文査読レベルを基準にし、合格判定は例外的にしか出さない。迷う場合は `No major findings` ではなく、証拠不足・仮定不足・弱化可能性として `Major revisions`、`Reject / 証明として不十分`、または `Blocked / cannot determine` に倒す。
- Findings first で書く。証明として不完全、主張過大、仮定依存、未放電、`axiom` / `sorry` / `admit` / `unsafe` / `by trivial` 風の薄い証明、台帳 drift を優先して出す。
- 対象 theorem だけを眺めて完了扱いにしない。定義、補題、instance、import 元、依存 theorem、example、index / proof obligation / GOAL claim まで、主張の成立に必要な依存範囲を読む。
- statement 品質・定義品質・スタイルの判定正本は
  `docs/aat/lean_quality_standard.md`(mathlib 型 statement review 基準)。
  material premise 三分類申告(本文由来 / 放電済み / 未放電)は実装者の
  申告を証拠採用せず、レビュー側が premise を独立に列挙して申告と突合する
  (申告のない仮定は未放電)。指定されたstatement contract(PRD、GOALカード、
  候補カード`planned_lean_statement`、Issue、その他の参照可能なartifact)がある対象は、実装
  declaration の signature と突合し、乖離は anti-weakening finding とする。
- Lean が通ることは十分条件ではない。仮定が主張を丸ごと含んでいる、`Prop` が弱すぎる、 witness が選択済みすぎる、非空性や decidability や finite universe を hidden assumption にしている、`True` wrapper / marker theorem になっている場合は finding とする。
- explicit certificate はそれだけでは放電ではない。certificate / class membership / structure field / theorem argument が material premise を透明に保持しているだけなら、未放電 premise として扱う。必ずその certificate 自体を生成する theorem / construction / finite witness / instance chain を追う。
- theorem statement に現れる premise が proof term で実質的に使われているかを確認する。未使用の `sheafCondition`、`faithfulness`、`exactness`、`descent` などは、主張補強ではなく ledger/package への添付にすぎない可能性が高い。
- 大定理モードでは、「大定理名の theorem が存在する」「main theorem が build する」「候補カードが proved と言っている」だけでは完了にしない。本文 / GOAL が要求する強さ、主要仮定の放電、依存補題のstatementとproof dependency、台帳の rigor label が揃って初めて証明完了候補とする。
- `docs/aat/algebraic_geometric_theory/`、`docs/sft/software_field_theory.md`、`docs/sft/aat_interface.md` は保護対象。レビュー目的で読んでよいが、明示的な本文編集依頼なしに変更しない。
- AAT / GOAL / Lean theorem の claim scope 外にある事項を未達 finding にしない。たとえば ArchMap の抽出完全性、実プロジェクトからの evidence completeness、tooling の observation completeness、runtime measurement exhaustiveness は、対象 claim が明示的に要求していない限りレビュー対象外とする。
- coverage を明示する。読んだ本文、読んだ Lean 宣言、依存として追った範囲、未確認範囲、実行した検証を分ける。

## 入力解釈

1. ユーザー指定を対象にする。
   - 数学本文: `docs/aat/algebraic_geometric_theory/...`、`docs/note/...`、Markdown 節、命題文。
   - 研究 GOAL: `research/goals/<goal-id>.md` の GOAL card、frontier、spine、target theorem、大定理モードの完了条件。
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
- `research/goals/<goal-id>.md`
- 対象 Lean ファイルと、その import 先 / 依存補題
- 対象数学本文。ただし保護対象の本文はレビューのみで編集しない

## GOAL card 大定理モード

`research/goals/<goal-id>.md` の大定理モード、target theorem、spine theorem、または「この大定理が証明されたら完了」というループをレビューするときは、次を完了 gate にする。

1. GOAL claim を正確に抽出する。
   - 大定理名、本文の自然言語 claim、必要な仮定、対象 universe、係数、site / topology、量化範囲、結論の強さを分ける。
   - GOAL card と supporting note / candidate card / report がある場合は、どれが完了条件で、どれが背景説明かを区別する。

2. Lean statement が GOAL claim を弱めていないか確認する。
   - 一方向だけ、有限例だけ、選択済み witness だけ、特殊 universe だけ、追加 compatibility 仮定つき、構成ではなく存在だけ、存在ではなく marker だけ、という弱化を finding にする。
   - 弱化がある場合は、`No major findings` を出さない。少なくとも `Major revisions`、主張の中心が失われていれば `Reject / 証明として不十分` にする。

3. 仮定放電を theorem family 単位で追う。
   - 大定理の各主要仮定が、GOAL の前提として許されたものか、別 theorem / construction / instance で放電済みか、未放電の仮定として残っているかを分類する。
   - 結論相当の lawfulness、certificate、compatibility、gluing、nonempty witness、repair witness、transport data を仮定に入れている場合は、証明ではなく assumption package として扱う。
   - `discharge-required` な premise は、明示引数に出ているだけでは放電済みにしない。certificate を受け取る theorem ではなく、その certificate を対象の入力dataから構成する theorem / finite witness / concrete construction を探す。見つからなければ `undischarged` とする。
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

重い Lean 検証には `AGENTS.md` の「Lean build 運用(hard rule)」を適用する。
4本の独立査読では `lake build` の結果を共有し、各査読者は `lake build` を実行しない。
追加検証は focused check に限定する。

- focused check: subagentへ許す場合は、親が明示した単一の非aggregate fileに対する
  `lake env lean <target-file>`だけとする。aggregate root、module群、全file loopは禁止する。
- package / module check: 統括エージェントだけがPR前に
  `lake build <module>`または`lake build`のどちらか1回を実行し、結果を各review laneへ渡す。
  Research packageのfull buildはCIで実行しない。必要な場合だけ統括エージェントが
  `cd research/lean && lake build`をローカルで1回実行し、subagentは実行しない。
- theorem dependency audit: 対象 Lean declaration ごとに `#print axioms <DeclarationName>` を一時確認する。複数 declaration が対象なら全件必須とし、未実行の declaration 名は最終報告の coverage に列挙する。確認用 scratch は `.tmp/` に置き、成果物に混ぜない。
- placeholder scan: `rg -n "\b(axiom|admit|sorry|unsafe)\b|by\\s+trivial|by\\s+simp\\s*$" Formal`
- hidden / bidi scan when reporting changed artifacts: `rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-or-reviewed-files>`

`#print axioms` の解釈では、Lean/mathlib の通常依存と、この repo が導入した `axiom`、未証明 placeholder、選択公理依存、証明の薄さを分けて報告する。`Classical.choice` だけで即失格にはしないが、存在・一意性・構成性を主張する本文と矛盾する場合は finding にする。

## Research import方向検査(hard fail)

レーンの裁量なしに、必ず機械検査する。

```bash
# 本体(Formal/AG 本線)から Research への import は禁止。
# Research packageの内部importは正当なので、本体だけを検査する
rg -n "import ResearchLean\.AG" Formal Formal.lean
```

- ヒットのうち**差分が新規に追加した行**が1件でもあれば、他のすべての
  観点の結果にかかわらず **`Reject / 証明として不十分`** とする。
  4本全承認ゲートで覆せない(承認の対象外)。
- 差分と無関係な既存ヒット(main 由来)は、その PR の Reject 理由には
  しないが、**既存のimport方向違反 blocker** としてユーザーへ即時報告する
  (黙認しない)。
- **移植(蒸留)は import ではない。** 「Research の theorem を本体へ
  移植した」という主張の実体が Research module の import +再導出
  ラッパーである場合、それは蒸留ではなく**依存 repackage**であり、
  対象の status は `unported (Research-proved)` のまま。台帳・PR 本文が
  これを「移植済み」と表示していれば、監査表示の過大化として finding に
  する。
- import の方向規律: `research/lean/ResearchLean/` 側が本体を import するのは可。
  逆方向は常に禁止(研究 sandbox と正本の疎結合。PRD-R AC18 不変条件)。
- `Formal.lean` / `Formal/AG.lean` 等の配線変更が Research module を
  default build の依存へ引き込んでいないかも同時に検査する。

## 厳格判定ポイント

次を疑う。基底パターン語彙(結論射影 / `True` 充足 / instance 実在 /
非退化発火 / 公理 / anti-weakening)、意味レベル空虚パターン、
移植元conjunct対応の正本は`lean-refutation-checklist.md`、no-go適用範囲、
帰属・ロック値検査、横断機械scanの正本は`refutation-checklist.md`にある。
以下は本skill固有の観点として両referenceと併せて適用する。

- 主張一致: 本文 theorem / GOAL claim が Lean theorem statement と同じ強さか。Lean が片方向、弱い predicate、選択済み witness、有限例、特殊ケースだけになっていないか。
- 仮定過多: theorem の仮定に結論相当の情報、ready-made certificate、lawfulness、nonempty witness、decidable equality、finite support、compatibility が埋め込まれていないか。
- 未放電: proof obligation、index、TODO、placeholder、`axiom`、`sorry`、abstract parameter、opaque witness が本質的な穴を隠していないか。
- certificate provenance: certificate が主張の入力dataから Lean theorem / construction / finite witness で作られているか。単に explicit argument として渡されているだけなら放電ではない。
- unused premise: theorem statement の material premise が proof body で使われているか。未使用 premise は、同値や構成を支える条件ではなく、近傍 package の飾りになっている可能性がある。
- 定義の薄さ: predicate が `True`、structure field が実質 marker、theorem が definitional unfolding だけ、example が実 witness ではなく wrapper になっていないか。
- 未発火: `lean-refutation-checklist.md` §1のinstance実在・非退化発火を適用する。
- structure-field escape: quotient relation、exactness、descent、effectivity、compatibility、naturality、comparison、global coherence の主要部分が structure field として供給されていないか。供給 field から accessor theorem を出しているだけなら、構成証明ではなく conditional surface と判定する。
- 依存補題: 対象 theorem は clean でも、依存補題が未証明、過大仮定、特殊化、または本文 claim と違う universe / coefficient / topology / site / category を使っていないか。
- 反例可能性: 本文主張に必要な separatedness、base change、descent、cover stability、functoriality、cohomology coefficient、stack quotient、finite/infinite distinctionが抜けていないか。
- 台帳整合: `lean_theorem_index.md`、`proof_obligations.md`、GOAL card、candidate card、report が Lean 実体と同じ rigor label を持つか。theorem 系 status は三分化語彙(`proved` / `packaged (assumption-relative)` / `statement-only`)および `unported (Research-proved)` と整合するか。仮定パッケージの帰結が `proved` を名乗っていないか。
- API 品質: import、namespace、命名、局所性が既存 pattern と整合しているか。定義が過度に抽象化されていないか。theorem statement が使いやすい形か(不要に強い仮定・弱すぎる結論になっていないか)。
- 範囲外の切り分け: AAT の theorem claim が要求していない ArchMap 抽出完全性、source coverage、tooling evidence completeness、外部実証 completeness を、証明未達の finding と混同していないか。

## Material Premise Discharge Audit

大定理 / target theorem の最終 gate では、次を独立した必須監査にする。

1. **Premise ledger extraction**
   - GOAL card の `target premise discharge policy`、`target material premise ledger`、completion criteria、report の final packet から material premise を列挙する。
   - 各 premise を `ambient-boundary`、`direction-hypothesis`、`discharge-required`、`conclusion-equivalent-risk` に分類する。

2. **Certificate provenance**
   - `discharge-required` premise ごとに、対応 certificate / class membership / instance / structure field の生成元を探す。
   - 生成元が theorem argument、opaque field、hand-supplied compatibility、selected comparison data に止まる場合は未放電とする。
   - 放電済みと呼べるのは、対象の入力dataから certificate を作る theorem、有限 witness、構成、または既に査読済みの predecessor theorem が確認できる場合だけである。

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

正式レビューとして起動された場合、数学査読 A/B と Lean 査読 A/B の4本を実行し、4本すべての承認を
合格条件とする。4本は補助関係ではなく、同じ基準を持つ重複独立査読とする。
lane定義、追加出力、統合schemaは
[references/reviewer-lanes.md](references/reviewer-lanes.md)を読む。

起動時点はPR作成後のレビューゲート(`review-pr`経由)または`target-theorem-loop`の完了判定に
限る。実装中はfocused checkまたは必要な単一subagentの確認に限定する。正式査読でfindingが出た
場合は、全laneのfindingをまとめて実装フェーズを再開し、修正後の確認は共有review protocolの
「レビューバッチと修正後確認」に従う。直接対応の資格を満たす修正(statement不変・新規宣言なし・
import方向不変・台帳status不変のproof内部または台帳・docs記載の修正)はfinding限定の
単一subagentで確認し、4本を再実行しない。資格を失う修正は、最終スナップショットを固定し直して
から正式レビューとして4本を再実行する。

## 親 Codex の統合判定

4 laneの結果をそのまま連結せず、重複、矛盾、claim mappingの不一致、
coverage gapを統合する。出力は共有契約と
[references/reviewer-lanes.md](references/reviewer-lanes.md)のschemaに従う。

重大な穴がある場合は、婉曲にしない。Lean 実装が数学本文の theorem を証明していないなら、そのまま「この Lean theorem は当該命題の形式化・証明としては不足」と書く。ただし、対象 claim が要求していない ArchMap 抽出完全性や tooling completeness を理由に不合格へしない。
