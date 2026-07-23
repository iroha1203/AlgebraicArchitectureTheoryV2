# リポジトリ作業ガイド

このファイルは、このモノレポで Codex が迷わず作業を始めるための入口である。
詳細な編集方針は各領域の `guideline.md` に分ける。

- [AAT / Lean guideline](docs/aat/guideline.md)
- [SFT guideline](docs/sft/guideline.md)
- [Tooling guideline](docs/tool/guideline.md)
- [Website guideline](docs/website/guideline.md)
- [PRD guideline](docs/prd/guideline.md)

## 基礎概念

- AAT は、Atom を primitive architectural fact として公理化し、law を方程式系として重ねる
  代数幾何的アーキテクチャ論である。Atom family から生成される architecture object を、
  lawful locus、obstruction、sheaf、cohomology、derived / stacky structure として読む。
- AAT は比喩ではなく、Atom を基礎単位としてアーキテクチャを本物の代数幾何の対象にする。
  そのため、特定のプログラミング言語、フレームワーク、ADL、実装形態に依存せず、
  言語を越えた architectural fact を同じ数学的基盤で扱える。
- AAT は本気で代数幾何を行う。Atom を土台に、site、Grothendieck topology、sheaf、
  ringed topos、scheme、Čech cohomology、derived / stacky structure などの本物の
  代数幾何概念へ接続していく。Lean 形式化でも、AAT 専用の仮置き wrapper や
  名前だけの analogue に留めず、定義、comparison map、同値、obstruction / scope theorem を通じて
  既存の数学的構造へ接続する方向を優先する。
- AAT の強みは、アーキテクチャを geometry として扱い、局所性、貼り合わせ、obstruction、
  変形、高次構造、repair 可能性を site / sheaf / law algebra / cohomology の同じ土台で
  分析できる点にある。既存の設計パターンも、経験則ではなく local model、幾何構造、
  gluing condition、singularity、obstruction、cohomological phenomenon として再解釈できる。
- semantic atom は、静的解析では扱いにくい意味論、責務、補償、不変条件、業務意味、
  side-effect discipline を AAT の対象へ持ち込むための基礎単位である。局所的には整合する
  architectural data、certificate、repair が大域的に貼り合わない問題は、必要に応じて
  `H^1` obstruction などの cohomological obstruction として読む。
- SFT は、artifact、practice、AI、review、CI、operational feedback が software evolution の
  reachable future をどう変えるかを扱う。AAT が構造の幾何を扱い、SFT が実践と進化の場を扱う。
- SFT の強みは、個別の artifact や workflow を、software evolution の reachable future を変える
  場の操作として統一的に読める点にある。
- ArchMap は、選ばれた Atom vocabulary と evidence contract の中で architecture evidence を記録する
  有限 artifact である。
- LawPolicy / MeasurementProfile は、law reading、cover、witness、measurement regime を固定する
  contract である。
- ArchSig は ArchMap と LawPolicy から bounded diagnostic / analysis packet を計算する tooling である。
- ArchSig の強みは、AAT の強力な幾何的理論を tooling 上で活かし、ArchMap と LawPolicy から
  lawful locus、obstruction、coverage、witness を読む高度な architecture analysis を計算できる点にある。
- ArchView は ArchMap の Atom / Context / Cover をコードベース理解の geometry として可視化し、
  その上に ArchSig の分析結果を重ねて source landing へ接続する。FieldSig は analysis packet と
  workflow evidence を SFT 側の evolution measurement / governance input として読む。
- Website は、AAT / SFT / tooling を公開向けに読むための publication surface である。
- Lean status は、証明済みの主張、定義のみの概念、将来の証明義務、実証仮説を区別して読む。

## モノレポの地図

このリポジトリは Lean 形式化、Rust tooling、公開 website、研究 docs が同居する。
同じ語でも領域によって責務が違うため、作業前に対象領域を確認する。

| 領域 | 主な場所 | 役割 | 詳細 |
| --- | --- | --- | --- |
| Lean / AAT | `Formal/AG`, `Formal/Arch`, `Formal.lean` | AAT / SFT の形式化、定義、定理、例。 | [AAT guideline](docs/aat/guideline.md) |
| AAT docs | `docs/aat` | AAT 数学本文、Lean status、proof obligation。 | [AAT guideline](docs/aat/guideline.md) |
| SFT docs | `docs/sft` | Software Field Theory と AAT / SFT interface。 | [SFT guideline](docs/sft/guideline.md) |
| Tooling | `tools/archsig`, `tools/archview`, `tools/fieldsig`, `docs/tool` | ArchMap / LawPolicy / ArchSig / ArchView / FieldSig の CLI、schema、visualization、workflow。 | [Tool guideline](docs/tool/guideline.md) |
| Website | `website`, `docs/website` | Cloudflare Pages 向け public reading surface と内部運用メモ。 | [Website guideline](docs/website/guideline.md) |
| Outreach | `outreach` | AAT / SFT / ArchSig の外部記事、翻訳、下書き、記事用素材。 | [Outreach README](outreach/README.md) |
| 研究プログラム | `research/`, `research/lean/ResearchLean/` | 研究 GOAL の下で候補探索 → 三審判 → Lean 検証 / 証拠固定 → SCORE 監査 → フェーズ区切り判定を回すループ engine と検証 sandbox。 | [research README](research/README.md) |
| Archive | `docs/archive` | 過去文書の退避先。現行 source of truth として扱わない。 | [docs README](docs/README.md) |

## 責務範囲

- AAT は Atom と law から立つ純粋理論である。ArchSig は ArchMap と LawPolicy から
  bounded diagnostic を計算する。観測者責務範囲は ArchMap author と evidence contract の責務として
  一括して扱う。
- ウィトゲンシュタイン的責務範囲を守る。選ばれた vocabulary、policy、evidence contract から
  語れることだけを語る。語れない領域は、失敗や残タスクではなく沈黙として扱う。
- AAT / Lean theorem の説明・レビューでは、定理が語る選択済み vocabulary、仮定、対象だけを
  肯定形で述べる。ユーザーや対象 artifact が明示していない限り、
  「この定理は実コードベース全体を対象としません」のような外側の否定 claim を付け足さない。
  外側は補足 caveat ではなく沈黙で扱う。
- Tooling の identity も同じ規律で書く。ArchSig の定義は
  「ArchMap + LawPolicy + MeasurementProfile から bounded verdict を計算する計測層」という
  肯定形であり、結論の相対性はこの入力契約に由来する帰結として述べる。
  「theorem prover ではない」「global truth ではない」のような否定形免責を
  identity 文へ習慣的に併記しない。否定を書くのは、読者の実在する誤推論を塞ぐ場合だけ、
  結論の近くで一度に限る。

## 作業規律

- ユーザーへの応答、commit message、PR / Issue の title と本文は日本語で書く。
  Lean 識別子、ファイル名、コマンド名、定理名、既存の英語技術用語はそのまま扱う。
- `docs/aat/algebraic_geometric_theory/`、`docs/sft/software_field_theory.md`、
  `docs/sft/aat_interface.md` の更新は、次の3条件がすべて揃う場合に限る。
  1. 人間の明示的な編集指示がある。対象文書と変更方針を特定した指示に限り、
     曖昧な依頼や他作業からの派生判断を編集許可と読まない。
  2. 実装者以外の LLM がレビューする(Codex 実装なら Claude レビュー、
     Claude 実装なら Codex レビュー)。
  3. 人間が差分を確認して merge する。LLM はこれらのファイルを含む PR を merge しない。
- 完了レビューや残タスク整理では、対象 Issue / PRD / 計画書 / acceptance test が要求する
  concrete condition だけを判定する。
- PRDの責務、参照禁止、完了後archiveの正本は [PRD guideline](docs/prd/guideline.md)
  とする。PRD作業では同guidelineをhard ruleとして適用し、既存違反も例外扱いしない。
- 作業は原則として GitHub Issue 起点で進める。次タスクは `priority:blocking`、`status:ready`、
  milestone の依存順を優先する。
- 一時的な検証や監査のための gate / task を恒久 CI に追加してはならない。
  一回限りの確認は `.tmp/` またはローカルコマンドで実施し、必要な証拠だけを Issue / PR に記録する。
  workflow への job / step 追加など、CI に新しい task を追加する変更は、編集前に人間の明示的な承認を
  得なければならない。
- 目的に対して自然に必要な設計、実装、docs、tests、website surface まで広げてよい。
  ただし、無関係な既存変更の巻き戻し、claim scope を越える主張、根拠のない互換性維持、
  不要な抽象化は避ける。
- 実装作業は `main` を最新化してから専用ブランチを切る。ブランチ名は Issue 番号または作業内容が
  分かる名前にする。PR 本文には `Closes #N` を明記し、`.github/pull_request_template.md` に沿って書く。
- 既存の未コミット変更はユーザーの変更として扱い、勝手に戻さない。
  `git reset --hard` や `git checkout --` は明示的な依頼なしに実行しない。
- `.lake` は Lake の build / dependency cache 専用とし、一時出力は `.tmp/` または `/private/tmp` に置く。
- ArchSig の test は ArchSig の runtime、CLI、schema、ArchSig が生成する serialized artifact だけを検査する。
  `tools/archsig` の Rust unit / integration / golden test から ArchView の HTML、UI、scene、内部関数、
  browser behavior、または website の source、文言、route、layout を検査することを禁止する。
  ArchView は `tools/archview/` が所有する browser / UI test、website は website の build / browser test で検査する。
- レビューは分野別の敵対レビュー SKILL
  (`math-lean-review` / `tool-review` / `website-review` / `docs-review`)で行う。
  共通の反証観点は `.codex/skills/_shared/refutation-checklist.md` を正本とする。
- Lean 実装(`Formal/`)を触る差分は、大きさを問わず PR 作成後のレビューゲートとして
  `math-lean-review` の4本の独立査読を行う。承認は、4本すべての合格、または finding
  全解消+`review-protocol.md` に従う有資格な修正後確認(直接対応)の記録をもって成立する。
- 正式レビューの起動時点、finding 修正後の直接対応(finding 限定の軽量確認)と
  正式レビュー再実行の条件は、`.codex/skills/_shared/review-protocol.md`を正本とする。
- Research 側で受理済みの成果が本体に無い状態は、scope 制限ではなく
  `unported (Research-proved)`(未移植)と呼ぶ。詳細は
  `docs/aat/guideline.md` の Lean status discipline を参照する。

## 「境界」という言葉の使用を禁止する

この節は AAT / Lean 作業の停止規則である。Codex はここを「推奨」ではなく
実装・レビュー・完了判定の hard rule として扱う。

### 原則

この見出しで名指しした語を `禁止語` とする。AAT / Lean 作業では `禁止語` を使用しない。
使いそうになった場合は停止し、下の対応表に従って具体的な状態名へ置き換える。

Lean 実装は数学本文を再定義しない。数学本文より弱い theorem、本文にない material premise、
結論相当の premise を外部入力として受け取る theorem、wrapper / alias / repackage は、
いずれも本文の証明ではない。`lake build`、`#print axioms`、theorem 名の存在、docs / ledger の整備は、
この欠陥を補わない。

AAT / Lean 形式化は mathlib 型の statement review 基準を採用する。仮定を増やして局所的に
通るだけの theorem、本文の数学的仕事を premise に肩代わりさせる theorem、既存 API と
接続しない閉じた wrapper theorem、再利用価値のない弱い theorem は査読を通さない。
実装前に target statement を固定し、完了判定は theorem 名の存在ではなく固定 statement との
一致で行う。実装中に仮定・結論・対象を変更した場合は、その時点で未達として停止する。
この statement review 基準と一次仕様・直接査読の手続きの正本は
`docs/aat/lean_quality_standard.md`(Lean 品質基準)である。

数学本文側に明示された制限は、`明示 scope`、`stated scope`、`対象の制限`、
`定理の仮定`、`statement の対象制限` と書く。無条件主張の不可能性を言う場合は、
証明済み theorem / counterexample の宣言名、statement、量化対象、本文主張との対応を
示せない限り、`未証明` / `要求未達` / `theorem strength mismatch` として扱う。
no-go 風の説明は免罪符にしない。

この規則に反する実装・説明・完了判定を見つけたら、Codex は作業を止めて
本文主張、実装 theorem、追加された仮定、未放電 premise、放電に必要な補題または未移植 theorem を
報告する。レビューでは major finding とし、完了根拠として数えない。

### 対応表

| 状態 | 使う語 |
| --- | --- |
| Research 側にはあるが AG 本体にない | `Research 成果の未蒸留` / `未移植` / `unported (Research-proved)` |
| Lean theorem がまだない | `未証明` |
| API、comparison、witness、proof chain がつながっていない | `未接続` |
| 本文にない仮定を theorem 引数、typeclass、structure field、certificate field で受けている | `未放電仮定` / `仮定相対` |
| implementation がない | `未実装` |
| theorem が数学本文や完了要求より弱い | `要求未達` / `theorem strength mismatch` |
| wrapper、alias、repackage、renaming だけで通している | `wrapper` / `alias` / `repackage` |
| completion evidence として使えない中間状態 | `完了根拠ではない` |
| 不可能性を主張しているが、証明済み theorem / counterexample の宣言名・statement・量化対象・本文主張との対応を提示できない | `未証明` / `要求未達` / `theorem strength mismatch` |
| certificate に結論相当の premise が入っており、それを読むだけで theorem が閉じる | `certificate escape` / `未放電仮定` |
| structure field に結論相当の premise が入っており、それを読むだけで theorem が閉じる | `structure-field escape` / `未放電仮定` |
| typeclass に結論相当の premise が入っており、それを読むだけで theorem が閉じる | `typeclass escape` / `未放電仮定` |
| 本文の theorem を Lean 都合で局所化・有限化・対象固定化したが、本文由来の根拠がない | `theorem strength mismatch` / `要求未達` |
| 比較写像、同値、witness、obstruction の生成が残っている | `未接続` / `未構成` / `未放電仮定` |
| 禁止語を避けた説明を書いただけで close 可能としている | `完了根拠ではない` / `Reject` |

- 対応表にない状態でも、`禁止語` を使わず、状態を直接表す語を選ぶ。

## 主要な入口

- `PHILOSOPHY.md`: プロジェクトの核となる思想と問い(なぜ)。
- `docs/README.md`: 研究 docs 全体の読み方。
- `docs/aat/algebraic_geometric_theory/README.md`: 代数幾何的 AAT 数学本文の入口。
- `Formal/`: Lean 形式化の実体。
- `research/goals/` と GitHub Issues: 作業状態と未解決課題。
- `docs/sft/software_field_theory.md`: SFT 本文。
- `docs/sft/aat_interface.md`: AAT / SFT interface。
- `docs/tool/README.md`: ArchMap / LawPolicy / ArchSig / ArchView / FieldSig の現行 tooling scope。
- `docs/website/README.md`: website の運用メモ。
- `research/README.md`: 研究ループ engine(`$research-loop`)の入口。

## よく使う検証

変更範囲に応じて必要な検証を選ぶ。

### Lean build 運用(hard rule)

- 通常作業とサブエージェント査読では、親が明示した単一の非aggregate fileに対する
  `lake env lean <target-file>` だけを実行する。
- サブエージェントからの `lake build` はtarget指定の有無を問わず全面禁止する。
  `lake build` を内部で呼ぶscript、skill、workflowに加え、別commandによるpackage全体、
  module群、aggregate root、全file loopのelaborationも禁止する。
- 親プロンプトや個別SKILLが実行を求めてもこの禁止を優先する。
  必要な場合は実行せず、統括エージェントまたはCIが担う未確認項目として返す。
- 本体のフル `lake build` はローカルで実行しない。PR 作成後の CI で実行し、その結果を完了確認に使う。

```bash
# 本体のフル Lean build は PR 作成後の CI で実行する
cargo test --manifest-path tools/archsig/Cargo.toml
cargo test --manifest-path tools/fieldsig/Cargo.toml
git diff --check
rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>
```

ArchSig の現行一次 workflow は `analyze` である。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json \
  --law-policy tools/archsig/tests/fixtures/ag_measurement/law_policy_ag.json \
  --measurement-profile tools/archsig/tests/fixtures/ag_measurement/measurement_profile_ag.json \
  --law-surface tools/archsig/tests/fixtures/ag_measurement/law_surface_ag_v052.json \
  --out-dir .tmp/archsig-analyze
```

website は Eleventy で authoring し、配信 artifact は純静的とする(詳細は [Website guideline](docs/website/guideline.md))。directory route、asset path、`sitemap.xml`、`robots.txt` を確認する場合は dev server で preview する。

```bash
cd website && npx @11ty/eleventy --serve   # 初回は npm install
```

Codex から Playwright を実行する場合、macOS のブラウザ起動権限により通常の sandbox 内実行で Chromium が固まることがある。必要に応じて sandbox 外実行を使う。

## PR 前の確認

- Lean 変更を含む場合、統括エージェントは変更範囲に応じて対象ファイルの focused check、対象moduleの targeted build、必要な監査を選ぶ。本体のroot全体のフル `lake build` は PR 作成後の CI で確認する。
- ArchSig 変更を含む場合は `cargo test --manifest-path tools/archsig/Cargo.toml` を実行する。
- ArchView 変更を含む場合は `tools/archview/` が所有するbrowser / UI testを使い、local server経由で確認する。ArchSigのRust testからArchViewのUI、scene、内部関数を検査しない。
- FieldSig 変更を含む場合は `cargo test --manifest-path tools/fieldsig/Cargo.toml` を実行する。
- Website 変更を含む場合は Playwright などで主要ページの title、link、asset path、layout を確認する。
- docs-only 変更でも Lean status、tool schema、website copy への影響を確認する。
- PR 前に `git diff --check` と hidden / bidirectional Unicode scan を実行する。
- GitHub PR 作成後は `gh pr checks --watch` などで CI を確認する。
