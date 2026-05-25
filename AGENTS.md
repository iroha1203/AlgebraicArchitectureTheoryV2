# リポジトリ運用ガイド

## 言語と GitHub 運用

- ユーザーへの応答は日本語で行う。
- コミットメッセージは日本語で書く。
- Pull Request のタイトルと本文は日本語で書く。
- GitHub Issue のタイトルと本文は日本語で書く。
- Lean の識別子、ファイル名、コマンド名、定理名、既存の英語技術用語を引用する場合は、名前をそのまま残してよい。必要に応じて日本語で補足する。

## Codex 作業 Rules

- 作業は原則として GitHub Issue 起点で進める。
- 次タスクを選ぶときは、`priority:blocking`, `status:ready`, milestone の依存順を優先する。
- Issue が前提タスクの完了で着手可能になった場合は、必要に応じて `status:blocked` を外し、`status:ready` を付ける。
- 実装作業は `main` を最新化してから専用ブランチを切る。
- ブランチ名は Issue 番号または作業内容が分かる名前にする。
- PR 本文には対象 Issue を `Closes #N` 形式で明記する。
- PR 本文は `.github/pull_request_template.md` に沿って、概要、証明した定理、編集したドキュメント、実施したテスト、チェックリストを埋める。
- 既存の未コミット変更がある場合は、ユーザーの変更として扱い、勝手に戻さない。
- `git reset --hard` や `git checkout --` のような破壊的操作は、明示的な依頼なしに実行しない。

## PR 前チェック

- Lean 変更を含む PR では、必ず `lake build` を実行する。
- ArchSig 変更を含む PR では、必ず `cargo test --manifest-path tools/archsig/Cargo.toml` を実行する。
- FieldSig 変更を含む PR では、必ず `cargo test --manifest-path tools/fieldsig/Cargo.toml` を実行する。
- website 変更を含む PR では、静的ページをグローバルインストール済み Playwright で確認し、リンク・asset path・レイアウト崩れを確認する。
- website 動作確認では、`python3 -m http.server 8000 --directory website` のような固定ポートの常駐サーバーを原則として避ける。
- Codex から Playwright を実行する場合、macOS のブラウザ起動権限により通常の sandbox 内実行で Chromium が固まることがあるため、原則として sandbox 外実行を使う。
- ドキュメントのみの PR でも、Lean status、tool schema、website copy への影響を確認する。迷う場合は関連する build / test を実行する。
- PR 前に `git diff --check` を実行する。
- PR 前に hidden / bidirectional Unicode scan を実行し、bidi control や zero-width 文字が混入していないことを確認する。
- Lean ソースに `axiom`, `admit`, `sorry`, `unsafe` が混入していないか、必要に応じて確認する。
- Rust ソースに不用意な `unwrap`, `expect`, `panic!`, placeholder 実装、claim boundary を曖昧にする fallback が混入していないか、変更範囲に応じて確認する。
- `.github/workflows` を変更した場合は、対応するローカル検証コマンドと workflow trigger / permissions / artifact path が実体と合っているか確認する。
- GitHub PR 作成後は `gh pr checks --watch` などで CI が通ることを確認する。

## プロジェクト構成

- Lean ライブラリの root は `Formal.lean`。
- 中核となる形式化は `Formal/Arch` 以下に置く。
- 研究ノートは `docs` 以下に置く。
- AAT の数学本文は `docs/aat/mathematical_theory.md`、Lean status と proof obligation は `docs/aat/proof_obligations.md` と `docs/aat/lean_theorem_index.md` で管理する。
- SFT 本文は `docs/sft/software_field_theory.md`、AAT / SFT 境界は `docs/sft/aat_interface.md` で管理する。
- tooling 仕様・schema・workflow 文書は `docs/tool` 以下に置く。
- `docs/archive` は過去文書の退避先であり、現行の source of truth として扱わない。
- Rust tooling は `tools/archsig` と `tools/fieldsig` 以下に置く。`archsig` は Lean 証明器ではなく、Architecture Signature 用の AAT structural telemetry / review artifact generator として扱う。`fieldsig` は SFT-based software evolution measurement layer として扱う。
- 公開 website は `website` 以下に置く。`docs` とは別の GitHub Pages 向け公開読書面として扱う。
- CI / Pages 設定は `.github/workflows` 以下に置く。Lean / Rust test は `lean.yml`、Signature diff は `signature-diff.yml`、GitHub Pages deploy は `pages.yml` で管理する。
- `Main.lean` は実行ターゲット `aatv2` を提供する。
- build 設定は `lakefile.toml`。
- Lean バージョンは `lean-toolchain` で固定する。
- ArchSig crate 設定は `tools/archsig/Cargo.toml`、lockfile は `tools/archsig/Cargo.lock` で管理する。FieldSig crate 設定は `tools/fieldsig/Cargo.toml`、lockfile は `tools/fieldsig/Cargo.lock` で管理する。

## Build コマンド

- `lake build`: すべてのターゲットを build する。
- `lake build Formal`: Lean ライブラリだけを build する。
- `lake exe aatv2`: 実行ターゲットを実行する。
- `lake env lean Formal/Arch/Core/Layering.lean`: 単一ファイルを type-check する。
- `cargo test --manifest-path tools/archsig/Cargo.toml`: ArchSig の test suite を実行する。
- `cargo test --manifest-path tools/fieldsig/Cargo.toml`: FieldSig の test suite を実行する。
- `cargo run --manifest-path tools/archsig/Cargo.toml -- --root . --out .lake/sig0.json`: repository root の ArchSig scan を実行する。
- `playwright --version`: グローバルインストール済み Playwright CLI が利用可能か確認する。
- `NODE_PATH="$(npm root -g)" node -e "const { chromium } = require('playwright'); (async () => { const browser = await chromium.launch({ headless: true }); const page = await browser.newPage(); await page.goto('file://' + process.cwd() + '/website/index.html'); console.log(await page.title()); await browser.close(); })();"`: website の静的ページを Playwright で確認する。Codex から実行する場合は原則として sandbox 外実行を使う。

## 形式化ポリシー

- 明示的な相談なしに `axiom`, `admit`, `sorry`, `unsafe` を導入しない。
- 定義は小さく保ち、同値性や対応関係は定理として育てる。
- 現在の `Decomposable` は `StrictLayered` を意味する。
- acyclicity, finite propagation, nilpotence, spectral conditions は `Decomposable` の定義に混ぜない。これらは別個の定理または将来の proof obligation として扱う。
- `ComponentCategory` は thin category であり、path count や walk length を意図的に忘れる。
- 定量指標は `Walk`, `Path`, adjacency matrix, または将来の free-category construction 側で扱う。
- executable metrics は、まず有限な測定 universe 上の計算として定義し、graph-level facts との接続は別 theorem として証明する。
- `ComponentUniverse` は proof-carrying measurement universe として扱う。実コードベース抽出器の完全性を直接主張しない。

## Rust Tooling ポリシー

- `tools/archsig` は Rust で実装された ArchSig CLI / library として扱う。
- 理論的な位置付け、claim boundary、非結論、adapter boundary は `docs/tool` と関連する AAT / SFT 文書に従う。
- JSON artifact / schema / report の互換性を壊す変更では、`docs/tool` と fixture / validation test を合わせて更新する。
- CLI surface を追加・変更する場合は、`tools/archsig/README.md` と `tools/archsig/docs/commands.md` を必要に応じて更新する。
- PR / CI 向け report は、結論だけでなく `nonConclusions`, `unmeasuredAxes`, theorem precondition status, evidence boundary を読める形に保つ。
- 実証研究用 dataset や operational feedback artifact は、相関・観測・仮説を因果 theorem と混同しない。

## FieldSig Tooling ポリシー

- `tools/fieldsig` は Rust で実装された SFT-based software evolution measurement CLI / library として扱う。
- FieldSig は ArchSig output を JSON artifact ref として受け取る。Rust 型共有を cross-tool contract として扱わない。
- FieldSig artifact は SoftwareFieldMeasurement / ForecastCone / ConsequenceEnvelope / governance / calibration / operational feedback を扱うが、forecast correctness、probability、causal correctness、global safety、CI/Test/human review の置換を主張しない。
- CLI surface を追加・変更する場合は、`tools/fieldsig/README.md` と `tools/fieldsig/docs/commands.md` を必要に応じて更新する。

## ドキュメントポリシー

- `docs` の研究主張を変更する場合は、対応する Lean status を明確にする。
- Lean status は、proved, defined only, future proof obligation, empirical hypothesis を区別する。
- Lean で証明済みの主張と、実証研究で検証する主張を混同しない。
- `docs` は研究上の定義、理論本文、Lean status、proof obligation、tooling specification、empirical protocol を管理する source として扱う。
- `README.md` と `README.jp.md` は入口文書として扱い、詳細な theorem 一覧、Issue 一覧、進捗台帳を重複して持たせない。
- `docs/archive` の文書は歴史的参照として扱い、現行文書の更新時に archive 側へ同じ変更を反映しない。ただし、移行メモや参照切れ修正が目的の場合は例外とする。
- 公開 website の本文、読者導線、landing page 向け説明は `docs` の責務にしない。website 側の説明は docs の研究上の境界を参照してよいが、docs を website copy の source of truth として扱わない。
- `公開 API` や `public API` のように Lean / tooling API の公開性を指す語は、website 向け記述とは区別して扱う。
- `docs/aat/mathematical_theory.md` は AAT 数学面の第一級設計書として扱い、Lean status、Issue 番号、実装済み API の進捗管理を本文に混ぜない。
- Lean status や Issue との対応は `docs/aat/proof_obligations.md` と `docs/aat/lean_theorem_index.md` で管理する。
- 数学設計書には、数学的な定義・定理候補・非目標・設計上の境界を記述し、実装済み / 証明済み / 未着手といった作業状態は別文書へ分離する。
- `docs/aat/proof_obligations.md` は GitHub Issues への索引としても使う。
- theorem や定義を追加した場合は、必要に応じて `docs/aat/proof_obligations.md` の Lean status を更新する。
- 研究の大目標は「設計原則はアーキテクチャ不変量を保存・改善する操作であり、品質は不変量の破れを多軸シグネチャとして評価する」ことである。この主張と矛盾する説明を追加しない。
- Architecture Signature は単一スコアではなく、多軸診断として扱う。
- 設計原則の分類では、SOLID を万能原理として扱わない。SOLID は局所契約層、Layered / Clean Architecture は大域構造層、Event Sourcing / Saga / CRUD は状態遷移代数層、Circuit Breaker / Replicated Log は実行時依存・分散収束層として整理する。

## Website ポリシー

- `website` は GitHub Pages 向けの公開読書面であり、`docs` の研究・実装管理文書とは責務を分ける。
- AAT / SFT の canonical page は宣伝文ではなく、web-native preprint / monograph として、定義・仮定・定理境界・例・反例・Lean status・non-conclusion を保つ。
- website は AAT / SFT の体系的解説として、その魅力を語り尽くす場でもある。claim boundary を守りつつ、読者が「何が見えるようになるか」「何が計算可能になるか」「どの概念が次の理解を開くか」を前面に出す。
- website copy は `docs/website/README.md` の Tone Guide に従う。防衛的な書き方や否定から入る説明を避け、`SFT studies ...`, `SFT defines ...`, `SFT computes ...`, `SFT systematizes ...`, `SFT makes ... computable.`, `SFT treats ... as ...` のように研究対象と可能になることを堂々と宣言する。
- Overview / landing / chapter introduction では、すべてを説明しきるよりも、読者を次の概念へ進ませる。章本文では field, force, attractor, basin, ForecastCone, ConsequenceEnvelope などの SFT 固有語彙を、危険さと魅力のある言葉として丁寧に定義し、計算可能な読みへ接続する。
- website の説明は `docs/aat/mathematical_theory.md`, `docs/sft/software_field_theory.md`, `docs/sft/aat_interface.md`, `docs/tool` の claim boundary から逸脱しない。
- claim boundary、Lean status、Issue 管理、repository / docs の責務分離は編集時の制約として扱い、公開コピーにそのまま出さない。読者向け本文では「何を読めるか」「何を理解できるか」「どの概念へ進むか」に翻訳する。
- 公開ページで repository、docs、Lean status、Issue、内部運用方針に触れるのは、読者の理解や検証に必要な場合に限る。landing page や section copy では、内部の根拠管理・進捗管理を説明文として書かない。
- public release で docs や Lean status にリンクする場合は、可能な限り commit-pinned GitHub URL を使い、`blob/main` による silent drift を避ける。
- ArchSig website では Core / Review の AAT structural surface と FieldSig 側の SFT / Operational / governance surface を分けて書く。
- 現在の website は no-build static stack として扱う。重い frontend framework は、静的 HTML / CSS / 小さな JavaScript では足りない明確な理由がある場合だけ導入する。
- asset path は project Pages 配下でも壊れないように相対 path を使い、root-absolute path を避ける。
- production `sitemap.xml` や canonical host は、公開 domain または GitHub Pages base URL が確定するまで placeholder で追加しない。
- GitHub Pages deploy は `main` への push で `website/**` または `.github/workflows/pages.yml` が変わった場合に走る。公開確認が必要な変更では Pages workflow の結果も確認する。

## タスク管理

- 未解決課題は GitHub Issues で管理する。
- Issue は研究の依存構造に沿って milestone に割り当てる。
- Issue の label は `type:*`, `area:*`, `priority:*`, `status:*` を使って整理する。
- empirical extractor や実証研究の Issue は Lean proof の進行をブロックしないように扱う。
