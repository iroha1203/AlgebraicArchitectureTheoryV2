# Tooling 編集ガイドライン

この文書は `tools/archsig`、`tools/fieldsig`、`docs/tool` を編集するときの作業方針をまとめる。

## 境界

- ArchMap v1 は supplied `archmap/v1` evidence を読む source-grounded Atom map である。primary input は `sources` / `atoms` / `molecules` であり、gap、projection info、concern hints、provenance、non-conclusions を primary schema に戻さない。
- AAT は Atom を公理的出発点とする。ArchMap / extractor は source code から Atom input を提示・検査する
  実測 surface であり、AAT の定理や完了条件を定義しない。
- LawPolicy v1 は policy pack / evaluator / basis / scope / severity を選ぶ selector である。witness rule、signature axis、coverage requirement、exactness assumption、distance rule は evaluator registry の責務である。AAT そのものではない。
- ArchSig は ArchMap + LawPolicy から typed evaluator results と `archsig-analysis-packet/v1` を作る AAT structural analysis layer である。Lean 証明器ではない。Rust と Lean の対応を tooling contract として要求しない。
- ArchSig は tool として肯定的な bounded diagnostic conclusion を出す。たとえば
  `SAFE_WITHIN_POLICY`、`NO_SELECTED_OBSTRUCTION`、`ACCEPTABLE_UNDER_EVIDENCE_CONTRACT`、
  `DISTANCE_WITHIN_THRESHOLD` のように、選ばれた LawPolicy、DistanceProfile、evidence contract の中で
  語れることを確かに語る。
- ArchSig は、未観測 runtime 全体や global semantic safety のように選ばれた evidence language の外にあるものを、
  failure、残タスク、Lean linkage requirement、長い `non-conclusion` 一覧として扱わない。外側は必要最小限の
  silence boundary として扱う。
- Review notes may exist outside ArchMap, but removed v0 fields such as `concernHints` are not v1 diagnostic input.
- FieldSig は `archsig-analysis-packet-v0` を bounded current AAT structural state として読み、SFT 側の evolution measurement / governance input へ写す。raw ArchMap observations を forecast truth として読まない。
- ArchSig validation は、schema、refs、generated middle layer、selected law-policy reading、fixture expectation など、
  明示された tooling contract を検査する。Lean theorem、実運用上の正しさ、予測精度を要求する場合は、
  それぞれ専用の theorem / fixture / dataset / issue として定義してから扱う。
- PRD や完了レビューでは、PRD 自身の acceptance criteria と実装済み test / fixture を照合する。
  PRD が要求していない巨大な一般 claim を、未完了タスクとして追加しない。

## CLI / schema 方針

- ArchSig の現行一次 workflow は `analyze` である。新しい docs、script、CI では `analyze` を使う。
- `llm-native-workflow` / `north-star-workflow` は同じ workflow の compatibility alias として扱う。
- pre-Atom workflow は Git history に残るだけで、現行 ArchSig surface や compatibility input として扱わない。
- JSON artifact / schema / report の互換性を壊す変更では、`docs/tool`、tool README、fixtures、validation tests を合わせて更新する。
- CLI surface を追加・変更する場合は、必要に応じて `tools/archsig/README.md`、`tools/archsig/docs/commands.md`、`tools/fieldsig/README.md`、`tools/fieldsig/docs/commands.md` を更新する。
- Rust 型共有を ArchSig / FieldSig 間の cross-tool contract として扱わない。serialized JSON artifact boundary を重視する。
- Rust source では不用意な `unwrap`, `expect`, `panic!`、placeholder 実装、claim boundary を曖昧にする fallback を避ける。
- Report / schema / CLI wording は「これは結論ではない」を主文にしない。結論、根拠、選ばれた evidence contract を
  先に出し、語らない領域は必要な場合だけ短い boundary として添える。

## 主要コマンド

```bash
cargo test --manifest-path tools/archsig/Cargo.toml
cargo test --manifest-path tools/fieldsig/Cargo.toml
```

ArchSig analyze:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out-dir .tmp/archsig-analyze
```

FieldSig handoff:

```bash
cargo run --manifest-path tools/fieldsig/Cargo.toml -- archsig-analysis-sft-input \
  --analysis-packet .tmp/archsig-analyze/archsig-analysis-packet.json \
  --out .tmp/fieldsig/operation-support-estimate.json
```

PR 前には次も確認する。

```bash
git diff --check
rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>
```
