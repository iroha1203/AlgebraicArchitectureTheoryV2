# Tooling 編集ガイドライン

この文書は `tools/archsig`、`tools/fieldsig`、`docs/tool` を編集するときの作業方針をまとめる。

## 境界

- ArchMap は supplied `archmap-observation-map-v0` evidence を読む source-grounded Atom observation map である。law-independent な観測、gap、projection info、concern hints、provenance、non-conclusions を記録する。
- LawPolicy / interpretation profile は、law universe、witness rule、molecule pattern、obstruction circuit definition、signature axis、coverage requirement、exactness assumption を選ぶ profile である。AAT そのものではない。
- ArchSig は ArchMap + interpretation profile から `archsig-analysis-packet-v0` を作る AAT structural analysis layer である。Lean 証明器ではない。
- `concernHints` は review cue であり、obstruction circuit、law violation、theorem evidence ではない。
- FieldSig は `archsig-analysis-packet-v0` を bounded current AAT structural state として読み、SFT 側の evolution measurement / governance input へ写す。raw ArchMap observations を forecast truth として読まない。
- ArchSig validation は extractor completeness、semantic correctness、architecture lawfulness、global safety、certified universal atom truth、zero curvature、SFT forecast correctness、Lean theorem discharge を証明しない。

## CLI / schema 方針

- ArchSig の現行一次 workflow は `analyze` である。新しい docs、script、CI では `analyze` を使う。
- `llm-native-workflow` / `north-star-workflow` は同じ workflow の compatibility alias として扱う。
- pre-Atom workflow は Git history に残るだけで、現行 ArchSig surface や compatibility input として扱わない。
- JSON artifact / schema / report の互換性を壊す変更では、`docs/tool`、tool README、fixtures、validation tests を合わせて更新する。
- CLI surface を追加・変更する場合は、必要に応じて `tools/archsig/README.md`、`tools/archsig/docs/commands.md`、`tools/fieldsig/README.md`、`tools/fieldsig/docs/commands.md` を更新する。
- Rust 型共有を ArchSig / FieldSig 間の cross-tool contract として扱わない。serialized JSON artifact boundary を重視する。
- Rust source では不用意な `unwrap`, `expect`, `panic!`、placeholder 実装、claim boundary を曖昧にする fallback を避ける。

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
  --out-dir .lake/archsig-analyze
```

FieldSig handoff:

```bash
cargo run --manifest-path tools/fieldsig/Cargo.toml -- archsig-analysis-sft-input \
  --analysis-packet .lake/archsig-analyze/archsig-analysis-packet.json \
  --out .lake/fieldsig/operation-support-estimate.json
```

PR 前には次も確認する。

```bash
git diff --check
rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>
```
