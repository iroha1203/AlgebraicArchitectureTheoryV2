# ArchSig v0.6.0

コードから観測した Atom と Law の上で、アーキテクチャを計算する道具。
何を入力に何を計算し何が返るかは [ArchSig v0.6.0 マニュアル](../../docs/tool/archsig_manual/README.md) が正であり、実装はそれに合わせる。

## 今できること

マニュアル第2章の一周に要るものを実装している。

| コマンド | 章 |
| --- | --- |
| `archsig status` | 第3章 読んだ範囲、第7章 archsig-observe |
| `archsig record <Atom のファイル>…` | 第3章 ArchMap のファイル |
| `archsig law check` | 第4章 |
| `archsig plan check <候補>` | 第5章 問い3(`changes commute with operations`、`changes keep`、消える要素を使う操作) |
| `archsig plan split <候補> [--reading <読み>]` | 第5章 問い7 分ける |
| `archsig compare --plan <候補>`、`--base <コミット>` | 第5章 問い3 実装後に比べる |
| `archsig show <結果>` | 第6章 |

Law ファイルは第4章の文法をすべて読む。計算するのは `changes` の規則だけで、ほかの規則の Law はサマリの `not_computed` に並ぶ。

## 試す

```bash
cargo test --manifest-path tools/archsig-v06/Cargo.toml
```

`tests/chapter2.rs` が、第2章の `shop` の例(`tests/fixtures/shop/`)で、沈黙、反例、成立、分担、実装後の比較までを通す。
