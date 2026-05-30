# AAT / Lean 編集ガイドライン

この文書は `Formal/Arch` と `docs/aat` を編集するときの作業方針をまとめる。

## 位置づけ

- AAT は Atom から architecture object、law、obstruction circuit、operation、flatness、path / homotopy、analytic representation を構成する局所代数の核である。
- Lean source は研究主張を形式化する場所であり、実コードベース抽出器の完全性や empirical correlation を直接主張する場所ではない。
- `docs/aat/mathematical_theory/` は数学本文である。Lean status、Issue 番号、実装済み API の進捗管理は本文に混ぜない。
- `docs/aat/mathematical_theory/` は AAT の根幹文書である。ユーザーの明示的な指示なしに更新しない。
- Lean status と Issue との対応は `docs/aat/proof_obligations.md` と `docs/aat/lean_theorem_index.md` で管理する。

## Lean 形式化方針

- 明示的な相談なしに `axiom`, `admit`, `sorry`, `unsafe` を導入しない。
- 定義は小さく保ち、同値性や対応関係は定理として育てる。
- 現在の `Decomposable` は `StrictLayered` を意味する。
- acyclicity、finite propagation、nilpotence、spectral conditions は `Decomposable` の定義に混ぜない。別個の定理または将来の proof obligation として扱う。
- `ComponentCategory` は thin category であり、path count や walk length を意図的に忘れる。
- 定量指標は `Walk`, `Path`, adjacency matrix、または将来の free-category construction 側で扱う。
- executable metrics は、まず有限な measurement universe 上の計算として定義し、graph-level facts との接続は別 theorem として証明する。
- `ComponentUniverse` は proof-carrying measurement universe として扱う。実コードベース抽出器の完全性を直接主張しない。

## docs の claim discipline

- Lean status は `proved`, `defined only`, `future proof obligation`, `empirical hypothesis` を区別する。
- Lean で証明済みの主張と、実証研究で検証する主張を混同しない。
- theorem や定義を追加した場合は、必要に応じて `docs/aat/proof_obligations.md` と `docs/aat/lean_theorem_index.md` を更新する。
- `docs/archive` は歴史的参照として扱い、現行文書の更新時に同じ変更を反映しない。
- Architecture Signature は単一スコアではなく、多軸診断として扱う。
- 設計原則の分類では、SOLID を万能原理として扱わない。SOLID は局所契約層、Layered / Clean Architecture は大域構造層、Event Sourcing / Saga / CRUD は状態遷移代数層、Circuit Breaker / Replicated Log は実行時依存・分散収束層として整理する。

## 検証

Lean 変更を含む場合は次を実行する。

```bash
lake build
```

単一ファイルを確認する場合は次の形を使う。

```bash
lake env lean Formal/Arch/Core/Layering.lean
```

PR 前には次も確認する。

```bash
git diff --check
rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>
rg -n "\b(axiom|admit|sorry|unsafe)\b" Formal docs
```
