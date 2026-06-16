# AAT / Lean 編集ガイドライン

この文書は `Formal/AG`、`Formal/Arch`、`docs/aat` を編集するときの作業方針をまとめる。

## 位置づけ

- AAT は Atom から architecture object、law、obstruction circuit、operation、flatness、path / homotopy、analytic representation を構成する局所代数の核である。
- AAT は Atom を公理的出発点とする。実コードベース抽出器、ArchMap observation、tooling validation は
  Atom 入力を提示・検査する前段または後段 surface であり、AAT の theorem package の完了条件ではない。
- AAT 自体に observation / measurement / tooling boundary はない。境界を持つのは、Atom 入力を提示する
  ArchMap、LawPolicy による選択、ArchSig / FieldSig の測定 artifact、または empirical dataset である。
- Lean source は Atom から生成される純粋な algebra / theorem package を形式化する場所である。
  実測や empirical correlation は、AAT ではなく tooling / SFT 側の artifact に相対化して扱う。
- Lean 形式化は全知の検査器ではない。形式化対象は、AAT の語彙で明示的に述べられる命題に限る。
  全 runtime、全 semantic universe、source extraction completeness、tooling validation completeness を
  AAT theorem package のスコープに入れない。
- `docs/aat/algebraic_geometric_theory/` は現行 AAT 数学本文の正典である。Lean status、Issue 番号、実装済み API の進捗管理は本文に混ぜない。
- `docs/aat/algebraic_geometric_theory/` は AAT の根幹文書である。ユーザーの明示的な指示なしに更新しない。
- Lean status と Issue との対応は `docs/aat/proof_obligations.md` と `docs/aat/lean_theorem_index.md` で管理する。

## Lean 形式化方針

- 明示的な相談なしに `axiom`, `admit`, `sorry`, `unsafe` を導入しない。
- 定義は小さく保ち、同値性や対応関係は定理として育てる。
- 現在の `Decomposable` は `StrictLayered` を意味する。
- acyclicity、finite propagation、nilpotence、spectral conditions は `Decomposable` の定義に混ぜない。別個の定理または将来の proof obligation として扱う。
- `ComponentCategory` は thin category であり、path count や walk length を意図的に忘れる。
- 定量指標は `Walk`, `Path`, adjacency matrix、または将来の free-category construction 側で扱う。
- executable metrics は、まず有限な measurement universe 上の計算として定義し、graph-level facts との接続は別 theorem として証明する。
- `ComponentUniverse` は proof-carrying measurement universe として扱う。source extraction の成否は
  AAT core の定理ではなく、ArchMap / tooling 側の入力生成 contract として扱う。
- ArchSig や Rust tooling の有用性を Lean との対応で正当化しない。Lean 側は AAT の語れる命題を支える
  形式化であり、ArchSig は別に `ArchMap + LawPolicy + evidence contract` から診断結論を出す tool である。

## docs の claim discipline

- Lean status は `proved`, `defined only`, `future proof obligation`, `empirical hypothesis` を区別する。
- Lean で証明済みの主張と、実証研究で検証する主張を混同しない。
- 完了レビューでは、対象文書が列挙した theorem、suite field、acceptance theorem、fixture、Issue closure を
  直接照合する。対象文書が要求していない無制限 claim を「未完了部分」として追加しない。
- 禁止: AAT の完了レビューで source-observation layer の性質を `non-conclusion`、残タスク、
  未完了 claim、証明不能な限界として列挙しない。AAT は Atom を公理とするので、source code から Atom input
  を提示する過程は AAT theorem package の外側にある。必要なら ArchMap / ArchSig / FieldSig の
  具体的な artifact、fixture、schema、validator、Issue acceptance として別管理する。
- non-conclusion / claim boundary は、具体的な theorem や artifact の近くで必要な分だけ記録する。
  レビュー報告や残タスク欄を、一般的に証明不能な巨大 claim の一覧にしない。
- 語れることだけを確かに語る。AAT / Lean docs では、語れない外部領域を `non-conclusion` 一覧として
  主役化しない。必要な boundary は、定理や artifact の有効範囲を示すために最小限だけ置く。
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
