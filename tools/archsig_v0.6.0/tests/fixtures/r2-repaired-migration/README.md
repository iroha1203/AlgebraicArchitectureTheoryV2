# 修復後の T3 消費と raw cancel の対照

[#6297 の E12](../r2-e12-consume/README.md) の Consume first から T3 の局所対応を使う。
期待 snapshot が一致し、output1 の live allocation と stock に収まる消費だけを共通操作域に含めた。
消費量 1 は 1/16 単位で 16。元側で数量が15の状態を仕様例として用意し、実 `apply` で16へ更新する。
T3 の比較用状態に置いた building と status は元の Consume first の output1 に合わせた。
入力は稼働 DB からの新しい測定を含まない。

- `before` の数量 Law は反証。有限の解から `chosen` を選び、実 `fixed.object` を
  `native` と `nativeWide` の局所に渡す。更新後の Law は成立する。
- `migrate` は T3 の consume だけを生成元として読み、操作保存を成立と判定する。
  `target` は実際の移行先を使って数量 Law を検査する。
- 広い読取りでは output1 の T3 と、R2 の raw cancel で差が出た output2 の局所を
  同じ比較用の全体に組み立てる。両側の T3 の数量 Law が成立しても、
  native 側は `building=true,status=10` に、Rust 側は `building=false,status=65` に進む。
  状態対応は同じ flag と code の状態同士を結ぶ。比較のために明示した対応先には、
  その操作が実際には到達しない対照状態も含む。写像は cancel の端点保存を反証する。各状態値は原始操作の `.to` を辿って読む。

このディレクトリで実行する。

```sh
set --
while IFS= read -r ask; do
  set -- "$@" --ask "$ask"
done < queries.txt
archsig run --atom-definition definitions.json --law laws.law --archmap archmap.json --out out "$@"
```

[期待出力](expected.json) は保存回答の状態の投影で、終了コードは1。統合テストは選択 Assignment、
元局所と包含、移行先、名前付き操作の保存命題と raw cancel の両端点 Atom を照合する。
比較する対象は修復後の一つの経路とその明示操作域である。
