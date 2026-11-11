# 有限の配置選択と T3 の移行

[#6297 の T3 対応](../r2-e12-consume/README.md) の原始端点を使う。Law の担当 View は
`split` と `reversed` を比較して `t.from` または `t.to` を担当集合にする。
`plan` と `lookalike` は表示名が同じで `reversed` が異なる。両方に `split=true` を適用すると、
前者は Rust、後者は native の担当・所有個体・操作端点を組み立てる。この二択は ArchSig 用の仕様例である。

- `prepare → solve → candidate → apply` が、設計主体の Bool を含む実 Assignment を作る。
  同じ `plan` を束縛した二つの組立ては、それぞれ選択値を保持した別の `design` と担当を返す。
- `lookalike` に同じ Bool を適用しても、`plan` の配置選択としては拒否される。
  `plan` の Assignment を `lookalike` の解集合へ適用する要求も拒否される。
- `move-T3` は Rust 配置へ届く。native 配置を選んだ全体を終域にすると局所対応の端点が合わず、
  保存条件を反証する。成立する写像では名前付き consume の保存命題を辿り、移行後の数量 Law を別に検査する。

このディレクトリで実行する。

```sh
set --
while IFS= read -r ask; do
  set -- "$@" --ask "$ask"
done < queries.txt
archsig run --atom-definition definitions.json --law laws.law --archmap archmap.json --out out "$@"
```

[期待出力](expected.json) は保存回答の状態を投影したもの。統合テストは設計の実出力、選んだ
担当 root、Map の終域、両操作を参照先から照合する。対象域は宣言した二配置と T3 の対応に限る。
