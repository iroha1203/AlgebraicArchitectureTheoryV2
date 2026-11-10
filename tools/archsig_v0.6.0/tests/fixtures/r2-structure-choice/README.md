# 有限の配置選択と T3 の移行

[#6297 の T3 対応](../r2-e12-consume/README.md) を残し、同じ全体 root に二種類の担当を
配置できる仕様を追加した。設計主体 `plan` は `old` と `new` に型付きの担当集合を持つ。
前者は native の担当、後者は Rust の担当であり、`split` の Bool 値で選ぶ。
両候補は別の個体、owner、操作端点を構成する。同じ表示名を持つ別の主体 `lookalike` には
異なる候補表を与えた。この配置の二択は ArchSig 用の設計例である。

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
