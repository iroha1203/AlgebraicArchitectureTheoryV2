# 共有境界を合わせた局所修復の再組立て

R2 P3 の `experiment/p3-integration/independent-draft-v1/COMMON-STRUCTURE.json` は、
site ごとの私有配置を残し、明示した origin alias を使う再構成を計画している。
その条件を9個体で読む仕様例を構成した。A/B は二拠点、ma/mb は同じ共有位置の明示的な対、
a/b はそれぞれの私有位置。左右の Step は共有位置につながる各拠点の名前付き操作である。
個体 ID、量 0/1、操作はこの例の定義で、R2 実行の観測値ではない。

- 原始状態では各拠点の二位置の量の和が1になる。共有位置は A が0、B が1なので、
  局所 Law の両成立と原始組立ての反証を同じ実行で確認できる。
- 各拠点で共有量を0に固定して `solve` し、異なる私有量を持つ二候補をそれぞれ `candidate` で選ぶ。
  `apply` の実出力を `assemble` の `local.a` と `local.b` へ渡す。
  私有量が両方0の組と両方1の組が成立し、B の共有量だけ1に修復した別候補との組は反証される。
- `inclusions[].applied` から局所 apply、`fragment`、`map`、`restriction`、`generators`
  から包含と再制限を辿る。共有代表 ma の owner と右操作の始点は全体側で G と ma になる。
  全体の a を量0の Law で再判定すると、一方は成立し、他方は反証される。
- B の `apply` を A の指定に混ぜた問いと、A だけ選んで B を原始状態のまま読んだ問いも反証される。

このディレクトリで実行する。

```sh
set --
while IFS= read -r ask; do
  set -- "$@" --ask "$ask"
done < queries.txt
archsig run --atom-definition definitions.json --law laws.law --archmap archmap.json --out out "$@"
```

意図した反証を含む完了結果の終了コードは1。[期待出力](expected.json) は保存した全回答の状態と
二つの組立ての数量を投影したもの。統合テストは包含・再制限の端点、実 `apply` の参照、生成操作、
共有境界反例も照合する。元の二拠点 runtime や DB での受入はこの例の実行範囲外である。
