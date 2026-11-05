# cache分岐とcallback後の読取り

架空の要求を先に固定する: cache hitならenterを呼ばず、hitでもvisitを呼ぶ。
visitが変更する同じchildのvalueを、visit後に読み戻り値にする。
例のcallbackは正常終了し、enterはnodeをそのまま返し、visitはchild.valueへ1を代入する。
cacheは同じnodeへの参照を保持する。実OSSの観測や実行の実測ではない。

以下は条件付き経路を読むための擬似コード。先読み案と後読み案を比較する。
番号は選択経路での作用の順序であり、ソース行番号や実測時刻ではない。

```text
if cacheHit:
    child = cache[key]       # enterを迂回。ここで操作全体はreturnしない
else:
    child = enter(node)     # この例ではnodeと同じ参照

先読み案:                  後読み案:
  saved = child.value [1]     visit(child)       [2]
  visit(child)        [2]     return child.value [3]
  return saved
```

先読み案のreturnは保存済み整数を返すので、child.valueの読取位置は[1]。
visit呼出しとその内部の代入、後続の読取が同じchildを指すことを対応づける。
整数の値がたまたま一致する入力でも、要求された読取順序の確認にはならない。
この例の順序Lawは固定callbackと同一参照の前提で使う。参照が変わる操作や例外経路では
その前提と経路を読み直し、三入力にも必要な区別を残す。

[Atom定義](callback.atoms.json)・[Law](callback.law)・[ArchMap](callback.archmap.json)は
先読みhit、後読みhit、後読みmissの三経路を保持する。
`hitPartial`は後読みhitからenter到達性だけを意図的に欠測にした比較入力。
既知の未到達は`enterReached=false`、未観測はそのAtomの欠測であり別の値である。
cache hitという条件だけを見て、未読の実装のenter到達性をfalseで埋めない。

SKILL冒頭の`cli`・`skill`・`work`を設定し、新しい出力先で実行する。

```sh
"$cli" run --atom-definition "$skill/assets/callback.atoms.json" \
  --law "$skill/assets/callback.law" --archmap "$skill/assets/callback.archmap.json" \
  --ask 'staleEnter=check(Callbacks.skipEnter,bind.b=@v/hitStale)' \
  --ask 'staleVisit=check(Callbacks.visitHit,bind.b=@v/hitStale)' \
  --ask 'staleRead=check(Callbacks.readAfterVisit,bind.b=@v/hitStale)' \
  --ask 'freshEnter=check(Callbacks.skipEnter,bind.b=@v/hitFresh)' \
  --ask 'freshVisit=check(Callbacks.visitHit,bind.b=@v/hitFresh)' \
  --ask 'freshRead=check(Callbacks.readAfterVisit,bind.b=@v/hitFresh)' \
  --ask 'missRead=check(Callbacks.readAfterVisit,bind.b=@v/missFresh)' \
  --ask 'partialEnter=check(Callbacks.skipEnter,bind.b=@v/hitPartial)' \
  --out "$work/callback-run"
```

`staleRead`は2<1を反証し、`freshRead`と`missRead`は2<3で成立する。
`staleEnter`・`staleVisit`・`freshEnter`・`freshVisit`は成立。
`partialEnter`はenterReachedの欠測で未決となり、batchは`partial`・終了コード2となる。
summaryだけでなく保存resultの
反例・欠測理由と元Atomを照合する。到達性の要求が成立しても読取順序の要求は別に検査する。

enterの誤観測を訂正するときは、そのAtomだけを置換して終えない。この例ならcache分岐の
出口、hit後のvisit、child参照の共有、visit内の代入、戻す値の読取位置を再読する。
同じ根拠を使う両案・hit/missの関連AtomとLawが読む値を照合し、旧入力・訂正内容・再計算結果を分けて残す。

この例では冒頭の要求から三つのLawを選んだ。既存Lawに読取順序がなければ、その成立から
順序要求への適合を結論しない。結果を見た後で不足するLawを追加する場合は要求根拠を示し、
元Lawでの結果と追加後の結果を区別する。後から追加したLawによる反証は事後検証であり、
実装前の発見や事前の候補選択の根拠として遡って数えない。
