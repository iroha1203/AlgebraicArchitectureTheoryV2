# R2 の正確な Backing 制約

R2 の `experiment/p1-integration/model-v0.2` から Pool 0.3 の定義、`Backing` reading、
`fixture` snapshot の4世界に属する80 subject と436 Atom を取り出した。各世界の ID、owner、参照、
Atom 値、Law 本体を保持し、由来を `specification` とした。元記録の
`compute-01/ordinary-relations.json` にある `general_exact_flows` は、同じ4世界の容量と請求量を
別の exact flow で読んだ結果である。

| 世界 | 元記録の不足 | ArchSig の全解 |
| --- | --- | --- |
| overlapFeasible | 0 | 一意。B1/Y と B2/X に各 5 |
| overlapInsufficient | 5 | 空 |
| threeUsesExact | 0 | 一意。M1、Sale、Transfer、M2 に順に 1/4、1/8、3/16、7/16 |
| threeUsesMicroShortage | 1/100000 | 空 |

このディレクトリで1世界ずつ実行する。各世界を切り出しても、同じ owner の全個体と参照先を保持する。

```sh
while IFS= read -r ask; do
  world=${ask%%=*}
  jq --arg world "$world" '
    def in_world: split(".")[0] == $world;
    .snapshots[] |= (
      .subjects |= map(select(.id | in_world)) |
      .atoms |= map(select(.subject | in_world))
    )
  ' archmap.json > "out-${world}.archmap.json"
  status=0
  archsig run --atom-definition definitions.json --law laws.law \
    --archmap "out-${world}.archmap.json" --out "out-${world}" --ask "$ask" || status=$?
  case "$status" in 0|1) ;; *) exit "$status" ;; esac
done < queries.txt
```

保存結果では `answers[].outputs.solutions` の `representation.certificate` から空または一意の
証拠を辿れる。座標を個体に戻すには同じ回答の `outputs.domain` にある `instances[].positions` を使う。
統合テストはこの4世界の ArchSig 実行、分数座標、保存結果の再照合を検査する。実行範囲は
この仕様入力と欠測・余剰容量の対照で、元の全 reading を含む実験や稼働 DB の再実行は含まない。
