# R2 E12 の共通消費操作を読む

R2 の `experiment/p2-migration/e12-comparison-v1/MANUAL-CORRESPONDENCE.md` の
Consume first と、`e12-execution-v1/COMPARISON-v1.json` の after_consume を根拠にした仕様入力。
native の `complete_allocations` と P2 の `consume` が対応するのは、output1 の live allocation に
対して、期待 snapshot が一致し、要求量が現存 allocation と物理 stock の両方の範囲内にある場合。
T3 の 1 と N の 0.06250 を、1/16 を単位とした整数の 16 と 1 で読む。前状態の 0 はこの操作による
新規消費分の原点である。N の output1 は選んだ操作の宛先であり、原 native の非追跡 stock が
過去の出力帰属を永続化したという主張には用いない。

## 構成と作用

- `comparison` は二つの読取りを同居させた比較 snapshot。始域の全体 root は `native-output1`、
  終域の全体 root は `rust-output1`。それぞれ T3 と N の局所 root を持つ。
- 各局所 root が owner である before/after state と consume arrow を与える。各側の T3/N の
  before state は、選んだ二成分の共通の開始位置として明示的に貼り合わせる。各 consume は
  この開始位置から別の after state へ進む。二つの成分に順序や可換性を課していない。
- `move-T3` と `move-N` が、native から Rust の同じ source の局所 root、前後 state、consume
  arrow をそれぞれ対応させる。全体の作用表は CLI が構成する。
- 保存結果の `move.outputs.map` から `locals` の correspondence と両 root、`generators` の両 Operation
  と保存 Proposition、`configuration_map.candidate.action` の像を確認できる。T3/N の量は
  `move.map.target` を使った別の問いで読む。[期待出力](expected.json) はその部分の投影で、
  統合テストが保存結果から同じ投影を作って照合する。

このディレクトリで実行する。

```sh
set --
while IFS= read -r ask; do
  set -- "$@" --ask "$ask"
done < queries.txt
archsig run --atom-definition definitions.json --law laws.law --archmap archmap.json --out out "$@"
```

`rust-N-consume.to` が存在しない個体を指す場合は、問いの前に ArchMap の元位置を伴う `reference` で拒否される。
同じ比較 snapshot における同じ型・field 位置の読取りを `assemble_map` の適用域とした。
この入力の result/4 は約12 MB で、ここには検査対象の結果部分を保存した。

操作保存の反例を再現するには、`rust-N-consume.to` を同じ owner の登録済み `rust-N-before` に
変更して最初の3問を実行する。両 assembly は成立し、`move` は `condition_failed` と保存反例を返す。
このとき後続の `$move.map.target` は利用できない。後続を含む5問で既存の依存解決が内部障害になる
問題は、親 #6292 の [#6317](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6317)
で追跡する。

## 原記録に残る境界

- P2 の complete-first は明示 consume 後、output1 の live binding 残量が零で再消費しない条件を持つ。
  raw native cancel `(remove_allocated_stock=false, remove_incomplete_outputs=false)` 後の output2
  は `is_building=true, status=10`、P2 の固定 cancel 後は `is_building=false, status=65`。
  未使用権の解放と既使用・良品の保持を共通部分として読む。今回の操作生成元は選んだ consume だけ。
- P3 の rich CLI の9問は Carry の原始 subject/Map を束縛していない。
  `experiment/coordinator/p3-rq-probe-v1/run-01/RESULT.json` の6局所組は、global dictionary key
  をそのまま参照 ID と読むと各32欄が未解決になる。種類別の件数は resource 12、plan 10、
  grant 4、line 4、claim 1、output 1。site/owner と参照先を明示できるまで、この読取りは入力の
  不備として保留する。P3 は元の実候補・全操作・二拠点受け入れが未完了。
- 局所修復の適合候補を再組立てに渡す接続は [#6303](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6303)、
  構造候補の選択は [#6304](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6304)、
  修復済み状態の移行と raw cancel の対照は [#6305](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6305)、
  別時点の観測・共有対象・候補の対応検証は [#6306](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6306)。
  いずれも親 [#6292](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6292) の後続課題である。
