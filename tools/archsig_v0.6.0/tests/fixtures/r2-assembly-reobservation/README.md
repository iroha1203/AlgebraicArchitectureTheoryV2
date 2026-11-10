# 共有位置の追加観測と候補の継続

R2 P3 の二拠点の共有 alias と、遠隔側の欠測を保留する設計を縮約した仕様入力。
`before.json` では B の共有位置 `mb.quantity` を欠く。A 側の有限修復は候補を選べるが、
実 `apply` を渡した組立ては未決で、後続の全体 Law も未決になる。

`after.json` では同じ field 型に `observed-shared-quantity` が加わる。
native の `reevaluate_assembly` に、snapshot を区別した A/B/G と各私有・共有位置の対応を明示する。
現在の候補域へ戻した元 Assignment が残ること、現在の `apply`、組立て、全体の Law が成立することを確認する。
保存入力を基準に A の私有量を 1 から 2、B の私有量を 0 から 1 に訂正した対照では、同じ Law の下で前回の Assignment は除外される。
現在の解から別候補を選び直し、その実状態で組立てと全体判定を行う。
期待出力の訂正ケースでは、現在側だけ `pick` を `replacement` に改名し、`apply` の参照も同じ名前に更新する。
A と B の対応を固定して共有個体 `ma` と `mb` の対応を入れ替えると、owner の照合に失敗する。

リポジトリのルートで、現在の二入力と対応を使うテストを実行する。

```sh
cargo test --locked --manifest-path tools/archsig_v0.6.0/Cargo.toml -p archsig-computation \
  explicit_reobservation_matches_a_shared_slot_and_rechecks_an_actual_assignment
```

[期待する証拠](expected.json) は before/after と訂正の区別を示す。各 snapshot 単独の公開 CLI では、
`queries.txt` の `SNAP` を `before` または `after` に置き換え、対応する ArchMap と実行する。
snapshot 間の対応は Rust API へ明示し、CLI の `--reuse` は保存結果の通常の再検査に使う。

全体判定は選択した局所の私有量を読む。上のコマンドで実行するテストでは、保存入力を変えた前後の対照で
B の私有量を 1 にして、前回の候補に異なる Bool 値を含める。現在側の個体を改名して
順序を変え、明示対応で同じ割当てが残ることを確認する。訂正の対照では A の原始私有量を
2、B を 0 にして、以前の割当ての除外と現在の候補の適用を確認する。
共有 View または owner が未観測の場合、実際の位置を現在の Atom に結ぶ。
