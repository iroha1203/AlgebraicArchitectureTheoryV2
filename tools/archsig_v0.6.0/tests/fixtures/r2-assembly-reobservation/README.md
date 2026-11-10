# 共有位置の追加観測と候補の継続

R2 P3 の二拠点の共有 alias と、遠隔側の欠測を保留する設計を縮約した仕様入力。
`before.json` では B の共有位置 `mb.quantity` を欠く。A 側の有限修復は候補を選べるが、
実 `apply` を渡した組立ては未決で、後続の全体 Law も未決になる。

`after.json` では同じ field 型に `observed-shared-quantity` が加わる。
native の `reevaluate_assembly` に、snapshot を区別した A/B/G と各私有・共有位置の対応を明示する。
現在の候補域へ戻した元 Assignment が残ること、現在の `apply`、組立て、全体の Law が成立することを確認する。
B の私有量の観測値も 0 から 1 に訂正した対照では、同じ Law の下で前回の Assignment は除外される。
現在の解から別候補を選び直し、その実状態で組立てと全体判定を行う。
A と B の対応を固定して操作 `left` と `right` を入れ替えると、owner の照合に失敗する。

リポジトリのルートで、現在の二入力と対応を使うテストを実行する。

```sh
cargo test --locked --manifest-path tools/archsig_v0.6.0/Cargo.toml -p archsig-computation \
  explicit_reobservation_matches_a_shared_slot_and_rechecks_an_actual_assignment
```

[期待する証拠](expected.json) は before/after と訂正の区別を示す。各 snapshot 単独の公開 CLI では、
`queries.txt` の `SNAP` を `before` または `after` に置き換え、対応する ArchMap と実行する。
snapshot 間の対応は Rust API へ明示し、CLI の `--reuse` は保存結果の通常の再検査に使う。

全体判定は選択した局所の私有量を読む。追加 Atom だけのケースでは `pick` を、
B の既存観測も訂正したケースでは現在の解から `replacement` を採用する。
同じ View が異なる共有対を返した場合や、適用を別の solve に付け替えた場合も検査する。
