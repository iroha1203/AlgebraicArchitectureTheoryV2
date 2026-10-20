# ArchSig v0.6.0

共通の Atom 定義を参照する Law・ArchMap を検査し、観測環境の view の値と Law の
成立・反証・未決を、型と導出元を持つ結果として計算する Rust クレートである。
旧版 [`tools/archsig`](../archsig/) とは独立している。

## 現在の提供形態

| 入口 | 提供する操作 | 結果 |
| --- | --- | --- |
| CLI | `archsig check`、`archsig version` | 入力の静的検査、`result.json` と入力コピー、一行の receipt／版情報 |
| Rust API | 三入力の検査、観測環境の `evaluate(View,B)`・`check(Law,B)` | 型付きの値・回答・導出 DAG、理由と元入力への参照 |

**CLI の `run` は未提供で、`usage`（終了コード64）として拒否する。**
CLI の `check` は Law の成立を評価せず、`requests`・`answers`・`nodes` は空で返す。
Rust API の評価結果には CLI の出力配送・receipt・終了コード・`--reuse` の連携は含まれない。
[I/O 仕様](../../docs/tool/archsig_v0_6_0_io/README.md)は v0.6.0 全体の実装要件を定めており、
このクレートはその全体の適合版ではない。

## 現行 CLI で入力を検査する

通常利用の入口は [run 一回から回答を読む例](../../docs/tool/archsig_v0_6_0_io/validation.md#最小の一周)にある。
run は未提供のため、以下は現行 CLI で行える入力検査の例である。

リポジトリルートで実行する。Rust 2024 edition 対応のツールチェーンが必要であり、
`--offline` は依存 crate がローカルに取得済みであることを前提とする。

```bash
cargo build --offline --manifest-path tools/archsig_v0.6.0/Cargo.toml -j 1
export PATH="$PWD/tools/archsig_v0.6.0/target/debug:$PATH"
archsig version
```

共通定義・Law・ArchMap を一回の check で検査する。
`--out` には存在しないディレクトリを指定する（出力先が既に存在する場合は別の名前にする）。

```bash
archsig check --atom-definition tools/archsig_v0.6.0/tests/fixtures/reservations.atoms.json --law tools/archsig_v0.6.0/tests/fixtures/reservations.law --archmap tools/archsig_v0.6.0/tests/fixtures/reservations.archmap.json --out result-check
```

`status=complete`、終了コード0となる。結果は `result-check/result.json` に保存し、stdout には一行の receipt を出す。
結果の形式は `archsig.result/2`。定義のコピーは `inputs/definitions/0.json` に置き、
入力 ID `definition0` と JSON Pointer から元の定義位置を追える。

複数の定義ファイルは `--atom-definition` を指定順に繰り返す。
明示したファイルだけを読み込み、未使用の語彙・依存・import も検査して保持する。
ファイル操作と終了コードの詳細は [実行仕様 §§5–7](../../docs/tool/archsig_v0_6_0_io/execution.md#5-ファイル操作と出力)を参照する。

## Rust API で観測値を評価する

呼出し側の crate から、このディレクトリを `archsig` の path dependency として指定する。
次の例の実行時 cwd はリポジトリルートとする。三入力の byte 列を渡すと、入力検査と
要求解決を経て Counter の値と二つの Law を評価できる。

```rust
use archsig::observed::{
    control::{Control, Limits, Usage},
    evaluate_observed_bytes,
    input::InputSources,
};

fn main() -> std::io::Result<()> {
    let fixtures = std::path::Path::new("tools/archsig_v0.6.0/tests/fixtures");
    let sources = InputSources::from_bytes(
        vec![std::fs::read(fixtures.join("counter.atoms.json"))?],
        std::fs::read(fixtures.join("counter.law"))?,
        std::fs::read(fixtures.join("counter.archmap.json"))?,
    );
    let asks = [
        "n=evaluate(CountCheck.amount,s=@v/s)",
        "ok=check(CountCheck.nonnegative,s=@v/s)",
        "audit=check(CountAudit.bounded,s=@v/s)",
    ];
    // この小例は予算制限・取消通知を設定しない。
    let mut control = Control::new(Limits::default(), |_| Usage::default());
    let result = evaluate_observed_bytes(sources, &asks, &mut control)
        .expect("対応範囲内の Counter 例");
    println!("{}", result.wire().canonical());
    Ok(())
}
```

結果の `status` は `complete`、`n` の値は型 `Z`・payload `"2"`、`ok` と `audit` は
`established` となる。Bool=false の view も値が確定すれば `established`、同じ false を
要求する Law は `refuted` となる。`guard=false` の行は `not_applicable` として保持する。

入力検査と要求解決を分ける場合は [`prepare_observed`](src/observed/mod.rs) と
`evaluate_observed`、検査済み bundle を使う場合は `prepare_checked_observed` を使う。
view は全 parameter の束縛を必要とし、Law の未束縛 parameter は型の全域で検査する。
同じ batch の `$id.value`・`$id.evaluation.value` と公開成分射影を後続の束縛へ渡せる。
計算は依存順、回答は指定順に返し、循環は要求 ID と依存グラフを保持して拒否する。
`Control` は入力検査・要求解決・評価で共有し、呼出し側が予算と計測・取消通知を設定できる。

## 機能別の概要

| 機能 | 現在の計算・保持内容 | 参照先 |
| --- | --- | --- |
| 三入力の静的検査 | 定義の schema・namespace・依存 DAG、Law の構文・名前・型・依存型・構造再帰・純粋性、ArchMap の ID・binding・値・参照・所属・Map 全域性・補完の存在を検査する。原式・位置・meaning・語彙 manifest と digest を保持する | [定義](../../docs/tool/archsig_v0_6_0_io/definitions.md)、[Law](../../docs/tool/archsig_v0_6_0_io/law.md)、[ArchMap](../../docs/tool/archsig_v0_6_0_io/inputs.md) |
| 値と式 | Z/Q/Fp/Bool/Unit/Text、参照、Tuple/List/Set/Option、対応する data 値を読む。正確な数値演算、比較、論理、let/if/match、view 呼出し、有限木の構造再帰、内包、count/sum/in を評価する。List の順序・重複、Set の外延、none・空・零・欠測を区別する | [式](../../docs/tool/archsig_v0_6_0_io/law.md#4-式束縛純粋性)、[評価器](src/observed/evaluate.rs) |
| 量化と欠測 | 有限型・登録参照族・Map 全域、owner に依存する族を扱う。同じ欠測 slot を共有し、入力制約に整合する有限全補完の各問い全体から不変値・反例・補完対を判断する。欠測 subject を域から除かず、補完値を観測 Atom に追加しない | [量化・補完](src/observed/quantifier.rs)、[補完評価](src/observed/completion_evaluate.rs) |
| 数値全域と Term | Z/Q の全代入に対するアフィン等値を係数から判断し、同じ未知 h の h−h の相殺と別 slot を区別する。既知 Map/Term の適用、有限域・アフィン Term の外延等値、Engine の生成 IR と保存判定を扱う | [数値全域](src/observed/universal.rs)、[Term](src/observed/term.rs)、[Engine 例](tests/observed_engine.rs) |
| 式内の Path | entity の恒等、内部 arrow／correspondence の path、端点、生成元列、共通 carrier 上の全作用と then 合成を扱う。等値は端点と全作用から判断し、名前・順序・reading は由来として保つ。計算値を原始 Atom や保存済み Operation へ昇格しない | [Path](src/observed/path_value.rs)、[Path 評価](src/observed/path_evaluate.rs) |
| 回答・導出・依存 | 型付き値、各原式の出現、束縛、Law instance、支持・Scope、数値残差・反証を導出 DAG に保持する。元入力・実 producer から再検査し、射影や所属の不適合は `condition_failed`、後続停止は `dependency_blocked` と元理由を保持する。中断時も検査済みの確定値・反例を残す | [結果仕様](../../docs/tool/archsig_v0_6_0_io/results.md)、[内部結果](src/observed/result.rs) |

## 未決・算法非対応・未実装

| 状態 | 扱い |
| --- | --- |
| 観測が足りず結果が決まらない | `undetermined` と `missing_observation`。元 slot と理由を保持する。全補完で不変の値は欠測があっても確定できる |
| 受け付けた問いに必要な算法が対応範囲外 | `undetermined` と `unsupported_algorithm`。元式・型・量化域・必要な判定を保持する。一般の無限非線形判定、未提供の存在量化判定、非数値無限域の判定などが該当する |
| 評価経路が未実装 | `EvaluationFailure::NotImplemented`。宣言・位置・機能名を返し、`wire()` は `None`。数学的な未決や `unsupported_algorithm` へ変換しない |
| 内部 API の対象外の問い・環境 | 要求解決の `ResolveFailure::NotApplicable`。この観測評価 API は `on` を省略した `evaluate`／`check` を対象とする |
| 入力や要求の不正／未知版／予算・取消 | それぞれ `invalid`／`unsupported`／`interrupted`。Law の反証や算法非対応と区別する |

評価の未実装経路には、対応する値型以外の payload を持つ data、上記の計算で扱わない式形、
補完後も確定しない参照からの field 読取り、対応範囲外の未観測 owner 所属・動的 owner 制約がある。
受理する構文・型の範囲と、実際に値を評価できる範囲は異なる。
また、`build` の ObjectAlgebra・equation realization、局所・大域診断、solve/repair 等の
完成出力と公開 CLI 接続は未提供である。式内 Path の計算とは区別する。

## テスト

クレート内の小さい試験を exact 名で一件ずつ実行する。CLI の静的検査と
上の Rust API 例に対応する試験は次のとおり。

```bash
cargo test --offline --manifest-path tools/archsig_v0.6.0/Cargo.toml -j 1 --test cli normative_examples_complete_both_checks -- --exact --test-threads=1
cargo test --offline --manifest-path tools/archsig_v0.6.0/Cargo.toml -j 1 --test observed_counter_evaluation counter_two_has_typed_ordered_complete_answers -- --exact --test-threads=1
```

他の試験は `--test TARGET NAME -- --exact --test-threads=1` で対象を指定する。
`tests/fixtures/` の規範例は [適合例](../../docs/tool/archsig_v0_6_0_io/validation.md)の
`examples/` と同じ byte 列を保持し、テスト入力はクレート内の fixture を使う。
全 suite の成否と、選択した試験の成否は区別する。
