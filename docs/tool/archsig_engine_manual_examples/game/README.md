# ゲーム操作の分類と記録形式

[利用手順](../../archsig_engine_manual.md) · [入力・出力の書式](../../archsig_engine_reference.md) · [検証資料](verification.md)

| ファイル | 内容 |
| --- | --- |
| [game.py](game.py) | 一部屋のゲーム、入力の解釈、三つの記録候補、ホストへの登録 |
| [game.archmap.json](game.archmap.json) | 型・値・原始項と使用関係の完全な入力 |
| [game.law.json](game.law.json) | 役割の束縛、評価、記録に課す Law、問いの完全な入力 |
| [expected/result.json](expected/result.json) | 全状態・入力・同値類・作用表・候補の判定・反例 |
| [calculate.py](calculate.py) | 二入力から結果を生成する補助計算 |
| [verify.py](verify.py) | ソースとの照合、隔離再計算、ID 改名と入力変更の検査 |

## 再計算

このディレクトリで、未作成の出力先を指定する。

~~~sh
python3 calculate.py \
  --archmap game.archmap.json --law game.law.json \
  --out /tmp/archsig-game-result.json
~~~

calculate.py が読む意味上の入力は指定した二ファイルだけである。
ゲームのソースや expected/ を読み込まず、標準ライブラリで有限な項を評価する。
ArchSig エンジンの実装ではなく、入力と期待出力の関係を再現するための補助計算である。

~~~sh
python3 verify.py
~~~

verify.py は、補助計算と二入力だけを別ディレクトリに置いて再実行し、完全な期待出力と比較する。
その後、ソースコード・登録との照合、ID 改名、値の欠落、非対応の項、不正参照、原始式の変更を検査する。
検査用の変形はメモリ内で作り、入力や期待出力を書き換えない。

マニュアルにある製品 CLI の呼出形式は次のとおりである。

~~~sh
archsig engine run --archmap game.archmap.json --law game.law.json --out out/game
~~~

この例の実行検証には calculate.py と verify.py を使う。
前者は入力から期待出力を再計算し、後者はその結果と入力変更時の振る舞いを検査する。
製品 CLI の実行検証は、この二つの補助コマンドの検証には含まれない。

## 二入力の読み方

ArchMap の原始宣言は、entity と、その definition を持つ term からなる。
payload.term にレコードの構造、定数、関数の引数型と式を記録する。
使用関係は別の entity とし、slot、target、label を持たせる。

| 登録の用途 | slot の値 | target が指すもの |
| --- | --- | --- |
| 状態の有限域 | state-domain | 引数なしの列挙項 |
| 入力の有限域 | input-domain | 引数なしの列挙項 |
| 一手の処理 | turn | 状態と入力を受け取る項 |
| 比較するゲーム値 | state-reading | 状態の読取り項 |
| 記録候補 | recording | 入力を記録へ変換する項 |

これらの使用事実は、game.py の MODEL_PORTS と RECORDERS の登録を観測したものである。
登録の用途と参照を観測者が確認し、核はその用途から宣言を束縛する。
関数名から役割を推測したり、target が保存するという判定を入力したりしない。

Law の vocabulary は、上の事実を kind・axis・predicate で選ぶ。
bindings の G・U・P・V は各役割に一つ、E は recording の全対象を束縛する。
G などは Law 内の変数名であり、入力の subject ID ではない。
候補の label は出力を読むための名前で、判定条件に使わない。

評価は、各状態と入力について「一手を適用し、そのゲーム値を読む」と明記する。

~~~json
{
  "invoke": "V",
  "arguments": [
    {
      "invoke": "P",
      "arguments": [
        {"variable": "state"},
        {"variable": "input"}
      ]
    }
  ]
}
~~~

記録に課す Law は、次の宣言である。

~~~json
{
  "portable_recording": {
    "operator": "factors_action",
    "action": "operations",
    "quantification": "all_finite_states_and_inputs"
  }
}
~~~

factors_action は「同じ記録値にまとめる入力は、全状態で同じ作用をする」という要求である。
これを各記録候補について検査する。状態数、操作の分類、十分な候補の名前は宣言に含めない。

JSON は Law DSL の宣言木を表す。
finite_terms/1 と finite_action/1 の意味、項の構文、判定は
[書式リファレンス](../../archsig_engine_reference.md#有限作用を扱う-law)で固定する。

## 結果の読み方

| query | 主な欄 |
| --- | --- |
| operations | bindings：解決した役割、states・inputs：生成した全要素、classes：同値類、action：代表によらない作用表 |
| recordings | candidates：各候補の status、fiberCount、realizesCanonicalResolution、counterexample、classEncodings |
| order | pairs：異なる操作クラスの組、順序交換の可否、反例 |

この例の operations は、58状態・192入力から7類と406行の作用表を返す。
各クラスの members は元の入力に戻り、action の state・nextState は状態に戻る。
クラス ID は表示用であり、その番号自体を操作の意味としない。

recordings の query が established でも、全候補の保存成立を意味しない。
これは候補の分類計算が完了したことを表す。採用する候補自身の status を読む。

| label | 保存 | 標準解像度との一致 |
| --- | --- | --- |
| keys | refuted | 不十分 |
| commands | refuted | 不十分 |
| events | established | 完全一致 |

十分な候補が不要な区別を残す場合には、status は established でも
realizesCanonicalResolution は false になる。
例えば原始の攻撃式から乱数への依存を除くと、作用は6類になり、commands が完全一致する。
events も保存はするが、使われなくなった乱数結果を余分に記録する。

反例の state・inputs・nextStates と、同じ記録値 sameEncoding を読むことで、
何を一緒にしてはいけないかを確認できる。evidence.atomIds から原始項・使用事実、
sourceRefs からソースの版と行範囲へ戻れる。
evidence.lawDecls は Law JSON の pointer、builtinRules は版付きの計算規則である。

## 有限モデルの範囲

盤面は中央が壁の8マス、敵は (2,2)、双方の体力は0・1・2である。
admissible が認める割当ては58通りであり、単一の初期状態からの到達集合ではない。
入力はキー6種、カメラ4方向、色2種、アニメーション2段階、乱数結果2種の直積である。

乱数生成器の seed・内部状態・消費順序はこの入力に含めていない。
記録するのは攻撃に実際に使う論理的な乱数結果である。
作用の一致は、この状態域・入力域・Law・固定した項の意味に対して成り立つ。
