# Lean ビルド性能と高速化

大規模 Lean 形式化では、elaboration 負荷・カーネルの `isDefEq` 滞留・heartbeat 引き上げ・広すぎる import が積み重なると CI が終わらなくなる。Phase 1 の全体スケルトン設計から Phase 2 の各 PR まで、次を基準に性能を守る。

## 基準

- **`elaboration` と `type checking`（カーネル）の両方を見る**: `maxHeartbeats` に引っかからなくても、カーネルの `isDefEq` 展開だけで 1 ファイル数分かかることがある。`-Dprofiler=true` で `type checking` 時間も確認する。
- **`maxHeartbeats` / `maxRecDepth`**: 既定値（`200000`）で通すのを原則とする。引き上げで逃げず、プロファイルで原因を潰す。どうしても残る宣言は最小件数に留め、直前に理由コメントを書き、PR 本文に一覧で載せる。`maxRecDepth` 引き上げや大幅な超過を構造改善で解消できない場合は `性能予算超過` として止めて報告する。
- **import 最小化とキャッシュ保護**: 広域 import（`import Mathlib` 等）を避け、必要な葉モジュールだけ import する。多くの上流依存が集まる土台ファイルは import を最小にして変更頻度を抑え、CI の差分ビルドキャッシュを壊さない。

## 重いときの直し方

- **カーネル `isDefEq` が巨大定義を展開してしまう（`type checking` が重いとき）**:
  - 具体的な重い構造（`GlueData` / `Limits.colimit` / テンソル積上の `ModuleCat` 等）の上で `change` や圏論図式を直接証明せず、一般の環・スキーム・対象に抽象化した補題（抽象コア）で証明してから具体構造へ適用する。
  - 自由変数と非 `rfl` 等式を残したまま高階構成を展開させず、証明冒頭で `subst` して `rfl` 上に落としてから書き換える。
  - 証明項だけが異なる依存引数（`f h` vs `f h.symm.symm` 等）をカーネルの暗黙照合に任せず、`Subsingleton.elim` + `congrArg` で明示的に橋渡しする。
- **`simp` / `aesop` が重い**: `simp?` で最小集合を拾って `simp only [...]` に固定する。等式変形は `rw [...]` や `calc` に落とす。
- **定義の展開・長い証明が重い**: 公開 `def` / `structure` に `@[simps]`・`ext`・計算補題を揃え、下流で `unfold` / `dsimp [Def]` を繰り返さない。必要に応じて `structure` 包装や `@[irreducible]` で展開を抑える。長い証明の途中ステップは `private lemma` へ切り出し、値の中身が不要な中間事実は `let` ではなく `have` を使う。
- **型クラス探索（`synthInstance`）が詰まる**: `letI` / `haveI` のスコープを最小に閉じ、遅い呼び出しに型注釈や `@foo ...` の明示引数を与える。既存インスタンスと競合するローカル instance を避ける。
- **具体例・反例と並列性**: `NormNum` 等の計算を伴う具体例・反例は本体モジュールと別ファイルに分け、共通の薄い定義から横に広がる依存構成を保つ。

## 計測・プロファイル

PR 前に変更・新規ファイルで確認し、重いファイルの計測結果とオプション指定件数を PR 本文に載せる。ファイルを編集せず CLI フラグでプロファイルすると、オプションの消し忘れを防げる。

```bash
# 単一ファイルの時間・elaboration / type checking 内訳
/usr/bin/time -p lake env lean -Dprofiler=true -Dprofiler.threshold=500 <target-file>

# 型クラス探索の詰まりを調べる場合
lake env lean -Dtrace.profiler=true -Dtrace.Meta.synthInstance=true <target-file>

# オプション残存・広域 import 確認（profiler / trace.* はコミット前に必ず 0 件）
rg -n "set_option\s+(maxHeartbeats|maxRecDepth|synthInstance|profiler|trace\.)" <changed-files>
rg -n "^import\s+Mathlib(\s|$)" <changed-files>
```

## 節目の振り返り

章・部の切れ目や直近 CI の所要時間が目立って増えたタイミングで、CI 実行時間の推移・`maxHeartbeats` / `maxRecDepth` 件数・最も重いファイル群・キャッシュの効き方を確認し、CI 完走を脅かす傾向があれば新機能追加より先に性能改善または `性能予算超過` 停止を選ぶ。
