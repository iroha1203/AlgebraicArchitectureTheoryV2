# 描画条件と表示の検証

左右の画面外内容を示す機能について、方向条件を読む小さな候補例を使う。
以下は架空の Python ソースで、実 UI フレームワークの観測や画面の実測とは分ける。
`render` が呼ばれたときに返すセルを `(記号, 前景, 背景)` とする。
`surface` は合成済みの背景、`None` は背景指定なしを表す。
幅は2以上、`0 <= offset <= limit`、`displayed` は表示対象の有無とする。

```python
class Kept:
    def directions(self, offset, limit, width, displayed):
        return (displayed and width > 0 and offset > 0,
                displayed and width > 0 and offset < limit)

    def background(self, surface):
        return surface

    def render(self, offset, limit, width, displayed, foreground, surface):
        left, right = self.directions(offset, limit, width, displayed)
        background = self.background(surface)
        return (('◀' if left else ' ', foreground, background),
                ('▶' if right else ' ', foreground, background))

    def clear(self, state, redraw):
        state['displayed'] = False
        redraw()

class Dropped(Kept):
    def background(self, surface):
        return None

class Deferred(Kept):
    def clear(self, state, redraw):
        state['displayed'] = False
```

例の要求として「render が呼ばれたとき、左右の記号条件が表示対象と幾何条件に一致する」を採用する。
狭い Law は `directions = (displayed and width > 0 and offset > 0,
displayed and width > 0 and offset < limit)` という関係である。
三候補とも同じメソッドを継承するので、この関係は成立する。ここで選んだ要求と式の対応を、
利用者の「知覚できる表示」という目的全体へ広げない。

有限族 S は三候補を同じ引数 `offset=1, limit=2, width=4, displayed=True` で読む3要素。
q は `directions` の値であり、全要素で `(True, True)`。
v の最初の列 `directions` も同じ呼出しの方向値を読む view とする。
これは関係の成立 Bool と、関係の左右に現れる値を区別した上で、方向値だけの保存を問う例である。

| 候補 | directions | background(surface) | clear 内の作用の順序 |
| --- | --- | --- | --- |
| Kept | `(True, True)` | `surface` | displayedをFalseへ更新 → redrawを呼ぶ |
| Dropped | `(True, True)` | `None` | displayedをFalseへ更新 → redrawを呼ぶ |
| Deferred | `(True, True)` | `surface` | displayedをFalseへ更新 |

追加の二列は、上のソースの背景引数の受渡しとclear内の呼出し順序を読む view。
`background` の比較は `surface` に非Noneの同じ値を渡す条件で行う。
`clear` の比較は正常に状態更新できる辞書を前提とする。このメソッド内にある呼出しを読み、
redrawの成功・描画完了・他の通知経路の存在は読み込まない。
この二列を要求として採用するかは別の判断であり、全UIに同じ実装手段を義務化しない。

## 有限表を実行する

`cli`、`skill` は [SKILL](../SKILL.md) のバンドル指定を使う。
二つの同梱表は、上のソースと代入から手で読んだ値を、等号を保つtokenへ対応づけている。
`TT` は方向tuple、`surface` / `none` は背景引数、
`set-false,redraw` / `set-false` はclear内の順序付き作用を表す。
未測定の表示品質を合格・不合格tokenとして入力しない。

```sh
"$cli" law-fibers --table "$skill/assets/rendering-directions.json"
"$cli" law-fibers --table "$skill/assets/rendering-actions.json"
```

最初は十分で終了0。qとvが同じ方向値なので、この表の成立は構成上自明である。
二つ目は同じSとqに背景・clear作用のviewを追加し、終了1で3対すべての反例を返す。
Kept/Droppedは背景、Kept/Deferredはclear作用、Dropped/Deferredは両方が異なる。
`laws` という表の欄にview名を置いており、各列の値の保存を調べる。
追加列の違いを狭い方向Lawの反証や、実際の画面品質の不合格へ読み替えない。
この補助計算は与えた表の全対を比較する。Pythonの実行や意味抽出は行わず、
三入力のcheck/runを代替しない。実ソースを三入力へ写す際は、継承元・呼出し先・適用条件まで
根拠を照合する。背景やclear作用も問いに含めるなら、その原始事実と読取りを追加する。

## 実装と画面を確かめる

この例から確認できるのは、同じ方向条件と文字列でも背景指定が異なり、
clearの状態更新後にこの経路から再描画を要求するかも異なること。
背景指定なしの見え方は合成処理と端末の既定背景に依存する。
再描画要求の有無も、実際の描画到達・完了とは分ける。

| 受け入れたい内容 | 独立に確認する証拠の例 |
| --- | --- |
| 記号セルが意図した背景を保持する | 元セルと置換セルの合成styleを比較する回帰検査、明色・暗色テーマの合成画面を保存して目視確認 |
| 空状態へ更新した後に記号が消える | overflow → 選択解除 → clearの系列を実行し、対象状態と描画の完了を待って合成画面を確認 |
| 利用環境で記号を読める・操作できる | 採用する端末・フォント・focus状態で画面と操作を確認。必要なアクセシビリティ条件は別に合意して検証 |

文字列に記号が含まれる検査だけでは背景情報を読めない。画面検証にも対象テーマや状態があり、
一枚の画像で全環境を確認済みにしない。待機は対象の更新・描画完了へ結び付ける。
これらの実行時証拠は実装観測Atomと分けて報告する。
方向だけを読む式には背景や再描画の欠測slotが存在しないため、
`needed` に不足がなくても、この独立検証が完了したことにはならない。
