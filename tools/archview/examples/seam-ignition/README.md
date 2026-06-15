# Seam Ignition — watch an H¹ obstruction be born

ArchView の旗艦機能のデモ。**測定されたフレーム列を再生し、H¹ gluing obstruction が
生まれる正確なフレームを見る。** 他のどのコード可視化ツール(call-graph / blame /
Sourcegraph / CodeScene / Structurizr)も「どのコミットでアーキテクチャが局所片から
貼り合わなくなったか」を答えられない ── obstruction class が無いから。ArchView は
ArchSig がそれを測定するので、測定の裏付けで言える。

## 何が起きるか

同一 cover `cover:order-inventory` 上の3フレーム。各フレームは独立した実 `archsig analyze` run:

| frame | ArchMap | 測定された結論 | 意味 |
| --- | --- | --- | --- |
| f0 · calm | `frame-00.archmap.json` | `NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` | 凪。loop は閉じる |
| **f1 · mismatch added** | `frame-01.archmap.json` | `MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` | **⚡ H¹ 発火**。`atom:left-bottom-cech-mismatch` が現れ、left↔bottom が貼り合わなくなる |
| f2 · healed | `frame-02.archmap.json` | `NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` | ✓ 治癒。mismatch atom が消え seam が閉じる |

フレーム間の差は **mismatch atom が1つ現れて消えるだけ**(同一 cover・同一 4 context)。
タイムラインを scrub すると、f1 で amber の cocycle seam が結晶の中で発火し、teal の
closure ring が開き、bloom が新生 supportEdge ただ一つに灯る。

## 忠実性

ArchView は新しい verdict を作らない。`ignite` / `heal` は**各フレームの emitted
`decisionBar.conclusion`(ArchSig が測定した measured_zero / measured_nonzero)を隣接
フレーム間で比較しているだけ**。フレーム間の補間値は描かない(各 tick は実測フレーム)。

## ビルドと実行

```bash
tools/archview/examples/seam-ignition/build-sequence.sh        # → .tmp/archview-seq
python3 -m http.server 8000 --directory .tmp/archview-seq
# → http://localhost:8000/archview.html  (▶ Play、または tick をクリックして scrub)
```

`archview-sequence.json` が viewer の隣にあると ArchView は自動でシーケンスモードに入る
(`schema: archview-sequence/v1`、`frames[].path` は各 packet ディレクトリへの相対パス)。
任意の単一 packet を読む通常モードには影響しない。

## 拡張

`frame-NN.archmap.json` を増やせば任意長のシーケンスにできる。実コミット列の ArchMap を
順に並べれば、実コードベースの「アーキテクチャが貼り合わなくなった瞬間」を再生できる。
`archsig pr-review` の base/head を2フレームとして並べれば PR 単位の発火も見られる。
