# archmap supply bench 系列

ArchMap 供給(archmap-creater SKILL による LLM 抽出)の再現性・精度を、
供給ベンチ正本(`docs/tool/archmap_supply_bench.md`)のプロトコルで実測した
報告の系列。指標定義・比較系列 key・claim boundary は正本を参照。

## 報告一覧

- [第1報: 規約 v2 の再現性・精度ベースライン](first_bench.md) — 2026-07-21、
  独立 3 run 対(6 run、読者 Sonnet)、tuned / prompt-literal-disjoint 分離。
  証拠束は `evidence/run1/`

## 再現手順

決定論部分(計量)— 証拠束から数値を再計算して報告と突き合わせる:

```bash
W=docs/reports/archmap_supply_bench/evidence/run1
REF=tools/archsig/tests/fixtures/supply_bench/reference_v1
for c in chunk-04 chunk-13 chunk-01; do
  CLASS=$([ $c = chunk-01 ] && echo prompt-literal-disjoint || echo tuned)
  cargo run --manifest-path tools/archsig/Cargo.toml -- supply-bench \
    --pair pair-1-$c=$W/consistency/pair-1-$c.json --alignment pair-1-$c=$W/alignment/pair-1-$c.json \
    --pair pair-2-$c=$W/consistency/pair-2-$c.json --alignment pair-2-$c=$W/alignment/pair-2-$c.json \
    --pair pair-3-$c=$W/consistency/pair-3-$c.json --alignment pair-3-$c=$W/alignment/pair-3-$c.json \
    --chunk-class pair-1-$c=$CLASS --chunk-class pair-2-$c=$CLASS --chunk-class pair-3-$c=$CLASS \
    --reference $REF/reference-$c.json --series-key $W/series-key.json \
    --id supply-bench:train-ticket-$c-v1 --out /tmp/supply-bench-$c.json
  diff /tmp/supply-bench-$c.json $W/out/supply-bench-$c.json && echo "$c: byte-identical"
done
```

corpus の取得(供給部分の再実行に必要):

```bash
git clone https://github.com/FudanSELab/train-ticket && cd train-ticket \
  && git checkout 313886e99befb94be6cd45f085c98e0019f59829
# 上流が消滅している場合:
git clone docs/reports/archmap_supply_bench/evidence/run1/train-ticket-313886e9.bundle train-ticket
# いずれの経路でも、対象60ファイルの sha256 を corpus fixture と突き合わせる:
# tools/archsig/tests/fixtures/supply_bench/corpus_v1.json の contentHash
```

供給部分(抽出・調停・alignment)の再実行は `evidence/run1/` の3指示書と
`series-key.json` に従う。得られる値は比較系列 key(モデル snapshot・調停者)に
相対する(正本の反証可能性の成立範囲を参照)。

## 証拠の同定

JSON artifact は canonical JSON digest(キーを再帰ソートした compact 直列化の
sha256)で同定する。全 artifact の digest は `evidence/run1/digests.json`。
