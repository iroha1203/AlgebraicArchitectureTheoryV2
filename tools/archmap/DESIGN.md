# ArchMap CLI分離の裁定

## CLI入口

観測側のauthoring / supply benchは、新しい `archmap` binaryへ移設する。
`archsig archmap`、`archsig scope-manifest`、`archsig extraction-diff`、
`archsig supply-bench` の互換subcommandは残さない。

理由は、これらがArchMap観測の準備・比較・計測を行う入口であり、ArchSigの
ArchMap + LawPolicyからの計算入口ではないためである。旧入口を残すと、責務の
帰属とCLIのsource of truthが二重化する。移設後の挙動は、同じ実装・schema・
fixture・testを `tools/archmap` から実行することで維持する。

## 依存方向

`archmap`はArchMapのschema型とArchSigが提供するArchMap validatorを利用する。
ArchSigはarchmapのauthoring / supply実装へ依存しないため、計算crateから観測側
パイプラインへの逆依存は発生しない。
