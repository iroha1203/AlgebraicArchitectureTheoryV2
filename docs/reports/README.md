# reports 読み方

`docs/reports/` は、実験・計測の**正本報告**を置くディレクトリである。
`docs/note/` が探索・考察のメモ帳であるのに対し、ここに置く報告は外部文書(論文・記事)から
引用されることを前提に、数値・結論・claim boundary・証拠の対応を凍結した記録として管理する。

## 文書類型の規律

- 1報告 = 1実験(または実験系列の1段)。マージ後はこのディレクトリのファイルが正本であり、
  GitHub Issue のコメントは起草時の一次記録として報告から参照する。
- 各報告は次の節を持つ。
  1. 実験概要 — 対象、実施日、実施主体・使用モデル、対応 Issue
  2. 結果 — 計測値と結論コード。証拠束のファイルと一致させる
  3. 実証したこと
  4. 実証していないこと — claim boundary。結論の近くに置き、対象実験が実際に要求した
     concrete condition だけを判定する。無制限 claim(現実コード全体、意味宇宙全体、未来予測)を
     残タスクとして持ち込まない
  5. 証拠束と再現手順
- マージ後の報告は凍結する。誤りが見つかった場合は本文を書き換えず、末尾に「訂正」節を追記する。
- 数値・結論コードは証拠束(または Issue 正本記録)と機械的に突き合わせられる形で書く。

## 引用の仕方

報告は「ファイルパス + commit hash」で引用する。証拠束の JSON artifact は canonical JSON digest
(キーを再帰的にソートした compact 直列化の sha256。ArchSig が `inputDigests` に記録する規約と同一)で
同定する。各系列ディレクトリの検証スクリプトで、報告・証拠束・digest の対応を機械検査できる。

## 報告一覧

- [train-ticket ドッグフーディング系列](train_ticket_dogfooding/README.md) —
  外部 OSS(FudanSELab/train-ticket)に対する ArchMap 供給〜ArchSig 診断の end-to-end 実験。
  試運転 / フルビルド / SAGA フル診断階段の3報告と証拠束。
- [archmap supply bench 系列](archmap_supply_bench/README.md) —
  ArchMap 供給の再現性・精度ベンチ(`docs/tool/archmap_supply_bench.md` が正本)。
  独立 run 対の分散付き実測と証拠束。
