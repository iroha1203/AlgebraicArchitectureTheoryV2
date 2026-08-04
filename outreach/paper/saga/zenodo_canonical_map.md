# Canonical 対応表(内部監査用)

paper(英語正本+日本語正本)とリポジトリ内 canonical 数学本文(日本語)の対応を
執筆・監査時に検証するための内部資料。読者は本表を必要としない(論文は self-contained)。
claim-to-evidence matrix(`zenodo_claim_evidence_matrix.md`)の A 層の検証正本。
旧草稿管理付録C(release 時に草稿から除去、2026-07-26)を独立ファイル化した。

基礎定義(第3章):

| paper | canonical | 内容 |
| --- | --- | --- |
| 定義 3.1 | 第I部 定義 1.1 | Atom |
| 定義 3.2 | 第I部 定義 3.1、3.2 | Atom family、support |
| 定義 3.3 | 第I部 定義 4.1、5.1、命題 5.3 | configuration、architecture object、Atom-origin |
| 定義 3.4 | 第II部 定義 3.1 | architecture context |
| 定義 3.5 | 第II部 定義 4.1、仮定 4.3、命題 4.2 | context category、overlap、finite-meet poset model |
| 定義 3.6 | 第I部 定義 7.1〜7.3 | equation system、fulfillment |
| 定義 3.7 | 第II部 定義 6.1、7.1、8.1 | coverage、AAT topology、AAT site |
| 定義 3.8 | 第II部 定義 9.1、10.1 | presheaf、sheaf condition |
| 定義 3.9 | 第III部 定義 5.2、6.1、6.2 | witness ideal、obstruction ideal |
| 定理 3.10 | 第III部 定義 11.3、定理 11.4 | displayed source、generated `Q_E` |

注: 論文 定理 3.10 条項5(旧条項4、2026-07-26 #3813 の residual restriction
naturality 条項挿入で繰り下げ)の名称は quotient zero criterion(#3781 項目8で
改名)。canonical 定理 11.4 の対応 clause は faithfulness / nondegeneracy の
ままであり、canonical 側は追随改名しない(2026-07-24 裁定)。名称の相違は
この注記が恒久的に対応づける。条項3(residual restriction naturality)は
canonical 定理 11.4 の同名条項に対応する(2026-07-26 #3813 で追補)。

構成と定理(第4〜5章):

| paper | canonical(第X部) | 内容 |
| --- | --- | --- |
| §4.1 | 定義 2.1、補題 2.2、定義 2.3、補題 2.1A | cover-relative Čech complex |
| §4.2 | 定義 3.1〜3.4、定義 4.1、4.2、補題 4.3、定理 4.4、系 4.5 | semantic 側の構成 |
| §4.3 | 定義 5.1〜5.3、補題 5.4 | equation 側の構成 |
| 命題 4.1(§4.3) | 定義 6.1、命題 6.1A | equation semantic realization(`χ^E` の構成) |
| 定理 5.1 | 定理 1.1 | SAGA 中心定理 |
| §5.3 | 補題 6.2A、定理 6.3、系 6.7、例 6.6 | 係数同型 `Φ` |
| §5.4 | 定義 7.1、定理 7.2、系 7.3、定理 7.4 | cochain 可換と `H¹` 同型 |
| §5.5 | 定理 7.5、定理 7.6 | residual 対応と統合 |
| 定理 5.2(§5.6) | 定義 8.1、系 4.5、補題 2.1A、定理 8.2、系 8.3 | Grounded Global Gluing |
| 補題 5.2A(§5.6) | 補題 2.1A(matching family clause のみ) | ordered matching completion |
| §5.7 | 原則 8.4 | additive/torsor/higher の分離 |
| 例 5.3(§5.8) | 例 10.2 | 非零類の有限 witness |

注: 論文 §5.6 の true semantic repair sheaf 定義は canonical 定義 8.1 と同一の
4条件である(2026-07-26 の記述整合対応 #3814 で、canonical に対応物のない
旧条件(5)と `P_sem^𝒰` 定義域分離を除去して統一)。Lean 側は担体
(`AffineSemanticRepairSystem.State`)が最初から site 全域である一方、torsor
三条件は `IsIntersectionCtx` ガードにより cover intersection 上でのみ仮定される。
`P_E` 側も同構造(`AffineCoefficientLiftSystem`、作用は intersection 上)。
仮定 7 の `β` の Lean 対応物は intersection diagram 上の成分と base 水準の
`betaW`(chart 整合仮説つき)に分かれる。

注: 論文 §4.2 の projection `π_V:Λ(V)→At` は、canonical 定義 3.1 の
occurrence 値 projection `π_V:Λ(V)→At(V)` を台 Atom へ圧縮した形である
(2026-07-26 #3813)。Lean は occurrence 水準を保持する
(`SemanticAtomData.projection` / `projection_natural` +
`AtomOccurrenceReading.occRestrict_atom`)。命題 4.1 の Lean
対応物は `EquationSemanticRealization.chiE` / `chiE_natural` である。
