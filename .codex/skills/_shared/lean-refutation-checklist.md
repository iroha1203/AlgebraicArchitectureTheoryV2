# Lean固有反証チェックリスト

AAT / Lean の証明・具体例提示・本体への移植を扱うときだけ読む。横断項目と実行手順は
`refutation-checklist.md` と `review-protocol.md` を参照する。

## 1. statement・premise・具体例

statement を実読し、台帳や checklist の status 記載を根拠にしない。

- 結論が仮定 structure の field 取り出しになっていないか。
- 仮定・field が `True` で充足可能な `Prop` でないか。
- 主張された instance / witness が実在し、条件文だけで具体例が欠けていないか。
- 具体例が PUnit、自明群、singleton site、`True` で埋める構成へ退化していないか。
  本文・PRD が退化例を明示的に許容する場合は、この反証を適用しない。
- 対象定理が AxiomAudit に収載され、公理依存が標準公理だけか。
- statement が本文・PRD・移植元より弱まっていないか。
- 指定された一次仕様に完全 Lean signature がある場合、signature の premise 追加・
  結論弱化・対象縮小を `docs/aat/lean_quality_standard.md` §5 で突合する。
  Lean 実装を要求する PRD・picked 候補で、target claim、必要な結論、明示された
  仮定・受け入れ条件を判定できる一次仕様が参照可能でないことを finding とする。
  完全 Lean signature の不在自体は finding としない。
- premise を独立に列挙し、実装者の三分類申告(本文由来 / 解消済み / 未解消)
  と突合する。申告のない material premise は未解消として扱う。

## 2. 意味レベルの自明化

- subsingleton 上の等式や proof-irrelevance で主張が自動成立していないか。
- 結論相当の情報が引数・field・型パラメータへ answer-encoding されていないか。
- 非自明に見える係数の非自明性が proof で使われているか。
- `Nonempty (X = X)` のような恒真 field がないか。
- 新規 Prop 述語・certificate に、満たす instance と満たさない instance の両方が
  あるか。片方が作れない申告は理由を実読し、恒真・恒偽の証拠なら finding とする。

## 3. 移植元conjunct対応(Research下限原則)

本体に新しい theorem 群を追加する差分では、タスク型宣言にかかわらず
`research/lean/ResearchLean/` を検索し、
検索語と結果を報告する。同主題の受理宣言があれば移植監査を適用する。

1. 移植元 statement を実読し、結論一覧を列挙する。
2. 本体 statement との対応表をレビュー側で独立に再構築する。
3. 欠けた結論、または移植元が構成した対象を入力 premise へ移した箇所を
   anti-weakening finding とする。
4. Research 側に同等以上の statement がある本体欠落は
   `unported (Research-proved)` とする。
5. 本体から `ResearchLean.AG` を import する再導出 wrapper は単なる依存ラッパーであり
   hard fail とする。移植は本体内で再構成する。
6. Research の逐語複製が疑われる場合、AxiomAudit、依存公理、持ち込んだ
   補助宣言の要否を検査する。
