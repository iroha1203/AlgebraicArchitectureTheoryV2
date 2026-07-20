# Lean固有反証チェックリスト

AAT / Leanの昇格・証明・発火・移植を扱うときだけ読む。横断項目と実行契約は
`refutation-checklist.md` と `review-protocol.md` を正本とする。

## 1. statement・premise・発火

statementを実読し、台帳やchecklistのstatus記載を根拠にしない。

- 結論が仮定structureのfield取り出しになっていないか。
- 仮定・fieldが`True`で充足可能な`Prop`でないか。
- 主張されたinstance / witnessが実在し、条件文だけで未発火でないか。
- 発火例がPUnit、自明群、singleton site、`True`充填へ退化していないか。
  本文・PRDが退化例を明示的に許容する場合は、この反証を適用しない。
- 対象定理がAxiomAuditに収載され、公理依存が標準公理だけか。
- statementが本文・PRD・移植元より弱まっていないか。
- 固定statementがある場合、signatureのpremise追加・結論弱化・対象縮小を
  `docs/aat/lean_quality_standard.md` §5で突合する。Lean実装を要求する
  PRD・picked候補に固定statementが無いこと自体もfindingとする。
- premiseを独立に列挙し、実装者の三分類申告(本文由来 / 放電済み / 未放電)
  と突合する。申告のないmaterial premiseは未放電として扱う。

## 2. 意味レベルの空虚化

- subsingleton上の等式やproof-irrelevanceで主張が自動成立していないか。
- 結論相当の情報が引数・field・型パラメータへanswer-encodingされていないか。
- 非自明に見える係数の非自明性がproofで使われているか。
- `Nonempty (X = X)`のような恒真fieldがないか。
- 新規Prop述語・certificateに、満たすinstanceと満たさないinstanceの両方が
  あるか。片方が作れない申告は理由を実読し、恒真・恒偽の証拠ならfindingとする。

## 3. 移植元conjunct対応(Research下限原則)

本体に新しいtheorem群を追加する差分では、タスク型宣言にかかわらず
`research/lean/ResearchLean/`を検索し、
検索語と結果を報告する。同主題の受理宣言があれば移植監査を適用する。

1. 移植元statementを実読し、結論一覧を列挙する。
2. 本体statementとの対応表をレビュー側で独立に再構築する。
3. 欠けた結論、または移植元が構成した対象を入力premiseへ移した箇所を
   anti-weakening findingとする。
4. Research側に同等以上のstatementがある本体欠落は
   `unported (Research-proved)`とする。
5. 本体から`ResearchLean.AG`をimportする再導出wrapperは依存repackageであり
   hard failとする。移植は本体内で再構成する。
6. Researchの逐語複製が疑われる場合、AxiomAudit、依存公理、持ち込んだ
   補助宣言の要否を検査する。
