# PRD: Research Lean を本体 Formal tree から分離する

- 作成: 2026-07-11
- 親 Issue: #3199
- 実行: Codex `prd-loop`
- 対象: `Formal/AG/Research/**`、Research Lean の Lake package、検証・昇格監査

## 問い

**Research Lean を、本体から誤って参照できず、Research 成果を弱い本体 theorem に
置き換えて完了表示できない構成へ移せるか。**

この問いへの回答には、単なる directory rename ではなく、次の3点が同時に必要である。

1. 本体 package から Research module を解決できない。
2. Research package は本体へ一方向に依存し、独立して全件 build できる。
3. Research→本体の昇格は、元 statement の全結論と material premise を本体側が
   覆うことを、Research 側の audit-only surface で検査する。

## 現状診断

- `lakefile.toml` は `FormalAGResearch` を別 `lean_lib` として定義するが、source は
  本体と同じ `Formal` root にある。別 build target は build coverage であり、
  import のアクセス制御ではない。
- 2026-07-11 の main では、本体から `Formal.AG.Research` への import は0件である。
  ただし `.github/lean_quality/check_research_import_direction.sh` はdiff中の
  `+import Formal.AG.Research...` だけを検査し、現在木全体や `public import` を
  fail-closedに検査しない。
- corpus は239 fileである。

  | module群 | file数 |
  | --- | ---: |
  | `QualitySurface/**` | 199 |
  | `SFT/**` | 36 |
  | `SFTDynamics/**` | 3 |
  | `Basic.lean` | 1 |

- `Formal/AG/Research.lean` のaggregate importは198 moduleで、239 file中41 module
  （SFT 36、SFTDynamics 3、QualitySurface 2）を収載していない。現行239 fileのbuild coverageは
  `lakefile.toml`のglobが担い、`research-loop` / `target-theorem-loop` / `math-lean-review` /
  research docs / 台帳は現在pathと `FormalAGResearch` build targetを前提にする。
- direct importを禁止しても、Research statementの結論を落とす、対象を狭める、
  material premiseをtheorem引数・typeclass・structure fieldへ移す実装は可能である。
  現行premise diffはreview用出力で、昇格のhard failではない。
- #3172 は増分import scanを実装済み、#3167 はResearch evidence inventory整備を
  要求済み、#3089 は重いResearch buildの通常CI配線を扱った。いずれも本PRDの
  source分離と昇格監査を完了していない。
- 現在の`docs/aat/research_evidence_index.md`は索引表が空で、
  `docs/aat/research_evidence_inventory.md`は存在しない。#3167のclosed表示だけを
  backfill完了証拠にせず、R5のaudit対象を空集合にしてはならない。

## 現行 source of truth

- repository文書lifecycleとPRD規律: `docs/guideline.md`
- Research loop設計: `research/DESIGN.md`、`research/README.md`
- Lean statusとResearch下限原則: `docs/aat/guideline.md`
- Lean品質・固定statement: `docs/aat/lean_quality_standard.md`
- Research成果と移植状況: `docs/aat/research_evidence_index.md`、
  `docs/aat/lean_theorem_index_research.md`、`research/reports/**`
- review規律: `.codex/skills/math-lean-review/SKILL.md`、
  `.codex/skills/_shared/lean-refutation-checklist.md`
- 現行build構成: `lakefile.toml`、`Formal/AG/Research.lean`
- 現行CI検査: `.github/workflows/lean.yml`、`.github/lean_quality/**`

本PRDは実行中だけ有効な契約である。完了後も残る配置規則、build手順、昇格規則、
status、scan契約は上記の現行sourceへ反映し、本PRDを正本として参照しない。

## Target Statements

固定contractのsource of truthは
`docs/aat/statement_contracts/research_promotion.md`である。本PRDは固定statementや
command surfaceを複製せず、R3–R5とAC5–AC7で同contractの実装・発火を要求する。

R3・R4は新しい数学theorem・def・structureを追加せず、本PRDの移動同一性条件に
従う。具体的には、完全修飾名のprefixを除くidentifier、universe、binders、premise、
conclusion、proof term、axiom依存を維持し、旧Research prefixから新Research prefixへの
機械的変更だけを許可する。R5は同contractのaudit declarationと依存検査commandを実装する。

## 要求

### R1: 逆依存検査を全体検査へ強化する

- 現在木全体またはLean import graphを検査し、本体からResearchへの到達を0件に固定する。
- `import`、`public import`、利用中Lean versionで有効なimport modifierを覆う。
- 新規file、既存file変更、aggregate root変更、間接到達のfixtureを持つ。
- 既存のdiff-only checkは補助出力へ下げるか、全体検査に置換する。
- `.github/lean_quality/check_research_legacy_refs.sh`に`no-new <base> <head>`と`final`を実装する。
  旧prefixの現行path利用と、checker source・期待failure fixture内の検出用文字列を区別する。
- 旧prefix文字列の許可surfaceは同checker実装、
  `.github/lean_quality/fixtures/research_legacy_refs/negative/**`、`docs/archive/**`だけとする。
  negative fixtureは同directoryの`expectations.tsv`に期待failure commandを全件登録し、未登録fileを
  許可しない。production Lean、現行docs、skills、workflow設定での利用は許可せず、allowlist外hitを
  failにするpositive / negative fixtureを持たせる。

### R2: Research専用Lake packageを作る

- package directoryは `research-lean/` とする。
- Lean source rootは `research-lean/ResearchLean/`、module prefixは
  `ResearchLean.AG` とする。
- Research packageはroot packageをpath dependencyとしてrequireする。
- root packageはResearch packageをrequireせず、rootの`lake build`環境から
  `ResearchLean.AG.*`を解決できない。
- Research full build commandは `cd research-lean && lake build` とする。
- packageは`packagesDir = "../.lake/packages"`でroot workspaceの取得済みdependency sourceを
  再利用し、root package自体は`path = ".."`でrequireする。
- root default buildはResearch全件buildを含めない。
- 移動PRで使う`check_research_migration_manifest`を追加する。各移動PRのbase commitから
  旧fileを読み、headの新fileと比較して、canonicalized source digest、declaration数、
  universe / binder / premise / conclusionを含むtype digest、value expression digest、
  axiom setを`.tmp/research-migration/`へ出力する。件数差、digest差、比較不能をfailにする。
- declaration単位の`migration_record`を
  `<batch>/<new-relative-file>#<declaration-name>`形式で生成する。keyは旧module prefixを含まず、
  全artifact内で一意とし、R3/R4 artifactへ保存してpromotion manifestから同じkeyでjoinできる
  schemaにする。重複key、形式違反、digest欠落をfailにする。
- Research packageのmodule manifestを入力に、各moduleのfocused checkと、全declarationの
  axiom auditを実行するcommandを追加する。
- `.github/lean_quality/check_changed_public_artifacts.sh <base> <head>`を追加する。
  PR追加行のhidden / bidirectional Unicode、private local path、machine-specific identifier、
  変更Lean sourceの禁止primitiveを検査し、検査規則自身を自己検出しないfixtureを持たせる。

### R3: SFT系moduleを移動する

- `SFT/**` 36 fileと`SFTDynamics/**` 3 fileをResearch packageへ移す。
- `Basic.lean`は`SFT/ConwayTwoTopology.lean`、`SFTDynamics/TraceSite.lean`、
  `QualitySurface/SupportHitting.lean`から参照されるためR4で移す。
- R3完了からR4完了まで、移動済みSFT系がroot側の旧`Basic`をimportすることを
  一時的に許可する。この依存はR4で除去し、R7のmust-not-remainで0件にする。
- statement、premise、proof、axiom依存を変更しない。
- 39 fileの移動PRでmigration manifest比較を実行し、39/39一致をPR artifactへ保存する。

### R4: Basic・QualitySurfaceを移動する

- `Basic.lean` 1 fileと`QualitySurface/**` 199 fileをResearch packageへ移す。
- import graphを`ResearchLean.AG.*`へ機械的に更新する。
- 新Research aggregate rootを追加し、239 file全件をfull build対象にする。
- statement、premise、proof、axiom依存を変更しない。
- 規模上、1 Issue内で複数commitに分けてよいが、旧rootと新packageに同一sourceを
  重複保持する中間commitをPRの最終状態に残さない。
- 200 fileの移動PRでmigration manifest比較を実行し、200/200一致をPR artifactへ保存する。
- 239 moduleのfocused checkと、module manifestから抽出した全declarationのaxiom auditを
  新Research package上で実行する。

### R5: Research→本体の昇格監査を実装する

- `docs/aat/research_evidence_index.md` の全 `ported` 行に加え、
  `docs/aat/lean_theorem_index_research.md`、reports、本体側のResearch対応記述から
  本体対応がある受理成果を検索し、非空の昇格manifestを作る。
- manifestは少なくともResearch
  `lawEquation_constructs_groundedComparisonPacket`と対応する本体generated-pair routeを含む。
- index表が空であることをaudit対象0件の根拠にしない。対応候補の欠落は未達としてIssueへ戻す。
- 各行にTarget Statementsのaudit declarationを置き、全conjunctを対応させる。
- `#assert_promotion_signature`、`#assert_promotion_dependencies`、
  `#assert_promotion_inputs`、`#assert_promotion_conjuncts`、
  `#assert_promotion_premises`を実装し、signature drift、direct / transitive Research proof依存、
  入力binder置換、本体result / fieldの未使用、未申告の
  theorem argument / typeclass / structure-field premiseをhard failにする。
- negative fixturesとして、結論削減、追加premise、対象縮小、typeclass escape、
  structure-field escape、Research theorem直接利用、helper / opaque def / instance経由の
  Research proof依存、`skeleton`置換、binder dummy use、本体result破棄、field入替・未使用を
  それぞれ失敗させる。さらにmanifest行欠落、discharge closure欠落、construction /
  conversion追加premise、conjunct index欠落・重複、semantic project定数化、Type-valued
  witnessからの`Nonempty` / `Exists` / packet / structure answer encoding、
  input-field行重複、field equation型不一致を失敗させる。
- audit結果からevidence indexの各`ported`行へ辿れるようにする。

### R6: 運用surfaceを同期する

- `research/DESIGN.md`、`research/README.md`、research loop skills、target theorem skill、
  math review skill、shared checklistを新path・新build commandへ更新する。
- `docs/aat/guideline.md`、`docs/aat/lean_quality_standard.md`、evidence index、theorem index、
  proof obligationのfile pathと恒久規律を更新する。
- `AGENTS.md`、`CLAUDE.md`、research goals / ideas / reports、`docs/note/**`、
  `outreach/**`、website公開面の現行pathを更新する。
- `docs/sft/software_field_theory.md`のResearch artifact pathは本Issueの明示対象とし、
  数学claimを変更せずpathだけを更新してmath reviewを通す。
- Research変更時または手動実行の専用CI jobを用意する。
- 重いResearch full buildを全PRの通常CIへ無条件に戻さない。
- 本PRDへの参照を現行docs・source・test・workflowに追加しない。

### R7: 旧経路を撤去する

- `Formal/AG/Research/**`、`Formal/AG/Research.lean`、`FormalAGResearch` targetを削除する。
- 旧module prefix、互換wrapper、alias、重複declaration、依存repackageを0件にする。
- 本体build、Research full build、昇格audit、docs整合を最終確認する。

## Acceptance Criteria

- [ ] **AC1**: root packageから`ResearchLean.AG.*`をimportするnegative fixtureが失敗し、
  Research packageから`Formal.AG.*`をimportするpositive fixtureが通る。
- [ ] **AC2**: 本体→Researchのdirect / public / indirect importを現在木全体で検出し、
  違反fixtureがすべてhard failする。
- [ ] **AC3**: Research required CI checkの`cd research-lean && lake build`が239 file全件を
  elaborateして通る。
- [ ] **AC4**: root required CI checkの`lake build`がResearch full buildを含まずに通る。
- [ ] **AC5**: 239 file全件が`ResearchLean.AG`へ移り、39 fileと200 fileの各移動PRで
  `check_research_migration_manifest`がcanonicalized source、declaration数、type/value digest、
  axiom setの全件一致を機械検査し、合計239/239のartifactがある。
- [ ] **AC6**: evidence index、Research theorem index、reports、本体側対応記述から作った
  非空の昇格manifestにaudit declarationがあり、少なくともgenerated-pair routeを含め、
  各Research元の全conjunctとmaterial premiseを本体routeから再構成する。
- [ ] **AC7**: `#assert_promotion_signature`、`#assert_promotion_dependencies`、
  `#assert_promotion_inputs`、`#assert_promotion_conjuncts`、`#assert_promotion_premises`が
  全audit declarationで通り、非空のinput / input-field / conjunct / premise ledgerを持つ。
  固定contractの
  全negative fixtureが、結論・premise・binder preservation・conjunct proof-use・
  transitive proof dependencyの対応検査で失敗する。
- [ ] **AC8**: research loop / target theorem / math review / shared checklistが新pathと
  Research専用buildを使用する。
- [ ] **AC9**: Research変更時または手動実行のCI jobがResearch full buildとauditを実行し、
  通常PRのroot buildにResearch full buildを重複させない。
- [ ] **AC10**: evidence index、theorem index、proof obligation、research reportsの
  現行pathが新配置と一致し、`docs/aat/guideline.md`と`lean_quality_standard.md`の恒久規律、
  AGENTS / CLAUDE / goals / ideas / notes / outreach / website / SFT artifact pathも同期する。
- [ ] **AC11**: `Formal/AG/Research/**`、`Formal/AG/Research.lean`、`FormalAGResearch`、
  旧module prefix、互換wrapper、alias、重複sourceが現行pathとして残っていない。
  旧prefix文字列はR1で固定したchecker source・`expectations.tsv`登録済みnegative fixture・
  archive以外に存在しない。
- [ ] **AC12**: 各docs-only PRは`docs-review` 4観点、Lean差分を含む各PRは
  `math-lean-review` 4本を通り、最終状態は両review gateで承認される。
- [ ] **AC13**: `git diff --check origin/main...HEAD`と
  `.github/lean_quality/check_changed_public_artifacts.sh origin/main HEAD`が通る。PR追加行に
  hidden / bidirectional Unicode、private local path、machine-specific identifierがなく、
  変更Lean sourceの追加行に`axiom` / `admit` / `sorry` / `unsafe`がない。negative fixtureは
  専用directoryと期待failure commandの対応をreview packetで全件分類する。
- [ ] **AC14**: 現行sourceへ恒久規則・build手順・statusが反映され、本PRDへの参照が
  `docs/archive/`を除くrepository全体で0件になった後、本PRDがarchiveされる。
- [ ] **AC15**: 新Research packageの239 module manifestに対するfocused checkが全件通り、
  manifestから抽出した全declarationのaxiom auditが標準公理のみを報告し、Research専用CIで
  実際に発火する。

## Requirement Matrix

| Requirement | Issue | 依存AC |
| --- | --- | --- |
| R1 逆依存・旧参照全体検査 | #3200 | AC2, AC11, AC13 |
| R2 Research package | #3206 | AC1, AC4, AC13。AC3/AC5/AC15用checkerとsmokeを提供 |
| R3 SFT系移動 | #3202 | AC3/AC5の39 file分を提供 |
| R4 Basic・QualitySurface移動 | #3203 | AC3/AC5を239 fileで完了、AC15を完了 |
| R5 昇格監査 | #3201 | AC6, AC7 |
| R6 運用同期 | #3207 | AC8, AC9, AC10, AC12, AC13 |
| R7 旧経路撤去・最終監査 | #3205 | AC1–AC15 |

## Implementation Plan

1. #3200: 現行0件を全体scanで固定する。
2. #3206: `research-lean/` packageとsmoke fixtureを作る。
3. #3202: SFT / SFTDynamicsを移動する。
4. #3203: Basic / QualitySurface / aggregateを移動する。
5. #3201: 移動済み全Research corpusから非空manifestを作り、audit declarationと
   signature / dependency検査を実装する。
6. #3207: docs、skills、CI、台帳を新配置へ同期する。
7. #3205: 旧path・target・参照を撤去し、最終reviewとcompletion reviewを行う。

各周回は1 Issue = 1 PRとする。複数PRを同時にopenしない。Lean fileを触るPRは
規模を問わず`math-lean-review` 4本を通す。

`lake build`と同等の全体elaborationは、Lean / package差分がある場合だけ統括エージェントが
PR前に最大1回実行し、docs-onlyでは0回とする。差分が`research-lean/**`を含む場合は
Research package build、それ以外のLean / package差分はroot buildをローカルの1回に選ぶ。
選ばなかった独立package側はrequired CI checkの結果を証拠にする。
review subagentは実行せず、統括エージェントまたはCIから渡された結果を独立査読の証拠として使う。
R6のResearch required CIが入る前は、選択したResearch local buildを移行PRの暫定証拠にし、
AC3の最終達成はR6後のrequired CI発火で判定する。

## Must-not-remain

- 本体packageからResearch moduleを解決できる構成
- `Formal/AG/Research/**`または`Formal/AG/Research.lean`
- `FormalAGResearch` build target
- `Formal.AG.Research` module prefixを現行pathとして使う参照
- R1の狭いallowlist外にある旧prefix検出文字列
- 旧pathの互換wrapper、alias、re-export、重複source
- Research theoremをimportまたはproof内で直接呼ぶ昇格audit
- 空のevidence indexを根拠にaudit対象を0件として通す実装
- Research元より結論が少ない、premiseが多い、対象が狭い本体statementの`ported`表示
- Research full buildを全PRの通常root buildに重複させるworkflow
- 現行docs・source・test・workflowから本PRDへの参照

## Failure Contract

次のいずれかを確認したPRはマージせず、該当Issueを未達へ戻す。

- buildを通すためにtheorem statement、premise、proof内容、axiom依存を変更した。
- 旧pathをwrapper / alias / re-exportとして残した。
- root packageがResearch packageをrequireし、双方向依存を作った。
- audit declarationがResearch元theoremまたはResearch support theoremのproofを利用した。
- negative fixtureが意図した欠陥を発火させない。
- docsや台帳だけを更新して実装ACを完了表示した。
- `lake build`成功だけをstatement一致・premise放電の証拠にした。
- protected math sourceを明示許可なく変更した。

## Non-goals

- `docs/aat/algebraic_geometric_theory/**`の数学本文変更
- Research theoremの数学内容の補強・一般化・整理
- 未移植Research成果の新規蒸留
- 既存GOALのscore、target statement、completion criteria変更
- ArchSig / FieldSig / websiteの機能変更
- Research full buildを全PRの通常CIへ戻すこと

## 停止条件

- separate packageからroot packageへのpath dependencyがLakeで構成不能と実証された。
- 移動前後のsignatureまたはaxiom依存を一致させられないmoduleが見つかった。
- `ported`行のResearch元と本体先が一意に対応せず、固定audit statementを作れない。
- Target Statementsの依存検査commandがLean環境で実装不能と判明した。
- protected math sourceの変更なしにはACを満たせない。
- 同一ACが2周連続でMergeableにならない。

停止時はPRDを弱めず、該当Issueとtracking Issueへ実証結果を記録してユーザー判断へ戻す。

## 検証

```bash
# local: Lean/package差分がある場合だけ、統括エージェントが最大1回build
if ! git diff --quiet origin/main...HEAD -- research-lean; then
  (cd research-lean && lake build)
elif ! git diff --quiet origin/main...HEAD -- \
  ':(glob)**/*.lean' lakefile.toml lean-toolchain; then
  lake build
else
  : # docs-only: local full buildなし
fi

# PR後: root / Research両required CI checkを確認
gh pr checks --watch

# 本体からResearchへの到達
.github/lean_quality/check_research_import_direction.sh

# 移行中: PR追加行への旧path再導入を文脈分類してfail
.github/lean_quality/check_research_legacy_refs.sh no-new origin/main HEAD

# final PR: 狭い検出用allowlist以外の現行面をfail-closed scan
.github/lean_quality/check_research_legacy_refs.sh final

# 共通
git diff --check origin/main...HEAD
.github/lean_quality/check_changed_public_artifacts.sh origin/main HEAD
```

## 完了とarchive

AC1–AC13とAC15、Must-not-remainの実装証拠が揃った最終PRで、恒久規則が現行sourceへ
存在することを確認する。repository現行面から本PRDへの外部参照を0件にして、
`docs/archive/research_lean_separation_prd.md`へ移す。archive後の現行面scanと
`prd-completion-review`が通った時点でAC14を達成する。
