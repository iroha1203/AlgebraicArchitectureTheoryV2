# ArchSig v0.5.1 PRD — LawPolicy Stage 2(law-equation-surface と方程式供給経路の一本化)

対象は LawPolicy 案4 の Stage 2 = 方程式一級化。目標アウトカム **O4「Law ポリシーが AAT の求める
law を表現できるようになる」の完結**であり、v0.5.1 のスコープはこれのみとする
(ユーザー決定 2026-07-12: 外部リポジトリでのドッグフーディングと技術記事は
v0.5.2〔SAGA 完全対応〕完成後 — 順序は v0.5.1 → v0.5.2 → ドッグフーディング)。
**前提: v0.5.0 リリース済み(タグ v0.5.0)、PRD-1〜5 受け入れ済み**(単一契約版数 /
conclusionCode registry / lawSurfaceRef・policies[].profileRef の予約 fail-closed /
measurement-profile 独立 artifact + finiteBounds / basisLedger)。

関連(設計の正本):

- [ArchSig v0.5.0 再設計ノート](../archive/2026-07-archsig-v0.5.0-completed/archsig_v0_5_0_redesign_note.md)
  — §4(LawPolicy 案4 + 発展追随の拡張規律)、§8 裁定3(law-equation は law surface へ)・
  裁定7(単一契約版数)・裁定10(互換ゼロ)・裁定12(migrate は SKILL が担う)
- [design_lawpolicy](../archive/2026-07-archsig-v0.5.0-completed/design/design_lawpolicy.md)
  — §2 P1/P4/P6、§3.2(binding と NormalizedAtomV2 の対応規則)、§3.4 案4、§5(境界規律)、
  §6 Stage 2、§7 未決事項(本 PRD が閉じるもの・残すものを Non-Goals に明記)
- AAT 本文: 第III部(定義11.3 law equation realization / 定理11.4 / 系11.5 / 原則11.6 /
  原則5.8 law condition 6 型 / 定理5.6C)、第VIII部(定義2.1 / 定義4.1 / 定理5.2 / 原則5.3 /
  原則2.2 Measurement Is Internal)
- [責務憲章](archmap_lawpolicy_archsig_responsibility_charter.md) — 三層分離と
  「LawPolicy は witness predicate を手書きしない」の線引き(本 PRD で law universe 宣言の行を追加)
- G-06(law は方程式である。第III部 §11 の Lean proved 接続)

## 問い

**law の方程式は author の宣言から供給されているか —
registry 焼き込みと ArchMap 混入という二つの隠れ経路は消滅したか。**

原則11.6「predicate does not determine the equation. no coefficient, no cohomology.」を
採否の判定規律にする。G-06 で「law は方程式である」(定義11.3 / 定理11.4)が Lean proved に
なった以上、方程式データが author の書けない場所(evaluator 実装・観測 artifact・計測手段 artifact)
から流れてくる経路は、この定理の実装上の否定である。判定は反例駆動で行う:

- **反例1(焼き込み残)**: law surface の宣言(witness 変数 / forbidden 生成元 / edge 束縛)を
  書き換えても計測結論が追随しない `ag.*` law が 1 つでも残れば fail。
- **反例2(観測混入残)**: 宣言を固定したまま ArchMap の atom だけを書き換えると
  I_Ob の生成元集合が変わる経路が 1 つでも残れば fail。観測が動かしてよいのは
  「宣言された変数集合の共起が生起したか」という読みだけで、何が forbidden かではない。
- **反例3(計測手段からの供給残)**: witness 変数が measurement-profile(計測手段側)から
  供給される経路が残れば fail。witness 変数は定義11.3 の violation coordinates = law 側成分である
  (law 側 artifact への配置は第VIII部 定義2.1 の M の細分という theory 整合的 tool 設計選択。
  design_lawpolicy §5)。
- **反例4(補完 fallback)**: 入力欠落・宣言欠落を registry の方程式・既定値で埋める挙動が
  1 つでもあれば fail。挙動は fail-closed(契約違反の明示エラー)か
  boundary statement 付き沈黙のどちらかに限る。

**(採用条件)** 上記反例 4 種をゼロにする変更、およびそのゼロを負系テストで固定する変更。
**(却下条件)** 判定式・スコア・重み・circuit を law surface に書けるようにする変更(v0 の轍)、
closed-equational 以外の law 型の ideal 化(原則5.8)、結論相当フィールドの入力 schema への追加、
互換機構の追加(裁定10)、SAGA 段の先取り(diagnosticCeiling 有効化・saga-comparison・
supplied faithfulness — 0.5.x 後続波)は、たとえ有益でも却下する。

## Core Thesis

v0.5.0 出荷時点で、方程式データの供給経路は二形態に分裂したまま残っている(design_lawpolicy P1):

1. **cech / section-factorization 系**: law の内容(どの overlap の section 一致が law か)が
   `ag_measurement.rs` の evaluator 実装に焼き込みで、政策文書を変えても方程式は変わらない。
2. **square-free / tor 系**: forbidden 生成元が ArchMap の生 support atom
   (+ profile の witnessFamily)から供給され、観測された support 集合がそのまま
   I_Ob 生成元になる(`square_free_generators`)。law universe データが観測 artifact に混入している。

さらに witness 変数は計測手段側の measurement-profile(`witnessFamily`)に居残っている(P4)。
Stage 2 はこの三つを **law-equation-surface という単一の supplied artifact** に集約する:
変数宣言・ArchMap 生値座標への束縛・forbidden support 生成元・law condition 型を author が書き、
ArchSig は宣言から `I_Ob = ⟨x_S : S ∈ Forb⟩`・minimal forbidden supports・
Alexander dual hitting sets(第VIII部 定理5.2)・商環 Q を生成する(定理5.6C の範囲)。
defect class / restriction evaluator は defect source の供給と law 充足前提を要するため
生成対象に入らない(定理11.4 の supplied 成分。Stage 3 = SAGA 波の管轄)。

あわせて、3 artifact(law-policy / law-equation-surface / measurement-profile)が独立に
fingerprint を持つ policy-bundle を新設し、「政策は同一のまま計測だけ変えた」を
artifact 水準で言える台紙を作る(P6。定理8.4 / 8.5「比較可能性はデータ」の示唆を受けた
tool 設計選択。comparison data 本体は別次元でありスコープ外)。

## Design Principles

1. **DSL 3 制限 + deny_unknown_fields**: (i) closed-equational のみ ideal 化、
   (ii) 生成元は square-free monomial(witness 変数集合の部分集合)のみ — 係数・重み・スコア不可、
   (iii) binding は名前照合 / edge 宣言のみ。重み・スコア・circuit DSL は将来も schema に足さない
   (v0 の轍の再発防止を設計文書に明記)。
2. **anti-weakening**: law surface に結論相当フィールド(verdict / h1Zero / boundaryMembership /
   minimalForbiddenSupports / globalCoherent 等)を定義しない。加えて ArchMap R3 と同型の
   判定語 hard error(`check_law_surface_no_conclusion_shortcuts`: nonzero / obstruction /
   violation / mismatch / lawful / certificate 系を lawId・variable 名の語境界 exact match で拒否)。
   「定理の結論に現れる構造を supplied certificate として受け取らない」(第X部)の政策文書版。
3. **予約フィールドは fail-closed**: Stage 3 用の欄(law surface の `skeleton` / `defectSources` /
   `quotientSheafCondition`、profile の `diagnosticCeiling`)は schema に定義するが、
   書かれたら「未対応の宣言」として明示エラー。黙って無視しない。
4. **law surface は必須供給(本 PRD の裁定)**: design_lawpolicy §3.4(a) の 4 行条件表
   (lawSurfaceRef 有無 × --law-surface 有無)は「Stage 1 期の文書が無告知で意味を変えられない」
   ための機構だったが、単一契約版数(受理は完全一致のみ)により v0.5.0 文書は v0.5.1 で
   機械的に受理されず、保護対象が消滅した。よって law-policy/v0.5.1 は `lawSurfaceRef` 必須・
   `analyze` は `--law-surface` 必須とし、縮退 contract 行は設けない。
   残すのは宣言と供給の一致検査(id 突合)のみ。これは 4 行表の否定ではなく、
   その目的(無告知の意味変更防止)が版数機構で達成された後の簡約である。
5. **版数一斉更新**: 裁定7(全 schema 文字列 = 単一契約版数 = リリース版数)に従い、
   形状不変の artifact を含む全 schema 文字列を `<name>/v0.5.0` → `<name>/v0.5.1` に更新する。
   受理は現行版数の完全一致のみ。互換窓・deprecated エントリは置かない。
6. **観測層は schema 形状不変・authoring 規約は改訂**: archmap/v2 の schema・R1-R3・
   判定語 hard error は変更しない。ただし square-free 系 support atom の役割は
   「forbidden 生成元の供給」から「宣言された変数集合の共起という観測事実」へ反転する
   (意味論移行)。この移行は law surface validation・archmap-creater SKILL・fixture の
   三点で同一規則として同一 PR 群で固定する(drift 防止。design_lawpolicy §6 リスク表)。
7. **migrate なし**: 裁定10 / 裁定12 により migrate コマンドは作らない。
   law-policy-creater SKILL が新形の新規作成のみを担う(旧フォーマットのバックフィル非サポート)。
8. **Rust / Lean 非対応**: Lean `LawEquation.lean` の語彙借用は便宜であり contract ではない。
   proved の帰属は theoremRef の形で書き分ける。

## 改修(本体)

- **R1(law-equation-surface 新設)** `law-equation-surface/v0.5.1`:
  `laws[]` = `lawId` / `conditionType`(原則5.8 の 6 型 enum: `closed-equational | open |
  constructible | descent | temporal | stacky`)/ `witnessVariables[].{variable, binding}` /
  `forbiddenSupportGenerators[].support` / `evaluatorRef`。型規律を schema validation で強制:
  closed-equational は witnessVariables + forbiddenSupportGenerators 必須・evaluatorRef 禁止、
  他 5 型は evaluatorRef 必須・ideal 系欄(witnessVariables / forbiddenSupportGenerators)禁止。
  deny_unknown_fields + 判定語 hard error(原則2)。Stage 3 予約欄
  (`skeleton` / `defectSources` / `quotientSheafCondition`)は定義のみ・書かれたら fail-closed。
  単独検証サブコマンド `archsig law-surface --law-surface law_surface.json` を新設。
  schema catalog と lock fixture(`schema_version_catalog.json`)に登録。
- **R2(binding 解決規則)** design_lawpolicy §3.2 の対応規則を validation + 実行系に実装する。
  square-free / tor 系: **変数名の同一性照合** — law surface の `variable` 名が、選ばれた context 内の
  support atom の変数リスト(subject / object のカンマ区切りを合併、区別なし)の要素として
  現れるとき、その atom はこの変数を含む観測 support。別名は `binding.archmapVariable` で明示
  (省略時は `variable` と同名)。cech 系: `binding.edge: ["ctx:a", "ctx:b"]` を
  `restricts_to` 由来の導出 1-skeleton の辺に解決し、解決不能は validation fail。
  binding で参照可能な axis / predicate 語彙(`support` / `cooccurrence` / `sectionValue`)は
  `aat-atom-vocabulary` 側 manifest に一元化し、law surface validation と archmap-creater が
  同一 manifest を参照する(語彙 drift 防止)。
- **R3(経路 (i) の移行: square-free / tor)** I_Ob 生成元の供給を、観測 atom 直取り
  (`square_free_generators` の現行経路)から law surface の Forb 宣言へ移す。
  support atom は observed complex 側(宣言された変数集合の共起の生起)へ再解釈し、
  宣言にない変数を含む atom は当該 law の witness 座標に射影されない(照合は宣言変数上でのみ)。
  minimal 化・I_Δ・Alexander dual・Q の計算は従来どおり ArchSig が独占(憲章)。
  ArchMap authoring 規約・archmap-creater SKILL・既存 fixture を同一 PR 群で改訂(原則6)。
- **R4(経路 (ii) の移行: cech / section-factorization)** evaluator 焼き込みの law 内容を
  「law surface 宣言 → 実行計画」駆動へ再編する。laws[] を走査して evaluator 実行計画を組む
  組み立て層は新モジュールに置き、既存 if-else dispatch の連鎖に追記しない(モジュール規律)。
  既存 evaluator の計算本体(F₂ 線形代数・rank 判定)は変更しない — 変わるのは
  「何を計測するか」の供給元だけであり、計測値は R9 の数値ロックで不変を実測する。
- **R5(witnessFamily の移設)** measurement-profile から `witnessFamily` を削除する
  (deny_unknown_fields により残置は fail)。witness 変数の唯一の供給源は law surface。
  profile は計測手段(site / cover / 係数 / resolution / predicates / verdict discipline /
  finiteBounds)のみを持つ。`docs/tool/law_policy.md` の第VIII部対応表を改訂し、
  「selected witness family」行の供給元を law surface へ差し替える(M の細分の注記込み)。
  Stage 3 予約欄 `diagnosticCeiling` を profile に定義のみ追加(fail-closed)。
- **R6(law-policy 側の解決規則)** `law-policy/v0.5.1`: `lawSurfaceRef` を必須化し、
  supplied surface の `id` との一致を検査。`policies[].law` は surface の `lawId` への解決必須
  (未解決は validation fail)。`policies[].evaluator` と law の `conditionType` / binding.axis の
  整合(square-free axis の closed law に tor 系 evaluator を張る等の不整合)は
  registry manifest 所有の対応表で検査する。severity / scope / basis の運用判断面は不変
  (LawPolicy は selector のまま。憲章 C5)。
- **R7(policy-bundle と fingerprint)** `archsig-policy-bundle/v0.5.1` 新設:
  `lawPolicyRef` / `lawSurfaceRef` / `measurementProfileRef` / `componentFingerprints`。
  fingerprint は canonical JSON bytes の sha256(parse → object キー辞書順 → 最小区切り
  UTF-8 再直列化。整形・キー順・改行差で不変)。hash 実装は `sha2` crate を追加し自前で書かない。
  検証サブコマンド `archsig policy-bundle` と `analyze --policy-bundle`(個別フラグ指定と排他)を
  新設し、再計算・照合の不一致は validation fail。componentFingerprints を run-manifest と
  measurement packet の run 契約に記録する(compare / comparison data 本体の拡張はスコープ外 —
  ここでは「どの成分が固定されたか」の記録まで)。
- **R8(版数一斉更新)** schema catalog の全 schema 文字列(archmap-scope-manifest /
  llm-atom-archmap / aat-atom-vocabulary / law-policy / measurement-profile /
  archsig-repair-plan / law-evaluator-registry / archsig-measurement-packet /
  archsig-boundary-statement / archsig-gate-policy / archsig-gate-report / archmap-diff /
  archsig-comparison-report / archsig-run-manifest / archsig-atom-viewer-data /
  archmap-candidate-packet / archmap-extraction-consistency / archmap-coverage-ledger、
  および新設 2 種)を `v0.5.1` に更新し、lock fixture を改訂。v0.5.0 文字列の入力は全面拒否。
- **R9(fixture と数値ロック)** 既存 AG fixture・golden corpus・one-cent drift example の入力一式を
  新供給経路(law surface 付き)へ全面改訂する(旧形 fixture は残さない)。
  **計測値の不変ロック**: 擬円周 H^1 非零、hitting sets {q} / {p,r}、Tor_1 非零、
  F₂ circle nerve、one-cent drift の analyze → gate BLOCK → repair → PASS 系列が、
  供給経路移行の前後で同一の計測値・同一の verdict を再現することを実測固定する
  (供給経路の移行は計測の意味を変えない、の機械証拠)。決定論(同一入力 → byte 同一出力)維持。
- **R10(反例系の負系テスト)** 問いの反例 4 種をテストとして固定する:
  反例1 = 宣言追随の正系(forbidden 生成元の増減が minimalForbiddenSupports / hitting sets に、
  edge 束縛の変更が計測対象 overlap に反映される)、反例2 = 宣言固定 + atom 追加で
  I_Ob 生成元集合が不変(観測の読みだけが動く)、反例3 = witnessFamily 入り profile が fail、
  反例4 = law surface 欠落 / id 不一致 / 未解決 lawId / 宣言外 law の `ag.*` 評価がすべて明示 fail。
- **R11(SKILL / docs / website 同期)** law-policy-creater を 3 artifact
  (law-policy / law-surface / measurement-profile)+ bundle の authoring に拡張し、
  law surface の良悪対例集(判定語入り lawId の悪例、closed 以外の ideal 化の悪例、
  binding 照合の良例)を references に置く。archmap-creater に atom 意味論の規約改訂
  (support atom = 共起の観測事実)を反映。archsig-reader / archsig-pr-reviewer の読み方を同期。
  `docs/tool/law_policy.md`(対応表改訂)・責務憲章(law-equation-surface = 制度選択
  law universe の行を追加)・`tools/archsig/docs/commands.md`・README・website の
  ArchSig 製品マニュアル該当ルートを同一波で改訂する。hitting sets の表示箇所には
  第VIII部 原則5.3 の boundary(combinatorial repair target であって repair semantics ではない)を
  従来どおり併記。

## Changed / Removed Fields

- **Added**: `law-equation-surface/v0.5.1`(+ Stage 3 予約 3 欄)、`archsig-policy-bundle/v0.5.1`、
  `law-surface` / `policy-bundle` サブコマンド、`analyze --law-surface` / `--policy-bundle`、
  run-manifest / packet の componentFingerprints、profile の `diagnosticCeiling`(予約)、
  `sha2` 依存。
- **Changed**: 全 schema 文字列 v0.5.1(R8)、law-policy(lawSurfaceRef 必須化 +
  policies[].law の surface 解決)、cech / square-free / tor / section-factorization 系
  evaluator の供給経路(計算本体・計測値は不変)。
- **Removed**: measurement-profile の `witnessFamily`、`square_free_generators` の
  atom 直取り経路、evaluator 焼き込みの law 内容選択。
- **Not changed**: archmap/v2 の schema 形状(版数文字列のみ更新。binding は既存生値語彙への参照)、
  measurement packet の 6 区画、五値 verdict、gate / compare の決定面、finiteBounds の
  hard cap 規律、conclusionCode registry の既存 token。

## Failure Contract

- **fail-closed(明示エラー)**: lawSurfaceRef 欠落・`--law-surface` 欠落・id 不一致・
  未解決 lawId・宣言外 law の `ag.*` 評価・conditionType 型規律違反(closed 以外への ideal 欄、
  closed への evaluatorRef)・予約欄の使用・判定語入り surface・未知フィールド・
  edge 解決不能・fingerprint 不一致・witnessFamily 残置・v0.5.0 版数文字列。
- **沈黙(boundary statement)**: 宣言された witness 変数が観測に生起しないことは
  契約違反ではなく計測結果であり、到達した読みを主文に、未生起は boundary として記録する。
  fail-closed と沈黙の二分以外の挙動(補完・推測・縮退)は存在しない。

## Implementation Plan

各 PR の完了条件: `cargo test`(archsig / fieldsig)green、`git diff --check` +
hidden Unicode scan、**PR 説明に「問いの反例 1〜4 のどれをゼロへ近づけたか」を 1 行**。

| PR | 内容 | 対応 R |
| --- | --- | --- |
| PR-1 | law-equation-surface schema + validator(型規律・判定語 hard error・予約欄)+ `law-surface` サブコマンド + catalog / lock fixture 登録 + binding 語彙 manifest | R1, R2(validation 側) |
| PR-2 | 経路 (i) square-free / tor の移行 + atom 再解釈 + archmap-creater 規約 + 対象 fixture 改訂 | R2(実行側), R3 |
| PR-3 | 経路 (ii) cech / section-factorization の移行 + 実行計画組み立ての新モジュール | R4 |
| PR-4 | witnessFamily 移設 + law-policy 解決規則(lawSurfaceRef 必須化)+ 版数一斉更新 + 全 fixture 仕上げ | R5, R6, R8 |
| PR-5 | policy-bundle + canonical JSON fingerprint + run 契約への記録 | R7 |
| PR-6 | 反例負系テスト仕上げ + 数値ロック実測 + SKILL / docs / website 同期 | R9-R11 |

順序は PR-1 → PR-2 → PR-3 → PR-4 → PR-5 → PR-6。PR-2 と PR-3 は PR-1 の後なら並行可。
必須化と版数更新(PR-4)は両経路の移行が終わるまで行わない(中間状態でも常に green を保つ)。

## Acceptance Criteria

1. **反例1(焼き込み)の消滅**: (a) law surface の forbidden 生成元宣言の増減が
   minimalForbiddenSupports / hitting sets / Q に追随する(正系実測)。(b) cech 系で
   edge 束縛宣言の変更が計測対象 overlap に追随する。(c) 宣言を経由せずに law 内容を選択する
   コード経路(atom 直取りの生成元構成・evaluator 内の law 内容焼き込み)が存在しない
   (コード監査 + 負系テスト)。
2. **反例2(観測混入)の消滅**: 宣言固定のまま ArchMap に support atom を追加した fixture で、
   I_Ob 生成元集合が不変であり、変わるのは観測の読み(生起 / 未生起)のみであることを固定。
3. **反例3(計測手段供給)の消滅**: measurement-profile/v0.5.1 に witnessFamily が定義されず、
   書かれた profile は deny_unknown_fields で fail。witness 変数の供給源が law surface のみで
   あることの経路テスト。
4. **反例4(補完)の消滅**: law surface 欠落・id 不一致・未解決 lawId・宣言外 law の評価が
   すべて明示 fail し、registry の方程式・既定値で埋める挙動が存在しない(負系 4 本以上)。
5. **anti-weakening(負系)**: 結論相当フィールド・判定語入り lawId / variable 名・
   未知フィールド・予約欄(skeleton / defectSources / quotientSheafCondition /
   diagnosticCeiling)を含む入力がそれぞれ明示エラーで fail する。
6. **型規律(負系)**: closed-equational 以外への forbiddenSupportGenerators、
   closed-equational への evaluatorRef、conditionType と evaluator の不整合が schema / registry
   検査で fail する。
7. **数値ロック不変**: R9 の 5 系列(擬円周 H^1 / hitting sets {q},{p,r} / Tor_1 /
   F₂ circle nerve / one-cent drift の 4 幕)が移行前後で同一計測値・同一 verdict。
   同一入力 2 run の byte 同一(決定論)維持。
8. **fingerprint**: canonical JSON 正準化(キー順・空白・改行差で指紋不変)の正負系、
   `policy-bundle` / `analyze --policy-bundle` の照合不一致 fail、run-manifest と packet に
   componentFingerprints が記録されることの固定。
9. **版数統一**: catalog / lock fixture の全 schema 文字列が v0.5.1 であり、
   v0.5.0 文字列の入力が全面拒否される(完全一致のみ)。
10. **SKILL / docs**: law-policy-creater が fixture リポジトリ上で 3 artifact + bundle を
    新規作成し `analyze` が通る手順を references の実行例として固定。archmap-creater の
    意味論規約・law_policy.md 対応表・責務憲章・commands.md・README・website 該当ルートが
    v0.5.1 実体と一致(記載の全コマンドが実行可能)。
11. **問いへの遡及**: 各 PR の説明に、反例 1〜4 のどれをゼロへ近づけたかが 1 行で書かれている。

## Non-Goals

- **Stage 3(SAGA 波)**: `skeleton` / `defectSources` / `quotientSheafCondition` /
  `diagnosticCeiling` の有効化、SAGA 系 evaluator の階段(saga-comparison / class 転送 /
  saga-grounded 10 結論 / harmonic-debt / refactor-transport)— 0.5.x 後続。本 PRD は予約のみ。
- **supplied faithfulness / gluing data / H^1 comparison data / law-equation witness の slot** —
  design_lawpolicy §7 未決事項3 のまま。各 slot が確保されるまで、対応する段の
  law 依存肯定結論は出力しない(系11.5 の逆向き遮断)。
- **repair-proposal 系 artifact・comparison data 本体・compare の class-transport・
  archmap-delta / delta-apply・observation-frontier** — 別次元 / 後続波。
- **conormal 係数(I_U/I_U²、G-04 系)** — profile の coefficient enum という拡張点を残すのみで
  実装しない(受け皿も作らない。v0.6.0 予約)。
- **pack 機構の復活** — law surface の良例集が貯まってから判断(未決事項5)。
- **ArchView の law 方程式パネル** — ArchView 波(V-A〜C)。packet 側の invariant は本 PRD で揃う。
- **descent / temporal / stacky 型の evaluator 追加** — conditionType の宣言は許すが
  evaluator は既存 registry の範囲(temporal は FieldSig 側スコープの可能性。未決事項6)。
- **migrate コマンド・互換機構** — 恒久非目標(裁定10 / 裁定12)。
- **外部リポジトリのドッグフーディング・技術記事** — v0.5.2(SAGA 完全対応)完成後
  (ユーザー決定 2026-07-12: SAGA を実戦投入した上でドッグフーディングと記事に進む)。
