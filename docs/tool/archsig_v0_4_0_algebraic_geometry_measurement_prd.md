# ArchSig v0.4.0 Algebraic Geometry Measurement PRD

この PRD は、ArchSig v0.4.0 で実装する代数幾何版 AAT
(`docs/aat/algebraic_geometric_theory/`、以下 AG 本文)対応の要求を定義する。

## 問い

この PRD のすべての要求は、次の問いに仕える。

```text
問い:
  局所的にはすべて合法なのに、全体は歪んでいる ——
  それを、誰の主観にも頼らず測り、ヘッジなしに言い切れるか?
```

v0.4.0 は H^1 のための release である。「局所的には合法、全体は歪む」は
Čech cohomology の `H^1` がちょうど捉える情報であり(R3)、
witness counting では原理的に見えない(R14 がこの差をテストとして固定する)。

主問いには、次の従う問いが続く。

```text
境界を尊重したまま、どこまで言い切れるか?              (verdict / ledger: R9, R10)
どこを・最低どれだけ直せば消えるか、まで答えられるか?  (repair: R4, R6)
計測の差分を「コードが変わった」に帰着できるか?        (determinism: R1, R12)
```

各要求・各計測の採否は、この問いで読む。問いに仕えない計測は、
それ自体に価値があっても本 release に入れない。
R13 の monodromy 系 reading 削除は、この規律の適用例である
(言い切れる基盤を持たない計測は出さない)。

この release の上位には、プロジェクトの問いがある:
「AG 本文の finite measurement geometry は、実際のコードベースに当たる道具として
本当に動くか?」。これは tool + Lean 並行ロードマップ全体の問いであり、
本 PRD はその製品側の最初の答えとして位置づく。

## 中心方針

v0.3.0 が古典 AAT 読み(witness counting 中心)の measurement coordinate を増やす
release だったのに対し、v0.4.0 は計測の数学的基盤そのものを AG 本文の
finite measurement geometry(第VIII部 Measurement Theory)へ載せ替える release とする。

中心 pipeline は次である。

```text
ArchMap v2 (finite poset site observation)
  -> MeasurementProfile v1 (selected M)
  -> typed AG evaluators
       (Cech / Stanley-Reisner / Tor / Laplacian / period / transfer)
  -> archsig-measurement-packet/v1 (AG 本文 定義11.1 準拠)
  -> conclusion-first summary / viewer
```

互換性方針: v0.4.0 の非互換性は AG measurement path に限定する。
`archmap/v2` + `measurement-profile/v1` は `archsig-measurement-packet/v1`
を一次 surface とし、v1 typed evaluator artifact chain をこの path の入力・出力
surface として扱わない。一方で、現行 CLI には `archmap/v1` + `law-policy/v1`
の structural analysis path が bounded legacy compatibility として残る。これを
削除する場合は、別 Issue で runtime、schema catalog、fixtures、FieldSig
compatibility を同時に更新する。現時点では migration tooling は作らない。

## 背景

- AG 本文は、Atom family から finite poset site、obstruction ideal sheaf、
  Čech cohomology、monomial Tor、period pairing までを
  **有限の組合せ論と線形代数**に落ちる計算可能経路として整備済みである
  (第VIII部 定理4.2 Finite AAT Computability、
  `docs/note/aat_algebraic_geometric_theory_full_review.md`(以下、レビュー)§3.1)。
- 現行 ArchSig v1 の typed evaluator は witness counting 中心の古典 AAT 読みであり、
  AG 本文の幾何的不変量(H^1、Tor、NSdepth、period)は未実装である(レビュー §3.4)。
- 第VIII部は measurement profile(定義2.1)、verdict discipline(定義3.1)、
  measurement packet(定義11.1)、finite measurement synthesis(定理12.1)として、
  tool が実装すべき計測仕様をすでに数学側で固定している。
  v0.4.0 はこの仕様の実装である。

## アウトカム

v0.4.0 完了時にユーザー(アーキテクチャ責任者としてコードベースを計測する人)が
得られる成果を、ユースケースとして定義する。各ユースケースは要求 ID への対応を持つ。

### UC1. 「どこも規約違反していないのに、全体が歪んでいる」を場所つきで言える(R3, R14)

状況: モジュール分割・層規約は各所で守られており、PR 単位のレビューも通る。
しかし統合後のコードベースに、設計意図と違う依存の癖が積み上がっている感覚がある。
witness counting はゼロを返すので、この感覚を裏づける計測がなかった。

v0.4.0 の出力: Čech evaluator が `H^1` の `measured_nonzero` を返し、
cocycle representative と「どの context 対の貼り合わせで mismatch が起きたか」を
source refs 付きで示す。

アウトカム: 「局所的にはすべて合法だが、貼り合わせが壊れている」を、
感覚ではなく場所つきの計測結果として指摘できる。これは古典読みでは
原理的に見えない情報であり、v0.4.0 の存在意義そのものである。

### UC2. 修復計画を「最小セット候補+下界」として受け取る(R4, R6)

状況: 障害が多数あり、どこから手を付けるべきか優先度がつかない。
障害一覧はあっても「何個直せば全体が消えるか」が分からない。

v0.4.0 の出力: Alexander dual から minimal repair hitting sets
(「この atom 集合に触れれば forbidden support 族がすべて消える」候補の列挙)、
および essential repair lower bound(「これ未満の修正量では消えない」下界)。

アウトカム: 「最低 n 箇所の修正が必要、最小候補セットは k 通り」という形で
リファクタ計画を立てられる。候補は修復の意味論ではなく組合せ的候補である
(原則5.3)が、計画の出発点としては十分機能する。

### UC3. 新しいポリシーの導入前に、既存ポリシーとの構造的衝突を知る(R5)

状況: 新しい law(例: layering 規約の強化)を導入したい。既存の law 群と
原理的に両立するか、導入後に矛盾だらけになるかを事前に知りたい。

v0.4.0 の出力: LawConflict (monomial Tor) が law ideal 対の衝突を計算し、
衝突が載る witness 変数と context を support として示す。
common ambient が構成できない場合は `not_computed` を返し、
意味のない比較を黙って出さない。

アウトカム: 「このポリシー対は、この witness 上で構造的に衝突する」を
導入前に確認できる。ポリシー設計の試行錯誤が、導入後の手戻りから
導入前の計測に変わる。

### UC4. 「この障害は深い」を証明書として持てる(R4)

状況: ある障害について「表面的なパッチで消えるのか、設計レベルの修正が
必要なのか」をレビューで主張したいが、根拠が経験則しかない。

v0.4.0 の出力: Nullstellensatz certificate と NSdepth
(unlawfulness certificate の次数)。certificate の検証は有限代数なので、
見つかった certificate は経験則ではなく certified witness である。

アウトカム: 「この障害の証明書次数は高い=浅い修正では消えない」を
リファクタ提案の説得材料・優先度づけに使える。逆方向(certificate が
見つからないから lawful)は主張しない(R4 の verdict 対応)。

### UC5. アーキテクチャ負債の量を、合否と混ざらないスカラーで追う(R6, R7, R9)

状況: 「前より悪くなった気がする」をコミット間・期間で比較したいが、
障害の個数は粗すぎ、合否判定は二値すぎる。

v0.4.0 の出力: harmonic mass、distance-to-flatness、spectral gap、
period pairing 行列などの analytic reading。これらは structural verdict と
schema 上分離されているため、「値が小さい=合法」という誤読が型で防がれる。

アウトカム: 負債の量と分布を連続量として観察できる。ただし安定性定理
(レビュー T1)が証明されるまで、tool はトレンド・ノイズ耐性の claim を
生成しない(R13)。期間比較の解釈責任は当面ユーザー側に残る。

### UC6. CI で言い切れる合否ゲートを持てる(R9, R10, R11)

状況: 計測レポートがヘッジと non-conclusion の列挙で埋まると、
CI のゲート条件として機械判定できず、毎回人間が解釈する作業が発生する。

v0.4.0 の出力: conclusion-first summary(第一文が
`NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` のような肯定形結論)+
5値 verdict + CBI assumption ledger。

アウトカム: 「profile 内で H^1 障害なし、仮定台帳はこの通り」を
そのまま CI のマージ条件にできる。仮定が崩れたとき(`violated`)は
verdict が `not_computed` に落ちるので、ゲートが偽の安心を出さない。
ヘッジ文の解釈作業が消える。これが「境界の一括前払い」のユーザー側の姿である。

### UC7. ArchMap 作成から主観が減り、観測が再現できる(R1, R12)

状況: v1 の molecules は「どの atom をまとめて一つの分子と見るか」の判断が
作成者の主観に依存し、同じコードベースから人(または日)によって違う ArchMap が
できていた。計測結果の差が、コードの差なのか観測の差なのか切り分けられない。

v0.4.0 の出力: molecules は廃止され、contexts(有限 poset)と covers は
source-grounded な構造観測になる。extractionDoctrineRef の必須化と
normalize 決定性の CI 検査により、同一の ArchMap 入力からはバイト同一の
normalized ArchMap が機械的に保証され、doctrine が違う ArchMap 同士の比較は
入力検証で拒否される。

アウトカム: 観測の主観が混入しうる場所が「doctrine の宣言」一点に隔離される。
doctrine を固定して観測をやり直せば、計測結果の差分を「コードが変わった」に
帰着して読める。観測のやり直し・将来の自分による再現・計測履歴の比較が成立する。

### ユースケース横断の共通アウトカム

```text
v0.3.0 まで:
  多数の計測座標 + 慎重な境界注記
  -> 解釈は毎回ユーザーの仕事。

v0.4.0:
  profile 宣言 + 仮定台帳を前払い
  -> 結論は profile 内で言い切り。
  -> 解釈の仕事は「台帳の仮定を受け入れるか」の一点に集約される。
```

## 設計原則: 境界の一括前払い

境界(coverage、exactness、profile 相対性)は AG 本文の核心だが、
すべての結論文に境界注記を付けると、tool は何も言い切れなくなる。
v0.4.0 は次の規律でこの緊張を解消する。

```text
boundary is paid once, at input contract time:
  ArchMap v2 + MeasurementProfile + LawPolicy v2 が境界を宣言する。
  CBI assumption ledger が仮定の checked / assumed を記録する。

conclusions are unconditional inside the profile:
  ledger 記録後の結論は、肯定形で言い切る。
  結論文にヘッジ・but 節・non-conclusion 列挙を入れない。
```

この規律が成立する根拠は第VIII部の verdict discipline である。
`unmeasured` と `unknown` が `measured_zero` から型として分離されている
(原則3.2 Verdict Boundary)からこそ、`measured_zero` は profile 内で
無条件の主張として言い切れる。境界を気にして結論を弱めるのではなく、
境界を型に押し出して結論を強くする。

既存の Wittgenstein 境界(`docs/tool/guideline.md`)はそのまま引き継ぐ:
non-conclusions は metadata であり、本文は結論先行。
語れない領域は短い silence boundary として扱い、失敗・残タスク扱いしない。

## 要求

### R0. v0.4.0 を Algebraic Geometry Measurement Release として定義する

v0.4.0 の優先順位は次である。

```text
AG invariant evaluators (H^1 / Tor / period / Laplacian)
  > finite poset site input contract (ArchMap v2)
  > measurement profile / verdict discipline
  > CBI assumption ledger
  > summary / viewer 追従
  > review workflow polish (v0.7.0 以降)
```

採用基準: 各計測は AG 本文の Definition / Theorem / Certified bounded inference に
対応行を持ち、finite measurement regime(第VIII部 定義4.1)の中で有限計算に落ちる。
定理候補(theorem candidate)にのみ依存する読みは R13 の gating に従う。

### R1. ArchMap v2: finite poset site を一次入力にする

`archmap/v2` は、source-grounded Atom map に finite poset site の観測を加えた
一次入力とする。primary input は次である。

```text
sources:    v1 と同じ source inventory(kind / path / symbol / line)。
atoms:      v1 の atom record に subject / axis decoration を必須化する。
            support(F) / F|x の計算(第I部)に必要な座標を欠落させない。
contexts:   architecture context の有限 poset。各 context は atom 部分族への
            明示的所属と、poset 順序(restriction 方向)を持つ。
            v1 の molecules は contexts の特殊ケース(離散 poset)として吸収し、
            primary field としては削除する。
covers:     selected coverage 候補。各 cover は contexts の有限族であり、
            source refs に接地する。U-adequacy は ArchMap では主張せず、
            R10 の ledger で checked / assumed として扱う。
```

境界規律: contexts / covers は「codebase がどう分割されているか」の観測であり、
何を測るかの選択(係数、witness family、verdict predicate)は持たない。
それらは R2 の MeasurementProfile の責務である。
private / unavailable / out-of-scope evidence が primary JSON に入らない原則は
v1 から変更しない。

### R2. MeasurementProfile を first-class artifact にする

`measurement-profile/v1` を新設し、AG 本文 定義2.1 の selected `M` を
宣言する artifact とする。少なくとも次を固定する。

```text
siteRef / coverRef:        ArchMap v2 の contexts / covers への参照。
coefficient:               係数体または環 k_M(明示表示)。
effCoeff:                  selected kernel / image / quotient / ideal-membership
                           手続きの識別子(EffCoeff_M)。
witnessFamily:             selected witness variables E(law -> square-free 変数の対応)。
resolutionSelector:        Tor 計算に使う resolution(Koszul / Taylor / Scarf / monomial)。
domain / zeroPredicate /
nonZeroPredicate / certSelector:
                           Dom_M, Zero_M, NonZero_M, Cert_M。
verdictDiscipline:         5値 verdict の判定規律(R9)。
```

LawPolicy v2 は v1 の selector 構造(policy pack / evaluator / basis / scope /
severity)を保ち、`measurementProfileRef` を必須 field として追加する。
計算規則が evaluator registry に属する分担は変更しない。
`M` を固定して初めて measurement statement が意味を持つ(定義2.1)ことの
tool 側対応物として、profile 未指定の AG evaluator 実行は validation error とする。

### R3. Čech obstruction cohomology evaluator

selected cover 上の Čech cohomology を typed evaluator として実装する。

- `H^0(U_M, Ob_M)`、`H^1(U_M, Ob_M)`、および selected `H^2` を有限線形代数で計算する
  (第IV部、第VIII部 定理4.2)。
- nonzero class には cocycle representative を返し、その support
  (どの context 対 / 三つ組で mismatch が起きたか)を source refs 付きで出力する。
- alternating 規約は evaluator 内で明示的に固定し、schema に記録する
  (第II部 命題7.2C の規約明示要求への tool 側対応)。
- Čech 計算が sheaf cohomology を測ったことになる acyclicity 条件は
  本 release では証明しない。`H^n(U_M, Ob_M)` は cover-relative reading として
  schema 上で命名し、ledger に `leray: assumed` を記録する(R10)。
- 付録 B.8(Atom-Family-To-Geometry Toy Reading)の B.8.2 Čech Mismatch を
  golden fixture として再現する。

### R4. Square-free repair evaluator: I_Ob / Stanley-Reisner / Alexander dual / NSdepth

square-free witness regime(第VIII部 定義5.1)の計測経路を実装する。

- selected witness variables E から square-free obstruction ideal `I_Ob^U` を構成し、
  minimal forbidden supports を列挙する(付録 B.4)。
- Stanley-Reisner 複体 `Delta_U` を構成し、その被約 homology を有限計算する。
- Alexander dual から **minimal repair hitting sets** を列挙する
  (第VIII部 定理5.2 Stanley-Reisner / Alexander Dual Repair Theorem)。
  これは engineer-facing には「この obstruction 族を消す最小修復セット候補」である。
- repair hitting set は修復の組合せ的下界・候補であり、修復の意味論ではない
  (原則5.3)。出力は repair-route 候補 reading として既存 operation geometry の
  diagnostic 位置づけに合わせる。
- Nullstellensatz certificate と NSdepth(第III部 定義7.2B)を計測する。
  verdict 対応は非対称である: 選んだ最大次数 D 以下で certificate が見つかれば、
  その検証は有限代数なので unlawfulness を `measured_nonzero` として certified に
  出せる。D 以下で見つからない場合の verdict は `unknown` であり、
  lawfulness を結論しない —— 完全性方向は定理候補 7.2A Architecture
  Nullstellensatz にとどまるためである。
- NSdepth は「直せなさの証明書の深さ」reading であり、repair cost 下界との橋
  (レビュー T7)は theorem candidate なので R13 gating に従う。

### R5. LawConflict (monomial Tor) evaluator

law universe 対の衝突を derived 不変量として計測する。

- selected law ideal 対に対し、monomial Tor `LawConflict_i = Tor_i` を
  Taylor / Scarf resolution で計算する(第V部 命題5.5、第VIII部 §9)。
- common ambient pair(定義9.1)を入力前提とする。common ambient が
  profile から構成できない場合、verdict は `not_computed` とし、
  理由 `no_common_ambient` を記録する。ambient なしの conflict 比較は出さない
  (原則9.3 No Ambient, No Conflict Comparison)。
- conflict class の support(どの witness 変数・どの context に衝突が載るか)を
  source refs 付きで出力する。
- flat base change による安定性(定理候補9.2)は R13 gating に従う。

### R6. Cellular sheaf Laplacian / Hodge evaluator

既存 curvature / spectrum 系 reading を AG 基盤へ載せ替える。

- cellular measurement model(第VIII部 定義8.1)上で sheaf Laplacian `L_n` を構成し、
  finite Hodge decomposition(定理8.5)で cochain を
  exact / harmonic / coexact に分解する。
- harmonic mass、distance-to-flatness(定義8.3)、spectral gap(定義8.8)、
  curvature transfer spectrum(定義8.9)を analytic reading として出力する。
- harmonic debt minimality(定理8.6)と essential repair lower bound(系8.7)を
  「この cohomology class を消すのに必要な最小修正量の下界」reading として出力する。
- near-flat(analytic 値が小さい)を lawful と読まない(原則8.4)。
  structural verdict と analytic reading の分離(R9)をここで最も厳格に適用する。
- v1 の curvature / transfer spectrum 系 reading(`architecture-distance.json` の
  curvature geometry family)は、この evaluator の出力で置き換える。旧実装は残さない。

### R7. Period pairing / Stokes audit evaluator

- 有限 poset homology model 上の strict period(第VII部 定義5.2A、付録 B.6)を、
  formal cycle basis に対する period pairing 行列として計算する。
- Stokes audit identity `<d omega, gamma> = <omega, boundary gamma>` を
  数値検査として実装し、計測パイプライン自体の self-check とする
  (定理12.3 AAT-GAGA の period accounting 条項)。
  audit 不一致は計測結果ではなく evaluator 実装バグとして fail-fast にする。
- pairing の well-definedness(比較同型)は未証明(レビュー §3.2)なので、
  period reading は model-relative analytic reading として命名し、
  ledger に `period_comparison: assumed` を記録する。

### R8. Support-localized transfer evaluator

- support-localized repair path(第VIII部 定義10.1)に対する
  transfer measurement pairing(定義10.2)と transfer residue を計算する
  (定理10.3 Support-Localized Transfer)。
- Wasserstein transfer cost(定義10.6)を analytic reading として出力する。
- transfer reading から「修復が副作用を持たない」を結論しない(原則10.5)。
  transfer lower bound(定理候補10.4 / 10.7)は R13 gating に従う。

### R9. 5値 verdict discipline を全 evaluator に強制する

全 AG evaluator の structural verdict は次の5値に限る(第VIII部 定義3.1)。

```text
measured_zero / measured_nonzero / unmeasured / unknown / not_computed
```

- 各 verdict は VerdictData(InScope / Zero / NonZero / MethodStatus / CertRef)を
  添えて出力する。`Zero_M` と `NonZero_M` は論理的補集合として実装しない。
- `unmeasured != measured_zero`、`unknown != measured_nonzero`、
  `not_computed != unmeasured` を schema validation で強制する
  (原則3.2)。v1 の blocked / partial / unmeasured 状態系はこの5値へ統合する。
- structural verdict と analytic reading(distance、mass、spectrum、barcode、
  residual norm)を schema 上の別 field に分離する(定義3.3)。
  analytic 値から structural verdict を導出する evaluator code path を禁止する。

### R10. CBI assumption ledger: 仮定の checked / assumed 台帳

AG 本文の Certified bounded inference 定理は、それぞれ明示の仮定ブロックを持つ
(v0.4.0 が使うのは定理4.2、5.2、8.5、8.6、10.3、12.1、12.3)。v0.4.0 は実行ごとに、
使用した CBI 定理の仮定を proof-carrying ledger として出力する。

```text
assumptionLedger:
  theoremRef:    AG 本文の定理ラベル(例 "part8/4.2")。
  assumption:    仮定項目(例 "finite site", "U-adequate cover",
                 "square-free witnesses", "common ambient")。
  status:        checked / assumed / violated。
  checkedBy:     checked の場合、検査手続きの識別子と入力 refs。
  assumedBy:     assumed の場合、宣言元(profile / law-policy / archmap author)。
```

- tool が有限検査できる仮定(site の有限性、witness の square-free 性、
  係数の明示表示、resolution の有限性)は `checked` にする。
- 決定手続きを持たない仮定(U-adequacy、exactness、Leray acyclicity、
  period 比較同型)は `assumed` にし、宣言元を記録する。
- `violated` が1件でもあれば、当該定理に依存する verdict は `not_computed` に落とす。
- ledger は packet の `assumptions` 区画(R11)に入る。結論文には反映しない。
  これが「境界の一括前払い」の実装である: 仮定は台帳で機械可読に持ち、
  結論は ledger-relative に言い切る。

### R11. archsig-measurement-packet/v1 と summary / viewer 追従

ArchSig の一次出力 artifact を `archsig-measurement-packet/v1` とし、
AG 本文 定義11.1 AAT Measurement Packet の6区画に準拠させる。

```text
profile:            selected M の全 record(R2 の解決結果)。
structuralVerdict:  R9 の5値 verdict 一覧。
computedInvariants: H^n、Tor_i、generators、minimal forbidden supports、
                    repair hitting sets、dimensions、ranks、representatives。
analyticReadings:   distance、harmonic mass、spectrum、period 行列、
                    residual norm、repair cost、Wasserstein transfer cost。
assumptions:        R10 の assumption ledger。
nonConclusions:     unselected laws、unmeasured support、
                    unprovided coefficient data、undecided predicates。
```

- summary(`archsig-analysis-summary/v2`)と atom viewer data は
  measurement packet から再構成する。summary は conclusion-first を維持し、
  第一文は profile 内の肯定的結論
  (例: `NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE`)とする。
- 公開 summary / viewer surface の命名は architecture distance 系の
  engineer-facing 語彙を保ち、AG 数学節名を一次 label にしない。
  packet 内部 field は AG 本文の語彙に揃える。
- FieldSig handoff は measurement packet を読む形へ更新する。FieldSig 側の
  forecast / governance 設計は変更しない。

### R12. ArchMap determinism / A8 invariant

公理 A8 Essential Uniqueness(第I部)の tool 側対応物として、
ArchMap の決定性を CI 検査可能な不変量にする。

- ArchMap v2 に `extractionDoctrineRef` を必須 field として追加する。
  doctrine は `(V, Γ, R, ρ, E, N)` の構成要素を識別する fingerprint を持つ。
- `normalize` は決定的でなければならない: 同一 ArchMap v2 入力に対し、
  normalized output(ordering、id 採番、重複統合)はバイト同一とする。
  CI に同一入力二重実行の同一性検査を追加する。
- doctrine が異なる ArchMap 同士の比較・delta は、入力検証で
  理由コード `cross_doctrine_not_comparable` として拒否する
  (A8 の「一意性の相対化」の実装)。これは input validation error であり、
  R9 の5値 verdict に第6の値を追加しない。
- ArchSig は抽出器の健全性(source から Atom への対応の正しさ)を検査しない。
  検査するのは doctrine 固定下の決定性と doctrine 識別の明示のみである。

### R13. Theorem-candidate readings の gating

AG 本文で theorem candidate にとどまる読みは、certified 出力から分離する。

```text
candidate-regime readings (v0.4.0 で flag 付き analytic reading として許可):
  persistence / zigzag stability reading      (定理候補6.3 / 6.5)
  discrete Morse repair lower bound           (定理候補5.5)
  spectral hotspot reading                    (定理候補8.10)
  transfer lower bound                        (定理候補10.4 / 10.7)
  flat base change stability                  (定理候補9.2)

dropped from v0.4.0 (証明基盤が壊れているため):
  monodromy index / Mon_γ 系 verdict          (π1^AAT が ill-defined、レビュー §3.2 / T9)
```

- candidate-regime reading は packet の `analyticReadings` に
  `regime: "theorem-candidate"` flag 付きでのみ出力し、structural verdict を生成しない。
- 既存 monodromy / boundary holonomy 系 reading は v0.4.0 の出力から削除する。
  π1 の再構成(レビュー T9)が定理になった時点で再導入を別 PRD として扱う。
- 安定性定理(レビュー T1)が証明されるまで、計測値の摂動耐性は保証しない。
  summary はトレンド・ノイズ耐性の claim を生成しない。

### R14. Golden fixture: witness counting には見えず、H^1 には見える実例

AG 計測の存在意義を固定する識別 fixture を golden corpus に追加する。

- 古典読み(witness counting、cycle 数)では障害ゼロに見えるが、
  `H^1` の boundary residue が nonzero になる ArchMap v2 fixture を作る。
  局所的にはどの context でも law が満たされるが、
  restriction の貼り合わせで mismatch class が生じる構成
  (付録 B.8.2 の Čech mismatch パターンの拡張)。
- 期待出力: witness 系 reading は `measured_zero`、
  Čech evaluator は `measured_nonzero` + cocycle representative + support refs。
- 付録 B.3-B.8 の finite worked example(square-free ideal、monomial Tor、
  period pairing、verdict boundary)を end-to-end fixture として再現し、
  本文の数値と evaluator 出力の一致を test で固定する。

## スコープ

この PRD のスコープは次である。

- v0.4.0 を Algebraic Geometry Measurement Release として定義する要求。
- `archmap/v2`(sources / atoms / contexts / covers、subject-axis 必須化、
  extractionDoctrineRef)。
- `measurement-profile/v1` と LawPolicy v2 の `measurementProfileRef`。
- Čech cohomology / square-free repair / monomial Tor / sheaf Laplacian /
  period pairing / support-localized transfer の6 evaluator 族。
- 5値 verdict discipline と structural / analytic 分離。
- CBI assumption ledger(checked / assumed / violated)。
- `archsig-measurement-packet/v1` と summary / viewer / FieldSig handoff の追従。
- ArchMap determinism / A8 invariant の CI 検査。
- theorem-candidate gating と monodromy 系 reading の削除。
- 識別 golden fixture(witness-blind / H^1-visible)と付録 B worked example fixture。

v0.4.0 の実装設計で具体化するものは次である。

- 各 artifact の schema field 名と validation rule。
- evaluator registry への AG evaluator 登録形式と resolution selector の実装範囲
  (最低限 Taylor resolution、Scarf は optional)。
- 係数実装の範囲(最低限 有限体 F_2 と Q、EffCoeff 手続きは有限次元線形代数)。
- fixtures の v2 移行手順と削除対象の v1 fixture 一覧。
- `docs/tool/` 各文書(README、guideline、analysis packet 説明)の更新。

## Non-Goals

この PRD は次を目標にしない。

- v1 系 schema / packet / fixture との互換維持、migration tooling の提供。
- ArchSig を theorem prover にする。CBI ledger は仮定の記録であり、
  仮定の証明ではない。
- U-adequacy、exactness、Leray acyclicity、period 比較同型を tool が判定する。
- 安定性(摂動耐性)・単調性・識別力を保証する。対応する定理
  (レビュー T1 / T2 / T8)が証明されるまで、これらは theorem-candidate reading に
  とどまる。
- monodromy / boundary holonomy 系 verdict の継続提供。
- 抽出器(source -> Atom)の健全性・完全性の検査。A8 invariant は
  doctrine 固定下の決定性検査であり、抽出の正しさの検査ではない。
- Lean 形式化との接続。AG 定理ラベルの Lean 台帳登載は並行プロジェクトであり、
  tool の completion 条件にしない。
- refactor transport / functoriality 計測(第VIII部 定理7.3 系 evaluator)。
  certified だが本 release の問いに従属しないため、PR delta 計測とあわせて
  v0.5.0 以降の候補とする。
- Hochster 公式 / graded Betti 数 / lcm-lattice などレビュー B1 の拡張不変量
  (v0.5.0 以降の候補)。
- 第IX部 Evolution Geometry の時間方向計測(FieldSig / SFT 層の主題)。
- repair hitting set からの自動修復・修復安全性の結論。
- analytic reading(harmonic mass、distance 等)からの structural verdict 導出。
- tool quality、summary UX、review workflow、packaging の完成度
  (v0.7.0 以降の主題)。

## Acceptance Criteria / 完了条件

- 問いが冒頭に立てられ、要求・計測の採否を問いで読む規律が明記されている。
- v0.4.0 が Algebraic Geometry Measurement Release であり、後方互換を持たず、
  v1 系 surface を削除する方針が明記されている。
- v0.4.0 の優先順位が、AG invariant evaluators、input contract、
  profile / verdict discipline、assumption ledger、summary / viewer 追従、
  workflow polish の順で定義されている。
- ユーザー目線のアウトカムがユースケース(UC1-UC7)として定義され、
  各ユースケースが要求 ID への対応を持つ。
- `archmap/v2` が sources / atoms(subject・axis 必須)/ contexts(有限 poset)/
  covers を primary input とし、molecules を primary field から削除している。
- `measurement-profile/v1` が定義2.1 の構成要素(site / cover / coefficient /
  EffCoeff / witness family / resolution / Dom / Zero / NonZero / Cert / verdict)を
  宣言でき、profile 未指定の AG evaluator 実行が validation error になる。
- Čech evaluator が H^0 / H^1 / selected H^2 と cocycle representative、
  mismatch support refs を出力し、付録 B.8.2 fixture を再現する。
- square-free evaluator が I_Ob^U、minimal forbidden supports、Delta_U、
  Alexander dual repair hitting sets、NSdepth certificate を出力し、
  certificate 不在時に lawfulness を結論せず `unknown` を返し、
  付録 B.3 / B.4 worked example を再現する。
- Tor evaluator が common ambient pair を前提に LawConflict_i を出力し、
  ambient 不在時に `not_computed` + `no_common_ambient` を返し、
  付録 B.5 worked example を再現する。
- Laplacian evaluator が Hodge 分解、harmonic mass、distance-to-flatness、
  spectral gap、curvature transfer spectrum、essential repair lower bound を
  analytic reading として出力する。
- period evaluator が strict period pairing 行列を出力し、Stokes audit identity の
  数値検査を実装し、audit 不一致が evaluator error として fail する。
  付録 B.6 worked example を再現する。
- transfer evaluator が transfer residue と Wasserstein transfer cost を出力する。
- 全 AG evaluator の structural verdict が5値に限定され、
  analytic reading と schema 上分離され、verdict 混同の validation が存在する。
- assumption ledger が実行ごとに theoremRef / assumption / status /
  checkedBy / assumedBy を出力し、有限検査可能な仮定が `checked`、
  それ以外が `assumed` になり、`violated` 時に依存 verdict が `not_computed` へ落ちる。
- `archsig-measurement-packet/v1` が定義11.1 の6区画を持ち、
  summary が conclusion-first の肯定的結論を第一文に出す。
- ArchMap v2 normalize の決定性検査(同一入力二重実行のバイト同一性)が
  CI に存在し、cross-doctrine 比較が `not_comparable` として拒否される。
- theorem-candidate readings が `regime: "theorem-candidate"` flag 付き
  analytic reading に限定され、structural verdict を生成せず、
  monodromy 系 reading が出力から削除されている。
- witness-blind / H^1-visible 識別 fixture が golden corpus に存在し、
  witness 系 `measured_zero` と Čech `measured_nonzero` の共存を test が固定している。
- Non-Goals が、互換維持、theorem proving、adequacy 判定、安定性保証、
  抽出健全性、Lean 接続、自動修復、analytic からの verdict 導出を明確に除外している。
- `docs/tool/README.md` の source-of-truth boundaries と
  `docs/tool/guideline.md` の境界記述が v2 chain に合わせて更新されている。
