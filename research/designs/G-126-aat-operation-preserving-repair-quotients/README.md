# G-126：操作と観測を保つ修復商の実装設計

[固定GOAL A–E](../../goals/G-126-aat-operation-preserving-repair-quotients.md)を、
既存の商・readingのAPIと新規の操作合同関係・有限手続きへ分解する。
以下の新規宣言名とファイル名は設計上の提案であり、Leanでの証明を表すものではない。
宣言の再利用条件は[再利用対応表](reuse-map.md)、計算と費用の構成は
[有限構成](finite-construction.md)に置く。

## 1. 再利用と新規構成

| 部分 | 再利用するもの | 新しく構成するもの |
| --- | --- | --- |
| A：合同関係 | mathlibの`Setoid`、完全束、同値閉包 | 単項操作族への安定性、生成合同`generated`、将来の観測同値`behavior` |
| B：分類 | 商のlift、核による因子化、全射の核の商との同型 | 操作・観測保存の接続、修復商の同型類と区間の順序同型 |
| C：合成 | `Setoid.correspondence`、商の商の同型 | 操作安定性への制限、要求の像から生成した合同の同定、逐次商の整合性 |
| D：計算 | 有限対の濃度、`DFA.evalFrom_split`による語の短縮 | 両端の表計算、失敗の語、有限商の表、同じプログラムの正確性と費用 |
| E：Law | `Reading`、`FiniteLawFamily`、`jointKernelReading`、`computedReading`の核の定理 | 操作降下との同値、経路対からの要求生成、実行可能な出力との接続 |

実装先は`research/lean/ResearchLean/AG/OperationRepair/`、
名前空間は`AAT.AG.OperationRepair`とする。G-103のreadingや標準解像度を再定義せず、
G-126に必要な操作保存条件を加える。G-124の有限延長プログラムは扱う入力・出力が異なるため、
この手続きの実装には用いない。

## 2. 基本データとAの構成

`OperationSystem S E`は`step : E → S → S`を持つ。
観測`observe : S → O`と要求`R : S → S → Prop`は別の引数とする。
語の評価`eval s w`は`List.foldl (fun s e => step e s) s w`で定義し、
`eval s (u ++ v) = eval (eval s u) v`を基本式とする。
数学的な構成は有限性なしで成立する部分から証明し、有限性・等号判定・列挙はDで使う。
`O`の有限性、操作による観測値の不変性、`Nonempty S`は入力に加えない。

`OperationCongruence T`は、`Setoid S`と
`∀ e x y, r x y → r (T e x) (T e y)`の組とする。
順序は基底の`Setoid`の包含を使う。任意の交わりが安定なことから完全束を構成し、
任意の和については`Setoid.sSup_eq_eqvGen`と同値閉包の帰納法により安定性を証明する。
これにより忘却写像がinfとsupを保つことも得る。
二項乗法用の`Con`に人工的な乗法を入れる方法は採らない。

`generated T R`は、`R`を含む操作合同関係のinfとする。
中心APIは`generated_le_iff : generated T R ≤ c ↔ R ⊆ c`であり、
包含、単調性、冪等性、要求の合併とjoinの交換はこの最小性から導く。
有限計算の閉包も、この同じ`generated`と等しいことを証明する。

`behavior T observe`の基底は
`Setoid.ker (fun x => fun w : List E => observe (eval x w))`とする。
語の先頭に操作を加える式から操作安定性を示す。空語から`behavior ≤ ker observe`を得る。
任意の操作合同`c ≤ ker observe`について語長帰納法で`c ≤ behavior`を示し、
最大性のAPIとする。ここでGOALの`θ_R`を`generated T R`、`β_o`を`behavior T observe`へ対応させる。

## 3. Bの分類と普遍性

`RepairQuotient T observe R`は既存の`Reading S`に、商上の操作・観測と
GOAL Bの可換式・要求同一視を加えたものとする。
対象の条件として与える全射性は`Reading.surjective`を使う。
一方、標準商を返す構成では全射性、操作・観測の降下、要求同一視をそれぞれ証明する。
商の有限性は`Finite.of_surjective`から導く。

任意の商先`Q : Type v`への全射についても、核からの標準商との同型を先に示す。
同型類をまとめる型には`Reading S`の宇宙を使い、この標準化で任意の`Q`を扱う。
一般の因子化先`X : Type v`を同じ宇宙や有限型に制限しない。

`RepairHom q q'`はGOAL Bの全写像を持ち、`f ∘ q = q'`、操作・観測の保存を記す。
全射性による外延性から射の一意性、`q'`の全射性から射の全射性を示す。
恒等と合成を定義し、次の順で分類する。

1. 修復商の核に操作安定性を与え、`generated ≤ ker q ≤ behavior`を証明する。
2. 区間内の合同`c`から、`Quotient c`上へ操作を`Quotient.map`、観測をliftで降ろす。
   `generated ≤ c`から要求同一視を得る。
3. `Setoid.quotientKerEquivOfSurjective`で`S / ker q ≃ q.Target`を作り、
   元の`S`上で評価して操作・観測の保存を証明する。
4. 二つの修復商が`S`上で同型であることと核の一致を同値にする。
   同型類は実際の構造保存同型の存在で定義し、この同値を使って順序を降ろす。
5. `Nonempty (RepairHom q q') ↔ ker q ≤ ker q'`を証明し、
   同型類と`Set.Icc generated behavior`の`OrderIso`を構成する。

既存readingの向きは`q'.FactorsThrough q`、同値な順序は`q'.CoarserThan q`である。
射`q → q'`に対してこの向きを保つ。

存在条件の四つの同値はAの最小性・最大性から得る。
両端の初・終性は区間の最小・最大と射の一意性から導く。
任意の構造保存写像`h : S → X`の普遍性は、`ker h`の操作安定性と
`R ⊆ ker h`を証明して`Setoid.liftEquiv`を使う。
liftの操作・観測保存は代表元で示し、一意性は商写像の全射性で示す。
この部分は`Reading.Factors`の同一宇宙の型制約に依存させない。

## 4. Cの合成と自然性

有限族について、`generated_le_iff`を両辺に適用して合併とjoinの等式を証明する。
各項が`behavior`以下であることとjoinが以下であることから、修復可能性の同値を得る。
空族では`generated ∅ = ⊥`とし、元の操作・観測を持つ恒等商に対応させる。

逐次商では、まず`c₁ = generated T R₁`、`c = c₁ ⊔ generated T R₂`と置く。
`Setoid.correspondence c₁`を操作合同関係へ制限し、次の同定を証明する。

```text
generated (quotientOperations c₁) (Relation.Map R₂ q₁ q₁)
  = kernel (S/c₁ → S/c)
```

左辺は第一の商上で要求の像から新たに生成する合同である。
`Setoid.quotientQuotientEquivQuotient`の入力は右辺の核であるため、
この同定を済ませてから既存同型を適用する。
同型が操作・観測と可換なことは`S`の各元で確認する。
有限族は順序付き列と二分木で逐次商を表し、帰納的に合併の商と比較する。
順序変更・括弧変更の各比較は`S`上で可換な唯一の同型なので、
比較同型の合成が直接の比較に一致する。像の要求は常にその段階までの合成商写像で作る。

入力間の写像`h`については、次の二つを別々に示す。

- 下端：先の系の生成合同を`Setoid.comap h`で引き戻すと操作合同になり、
  元の要求を含む。最小性から`h`が生成合同を保存する。
- 上端：`h (eval x w) = eval' (h x) w`を語長帰納法で示し、
  観測保存を使って`behavior`の保存を得る。

両端の誘導写像は商のliftとし、元の状態での評価式をsimp補題にする。
下端から上端への写像との平方、恒等、合成、入力同型に対する逆写像は、
この評価式と商写像の全射性で証明する。`h`の単射性・全射性は仮定しない。

## 5. EのLawと経路要求

既存の`FiniteLawFamily S`から`observe x := fun law => laws.eval law x`を作る。
関数外延性と`jointKernel_kernel_iff`により、その核が`jointKernelSetoid`に一致する。
`FiniteLawFamily.adequate_iff_kernel`を使って、Bの修復商と
操作降下・adequacy・要求同一視を満たす既存readingの対応を作る。

`behavior ≤ ker observe`から`qβ`のadequacyを導き、
`jointKernel_coarser_of_adequate`と`jointKernel_factorsThrough_of_adequate`を適用する。
さらに、`ker qL`の操作安定性からAの最大性、逆方向には`behavior`の安定性を用い、
`ker qL = behavior`と操作安定性を同値にする。
各操作の降下は`qL.Factors (qL.read ∘ T e)`で表し、
`Reading.factors_iff_kernel`から安定性との同値を得る。

`E`が空ならすべての語が空語であり、`behavior = ker qL`となる。
Bの核同型から標準解像度との一意の同型を得る。
有限出力についても核一致を介して接続し、`computedReading`と
`computed_kernelEquivalent_jointKernel`をG-103の有限表示との比較に再利用する。
一般の`E`で`computedReading laws`が計算するのは現在のLawの核であり、
将来の操作を含む`behavior`との一致には前述の操作安定性が必要である。

有限経路対は明示リストとして与え、各`x`と経路対を評価して要求表`R_P`を作る。
商への語作用の可換式により、`R_P`の同一視と商上の全経路等式を同値にする。
逆向きには商写像の全射性を使い、代表元だけの等式を全商状態の等式にする。
これをBの分類、Dの実行結果、Cの誘導写像に接続する。
Law族・経路対の入力からの表生成費用は[有限構成 §6](finite-construction.md#6-law経路入力の前処理)で扱う。

## 6. モジュールと証明の依存順

以下は責務の分割であり、既存宣言の再包装だけを独立moduleにしない。

| 順序・ファイル案 | 主な新規宣言・証明 | 依存・受入条件 |
| --- | --- | --- |
| 1 `Basic.lean` | `OperationSystem`、語作用、`OperationCongruence`、完全束 | Setoidの束と操作安定性の一致。空の型を許す |
| 2 `Endpoints.lean` | `generated`、`generated_le_iff`、`behavior`、最大性 | 1。GOAL Aの二端を元の入力から構成 |
| 3 `Classification.lean` | `RepairQuotient`、`RepairHom`、`repairOrderIso`、存在同値、普遍性 | 2とReading。任意の商・任意の因子化先を扱う |
| 4 `Composition.lean` | `generated_union`、`sequentialRepairEquiv`、整合性、両端の誘導写像 | 3。像から生成した合同を同定して第三同型を使う |
| 5 `FiniteTables.lean` | 番号付き入力、表操作、費用付きループ、有限出力型 | 数学的な入力との対応。答えや正確性の証明を入力に含めない |
| 6 `FiniteClosure.lean` | 下端の閉包計算、停止、`computedLower_eq_generated` | 2・5。単なる同値閉包でなく操作安定性まで得る |
| 7 `FiniteBehavior.lean` | 上端の語探索、短い分離語、`computedUpper_eq_behavior` | 2・5とDFAの短縮。元の要求対と語を返せる |
| 8 `FiniteConstruction.lean` | 商表・因子化の生成、`runRepair`、成功・失敗の完全性 | 3・6・7。両端の分割と成功または失敗を同じ入力から計算 |
| 9 `Cost.lean` | 各ループの費用、`runRepair_cost_le`、Big-O系 | 8。実行関数の費用射影に固定多項式の上界 |
| 10 `LawBridge.lean` | reading対応、操作降下条件、経路要求、有限出力との一致 | 4・8とCanonicalResolution。GOAL E全文 |
| 11 `Examples.lean` | GOALの三例、空入力・空操作の評価 | 9・10。同じ`runRepair`と一般分類へ接続 |

主な証明鎖は`Basic → Endpoints → Classification → Composition`と、
`FiniteTables → (FiniteClosure, FiniteBehavior) → FiniteConstruction → Cost`である。
`LawBridge`と`Examples`が両者を接続する。

## 7. 検証と受入条件

一般定理の受入条件はGOAL A–Eに従う。実装時には各定理を
`research/reports/G-126-aat-operation-preserving-repair-quotients.md`へ対応させる。
とくにBの順序同型、Cの逐次商の同定、Dの実行関数との一致・費用、
Eの既存readingとの対応を、それぞれ証明の宣言へ結びつける。

固定例では次を一般APIと同じ手続きで検証する。

- 四状態例：下端の三ブロック、上端の二ブロック、区間の元がちょうど二つであること、
  二つの修復順序の商写像、Lawの因子化。
- 三状態例：下端は全関係、上端は等号関係、元の要求対を一文字で分離する出力、
  空語では分離できないこと、`qL`への操作降下の不成立。
- 経路例：`(ε,T)`から生成した要求の下端が上端と一致し、二状態の商で`T = id`、Lawは非定値。
- 端の条件：`n=0`、`m=0`、空の要求族、空のLaw族。因子化では非全射な入力写像も扱う。

新moduleは`research/lean/ResearchLean/AG.lean`と
`research/lean/research-modules.txt`へ登録し、対象fileを指定して確認する。例：

```bash
research/lean/check_research_modules.sh --focused ResearchLean/AG/OperationRepair/Examples.lean
```

これは実装・登録後の対象検証例である。必要な依存moduleだけを親が限定して準備し、
Research全体・aggregate・全file loopのbuildは行わない。
主要定理には既存の`#assert_standard_axioms_only`を適用し、実行関数には
非計算的な代表元選択を入れない。有限実験の結果と一般のLean証明は別の証拠として扱う。
