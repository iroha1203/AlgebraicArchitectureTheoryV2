# AAT代数幾何版 Lean形式化 PRD-4: 第IV部 Obstruction Cohomology

対象本文: [第IV部 Obstruction Cohomology](algebraic_geometric_theory/part_4_obstruction_cohomology.md)

先行PRD:
[PRD-1 第I部](lean_ag_part_1_atoms_objects_laws_prd.md) /
[PRD-2 第II部](lean_ag_part_2_sites_sheaves_prd.md) /
[PRD-3 第III部](lean_ag_part_3_law_algebra_lawful_locus_prd.md)

## 問い

第III部の lawful locus の上で、局所の合法性は大域の合法性か。
そうでないなら、その差は

```text
H^1(𝒰, Ob_U)
```

として機械検証できるか。すなわち、

- 非零の具体的 cocycle `[g] != 0` が local lawful sections の貼り合わせを
  阻むこと(定理7.1 Local Flatness Gap)
- effective abelian torsor の下で `[g] = 0` が大域 lawful section を
  与えること(定理11.1 Cohomological Flatness Criterion)

が、Lean 上で sorry なしに証明できるか。

採否規律: Čech obstruction complex の構成と、CBI 定理6本
(7.1 / 9.2 / 11.1 / 12.2 / 12.4 / 13.2)およびその系(11.2 / 12.3 / 12.5)に
寄与する定義・命題だけを形式化対象に採る。寄与しない要素(例、原則、意味の
節)は対象外とする。実装中に、CBI 定理の仮定ブロックが不足している、または
第II部・第III部の形式化と接続できないことが見つかった場合、それは本文または
本PRDの欠陥であり、ループを停止して報告する。

## 中心方針

PRD-1〜3 で確立した方針を引き継ぐ(塔を下から積む / 忠実性契約 /
`Formal/AG` 新規実装 / `axiom`・`sorry` 禁止 / Mathlib 二段橋 / 台帳統合 /
先行PRD依存の blocked 規律)。

本PRDで新たに加わる方針が四つある。

**(1) PRD-2 への約束の履行。** PRD-2 は命題7.2C のために有限 poset 版
Čech complex を先行定義した。本PRDは一般の AAT site 上の cover-relative
Čech complex を定義し、有限 poset regime での両者の一致を定理として証明する。
この一致定理は本PRDの完了条件である。

**(2) cover-relative を一次とする記法規律。** 主たる作業対象は
`H^n(𝒰, Ob_U)`(cover-relative Čech cohomology)である。`H^n(X, Ob_U)` は、
本文どおり「選ばれた topology と係数が Čech で sheaf cohomology を計算
できる場合、または refinement system を明示した場合」の条件付き記法として
定義し、無条件の sheaf cohomology 理論を新規開発しない。

**(3) derived 成分は placeholder に留める。** 定義2.4 の標準 obstruction
package のうち、`Def_U = I_U` と `ConDef_U = I_U/I_U²`(conormal、Mathlib
`Ideal.Cotangent` への橋)は形式化する。`DerOb_U(M) = Ext¹(L_{Flat/X}, M)` は
余接複体を要するため、opaque な宣言(型シグネチャのみ)に留め、中身は
第V部の PRD に委ねる。定義8.3 の derived category Mayer-Vietoris triangle も
同様に、Čech 水準の具体的構成(2-chart cover の connecting homomorphism)で
置き換え、triangle そのものは形式化しない。

**(4) 定理候補の statement は低次完全列の形に限定する。** 定理候補10.4
(Mayer-Vietoris spectral sequence)と14.2(Leray five-term)の statement は、
スペクトル系列の一般機構を立てずに表現できる低次五項完全列の形で形式化
する。スペクトル系列そのものの Lean 化はスコープ外であり、行わない。

## 背景

- PRD-1〜3 はマージ済みで、codex の prd-loop が順次実装中である。本PRDの
  実装は PRD-2(ArchCtx、J_U、overlap、有限 poset regime、有限版 Čech)と
  PRD-3(`O_X^U`、`I_Ob^U`、`Flat_U(X)`、lawful section)の成果物に依存する。
  依存先未実装の要求は `blocked` として台帳に記録する(R0)。
- 第IV部は ArchSig v0.4.0 との接続が最も濃い部である: Čech evaluator(R3)は
  本PRDの `H^n(𝒰, Ob_U)`、period / Stokes audit(R7)は定理13.2、golden
  fixture(R14「witness counting には見えず H^1 には見える実例」)は
  例9.3/9.4 の擬円周 boundary model がそれぞれ理論側の対応物である。
- 定理12.2 / 12.4 / 13.2 は有限 poset regime の主張であり、中身は有限次元
  線形代数と組合せ論である。第VIII部(PRD-5)の計測定理群は本PRDの定理を
  部品として使う。

## アウトカム

本PRDの完了時点で、次が成り立つ。

1. 一般の AAT site 上の Čech obstruction complex(`C^n(𝒰, Ob_U)`、
   `d∘d = 0`、`H^n(𝒰, Ob_U)`)が存在し、有限 poset regime で PRD-2 の
   有限版と一致することが証明されている。
2. 「局所合法 + 非零の具体的 class → 大域非合法」(定理7.1)と
   「局所合法 + class 消滅 + effective torsor → 大域合法」(定理11.1、
   系11.2)が、仮定を明示した theorem package として証明されている。
3. feature extension の境界残差(定理9.2)、cover の形による負債容量
   (定理12.2 / 12.4)、period の複式簿記(定理13.2)が証明されている。
4. 擬円周 boundary model が有限モデルとして実装され、「witness counting
   には見えず H^1 には見える」実例が example theorem として検証されている
   (ArchSig R14 golden fixture の理論側対応物)。
5. 第IV部の本文ラベルと Lean 宣言の対応が両台帳で追跡できる。

## 第IV部ラベルの処遇表

ギャップ分析はこの表を基準に行う。

| 本文ラベル | 処遇 | 備考 |
| --- | --- | --- |
| 定義2.1 Obstruction Sheaf | 定義 | 係数 sheaf としての抽象定義 |
| 定義2.2 Coefficient Type | 定義 | abelian group sheaf / `O_X^U`-module 値。set-valued は cohomology の対象にしない |
| 原則2.3 Obstruction Layers | 対象外 | abelian 層のみ扱う。torsor / gerbe 層は非主張に記録 |
| 定義2.4 Canonical Obstruction Package | 定義(一部 placeholder) | `Def_U = I_U`、`ConDef_U = I_U/I_U²`(`Ideal.Cotangent` 橋)。`DerOb_U` は宣言のみ、第V部へ委譲。pushforward `i_* ConDef_U` の圏の固定を含む |
| 原則2.5 Obstruction Sheaf Relativity | 対象外 | 型パラメータで反映 |
| 定義3.1 Cover / 定義3.2 Čech Cochains / 定義3.3 Čech Differential | 定義+証明 | 一般 AAT site 版。`d^{n+1} ∘ d^n = 0` を証明。PRD-2 有限版との一致定理を含む(R2) |
| 定義4.1 Obstruction Cohomology | 定義 | cover-relative が一次。`H^n(X, Ob_U)` は比較仮定の下の条件付き記法(R3) |
| 意味4.2 / 原則4.3 / 原則4.4 | 対象外 | 4.4 の規律(具体的 class を仮定に取る)は各定理の形に反映 |
| 定義5.1 Local Flatness Data | 定義 | PRD-3 の `Flat_U(X)` を使う |
| 定義5.2 Gluing Mismatch | 定義 | 比較写像 `mismatch` はパラメータ |
| 原則5.2A Torsor-Normalized Mismatch | 定義+証明 | pseudo-torsor 構造の定義と、cocycle 条件の自動成立補題(R4) |
| 定義5.3 Descent Obstruction Class | 定義 | |
| 定義6.1 Hidden Coupling Cocycle / 定義6.2 Hidden Coupling Class | 定義 | |
| 定理7.1 Local Flatness Gap [CBI] | 証明 | 大域 section の存在 → mismatch は coboundary → `[g] = 0` の対偶(R5) |
| 原則7.2 | 対象外 | |
| 定義8.1 Feature Extension Cover / 定義8.2 Boundary Mismatch Section | 定義 | 2-chart cover `{C_core, F}` と boundary `B` |
| 定義8.3 Boundary Connecting Homomorphism | 定義 | Čech 水準の構成(2-chart Čech complex の connecting map)。derived triangle は形式化しない(R6) |
| 定義9.1 Boundary Holonomy | 定義 | `Hol = delta(b_U)` |
| 定理9.2 Boundary Residue Theorem [CBI] | 証明 | 仮定ブロック(boundary-exact 係数、effective descent、`delta(b_U)` の完備性、NoHigherBoundaryObstruction)を引数として明示(R6) |
| 例9.3 / 例9.4 擬円周 | 例 theorem | R10 の有限モデルの中心。ArchSig R14 golden fixture の理論側対応物 |
| 定義10.1 Triple Overlap Coherence Failure | 定義 | 2-cocycle と `H^2` class |
| 意味10.2 / 原則10.3 | 対象外 | |
| 定理候補10.4 Multi-Feature MV Spectral Sequence | statement のみ | 低次五項完全列の形で形式化。スペクトル系列機構は立てない(R7) |
| 定理11.1 Cohomological Flatness Criterion [CBI] | 証明 | effective abelian `Ob_U`-torsor の仮定の下、`[g] = 0` iff 大域 lawful section(局所調整後)(R8) |
| 系11.2 Local-to-Global Flatness | 証明 | (R8) |
| 原則11.3 | 対象外 | 非主張に記録 |
| 定義12.1 Cover Nerve | 定義 | overlap 成分を明示した nerve。多重成分を許す(R9) |
| 定理12.2 Topological Debt Capacity [CBI] | 証明 | rank-nullity による下界。有限次元線形代数(R9) |
| 系12.3 Constant Coefficient Nerve Reading | 証明 | `H^1(U,k) ≅ H^1(N(U),k)`、`b_1` 読み(R9) |
| 定理12.4 Local Gluing Sufficiency [CBI] | 証明 | forest + surjective restriction → `H^1 = 0`(R9) |
| 系12.5 Euler Accounting | 証明 | 交代和の保存(R9) |
| 定義13.1 Cochain-Chain Pairing | 定義 | Stokes-compatible pairing(R11) |
| 定理13.2 Period Stokes Identity [CBI] | 証明 | `<dω,γ> = <ω,∂γ>` と `<delta(b),γ> = <b,∂γ>`(R11) |
| 原則13.3 | 対象外 | 非主張に記録 |
| 定義13.4 Extension Holonomy Accounting Reading | 定義(規約) | `kappa_U` の加法性を defining property とする会計規約。定理ではないことを docstring に明記 |
| 定義14.1 Aggregation Morphism | 定義 | 有限 site 射 `pi`、`pi_*`。`R^q pi_*` は statement に必要な範囲の Čech 式定義(R12) |
| 定理候補14.2 Leray Five-Term Debt Sequence | statement のみ | 五項完全列の形で形式化(R12) |
| 定義14.3 Scale-Stable Debt | 定義 | `image(H^1(coarse) -> H^1(fine))` への所属(R12) |
| 原則14.4 Scale Relativity | 対象外 | 非主張に記録 |

## 要求

### R0. 前提の確認と Formal/AG/Cohomology の立ち上げ

- 本PRDの実装は PRD-2(`Formal/AG/Site`)と PRD-3(`Formal/AG/LawAlgebra`)の
  成果物に依存する。着手時に依存宣言の存在を確認し、未実装の場合は
  `blocked` として tracking Issue に記録する。先行PRDの実装を先取りしない。
- 第IV部のモジュールを `Formal/AG/Cohomology/` 以下に実装する(例:
  `ObstructionSheaf.lean`, `CechComplex.lean`, `Cohomology.lean`,
  `Descent.lean`, `FlatnessGap.lean`, `BoundaryResidue.lean`,
  `FlatnessCriterion.lean`, `Nerve.lean`, `Stokes.lean`, `Aggregation.lean`)。
- ルート import に追加し、CI の `lake build` 対象に含める。
- 完了条件: 空でない最初のモジュールが CI でビルドされ merge されている。

### R1. Obstruction Sheaf と標準 package(定義2.1、2.2、2.4)

- obstruction sheaf `Ob_U` を、AAT site 上の abelian group 値または
  `O_X^U`-module 値の係数 sheaf として定義する(定義2.2 の係数型を型クラス
  または圏パラメータで固定する)。
- 標準 obstruction package を形式化する: `Def_U := I_U`(PRD-3 の
  `I_Ob^U`)、`ConDef_U := I_U/I_U²`(Mathlib `Ideal.Cotangent` への橋、
  lawful locus 上の module としての圏の固定、`i_* ConDef_U` との区別)。
- `DerOb_U(M)` は型シグネチャのみの opaque 宣言とし、余接複体と `Ext¹` の
  実装は第V部 PRD へ委ねることを docstring に明記する。
- 完了条件: 定義と橋が sorry なしで存在する。

### R2. 一般 Čech 複体と PRD-2 一致定理(定義3.1–3.3)

- 一般の AAT site 上の cover `𝒰 = {W_i -> W}` に対して、Čech cochain
  `C^n(𝒰, Ob_U)`(`(n+1)`-fold overlap 上の section の積)と Čech
  differential(restriction の交代和)を定義し、`d^{n+1} ∘ d^n = 0` を
  証明する。
- `H^n(𝒰, Ob_U) = ker d^n / im d^{n-1}` を定義する。
- **PRD-2 一致定理**: 有限 poset AAT site regime において、本定義の
  `C^n` / `d` / `H^n` が PRD-2(命題7.2C 用)の有限 poset 版と一致することを
  定理として証明する。
- 完了条件: `d∘d = 0` と一致定理が sorry なしで証明され、
  `proof_obligations.md` で `proved` に昇格している。

### R3. Obstruction Cohomology の記法(定義4.1)

- cover-relative `H^n(𝒰, Ob_U)` を一次の対象とする。
- `H^n(X, Ob_U)` を、Čech-to-sheaf 比較または refinement system を仮定として
  明示した条件付き記法として定義する(仮定は構造体フィールドとして持ち、
  無条件の sheaf cohomology を構成しない)。
- 完了条件: 定義が sorry なしで存在する。

### R4. Gluing Mismatch・Torsor 正規化・Descent Class(定義5.1–5.3、原則5.2A)

- local flatness data(各 `W_i` 上の lawful section、PRD-3 の
  `s_i^* I_Ob^U = 0`)を定義する。
- gluing mismatch `g_{ij} = mismatch(s_i|W_ij, s_j|W_ij)` を、比較写像を
  パラメータとして定義する。
- pseudo-torsor 正規化(原則5.2A)を形式化する: `Lawful_U(W_i)` が
  `G_U(W_i)`-pseudo-torsor をなす場合、`g_{ij} = s_j - s_i` が triple
  overlap 上で cocycle 条件 `g_{ij} + g_{jk} + g_{ki} = 0` を自動的に
  満たすことを補題として証明する。
- descent obstruction class `[g] in H^1(𝒰, Ob_U)` を定義する。
- 完了条件: 定義と cocycle 自動成立補題が sorry なしで存在する。

### R5. Hidden Coupling と定理7.1(定義6.1、6.2、定理7.1)

- hidden coupling cocycle / class を定義する。
- 定理7.1 を証明する: `𝒰` が U-adequate、各 `s_i` が `Flat_U(X)` を factor
  through し、hidden coupling class `[hc_U(X)] != 0` ならば、`s|W_i = s_i`
  かつ `Flat_U(X)` を factor through する大域 section `s` は存在しない。
  証明は「大域 section が存在すれば mismatch は coboundary であり
  `[g] = 0`」の対偶による。
- 完了条件: 定理7.1 が sorry なしで証明され、`proof_obligations.md` で
  `proved` に昇格している。

### R6. Boundary Residue(定義8.1–8.3、9.1、定理9.2)

- feature extension cover(`C' = C_core ∪ F`、`B = C_core ∩ F`)を 2-chart
  cover として定義する。
- boundary mismatch section `b_U in H^0(B, Ob_B)` を定義する。
- connecting homomorphism `delta : H^0(B, Ob_B) -> H^1(C', Ob_C')` を
  2-chart Čech complex の水準で具体的に構成する(`C^0 = Ob(core) × Ob(F)
  -> C^1 = Ob(B)` の complex から)。derived category の MV triangle は
  形式化せず、係数が一つの object の制限から来る場合の Čech 表現として
  読む。
- boundary holonomy `Hol_U = delta(b_U)` を定義する。
- 定理9.2 を証明する: 本文の仮定ブロック(C_core / F の U-flatness、
  boundary witness coverage、axis exactness、boundary-exact 係数、
  ring restriction compatibility、selected torsor/module の effective
  descent、`delta(b_U)` による大域 obstruction class の完備性、
  NoHigherBoundaryObstruction)をすべて theorem 引数として明示した上で、
  `C'` is globally U-flat iff `delta(b_U) = 0`。
- 完了条件: 定理9.2 が sorry なしで証明され、`proof_obligations.md` で
  `proved` に昇格している。

### R7. H^2 と定理候補10.4(定義10.1、定理候補10.4)

- triple overlap coherence failure(2-cocycle `h`、`[h] in H^2`)を定義する。
- 定理候補10.4 を statement として形式化する: 有限 cover の Čech filtration
  から得られる低次五項完全列の形に限定し、スペクトル系列の一般機構は
  立てない。証明はしない。
- 完了条件: 定義と statement がコンパイルされている。

### R8. 定理11.1 Cohomological Flatness Criterion と系11.2

- effective abelian `Ob_U`-torsor の概念(local adjustment の差が abelian
  係数の作用で記述され、作用が effective)を定義する。
- 定理11.1 を証明する: 本文の仮定ブロック(local flatness、abelian 係数、
  cocycle `g`、effective torsor、U-adequate cover、soundness /
  completeness / axis exactness / witness coverage、descent、effective
  adjustment)の下で、貼り合わせ obstruction は `[g] in H^1` であり、
  `[g] = 0` なら局所調整後に大域 lawful section が存在し、`[g] != 0` なら
  存在しない。torsor class の消滅と torsor の自明性の同値を経由する。
- 系11.2(local flatness + vanishing `H^1` class → global flatness)を
  証明する。
- abelianization では元の non-abelian torsor の自明性が復元できないことを
  非主張として docstring に記録する。
- 完了条件: 定理11.1 と系11.2 が sorry なしで証明され、
  `proof_obligations.md` で `proved` に昇格している。

### R9. Cover Nerve と位相的負債定理(定義12.1、定理12.2、系12.3、定理12.4、系12.5)

- cover nerve `N(U)` を、overlap の連結成分を明示した複体(頂点 = chart、
  辺 = pairwise overlap 成分、面 = triple overlap 成分。多重成分を許す)
  として定義する。
- 定理12.2 を証明する: 有限 poset regime、有限次元 `k`-線形空間係数で、
  `dim H^1 >= dim C^1 - dim C^0 - dim C^2`(rank-nullity)。
- 系12.3 を証明する: 定数係数 `k` で `H^1(U,k) ≅ H^1(N(U),k)`、したがって
  `dim H^1(U,k) = b_1(N(U))`。
- 定理12.4 を証明する: `N(U)` が forest、triple overlap 面なし、restriction
  全射のとき `H^1(U,F) = 0`(木上の帰納法による mismatch の逐次吸収)。
- 系12.5 を証明する: `chi(U,F) = Σ (-1)^n dim C^n` は cochain 次元のみで
  決まり、shape と stalk 次元を保つ refactor で不変。
- 完了条件: 4定理・系が sorry なしで証明され、`proof_obligations.md` で
  `proved` に昇格している。

### R10. 擬円周ゴールデン例と有限モデル拡張

- PRD-1〜3 の有限モデル(`Formal/AG/Examples/`)を第IV部の水準へ拡張する。
  (a) 擬円周 boundary model(例9.3 / 9.4)を実装する: 各 chart は lawful、
      witness counting(`H^0` 的読み)では障害が見えないが、
      `H^1(𝒰, Ob_U) != 0` の具体的 cocycle が存在し、定理7.1 により大域
      lawful section が存在しないことを example theorem として検証する。
      ArchSig v0.4.0 R14 golden fixture との対応を docstring に記録する。
  (b) 2-chart feature extension の実例で定理9.2 の両方向(`delta(b) = 0` で
      貼り合う / `delta(b) != 0` で貼り合わない)を検証する。
  (c) forest cover の実例で定理12.4 の `H^1 = 0` を検証し、cycle を持つ
      nerve の実例で系12.3 の `b_1` 読みを検証する。
- 完了条件: (a)–(c) が sorry なしで存在する。

### R11. Period Stokes(定義13.1、定理13.2、定義13.4)

- 有限 poset / Čech model 上の chain group、boundary、cochain-chain pairing
  (basis simplex と dual basis、Stokes-compatible 条件)を定義する。
- 定理13.2 を証明する: `<d omega, gamma> = <omega, boundary gamma>`、および
  connecting homomorphism が coboundary representative で構成される場合の
  `<delta(b), gamma> = <b, boundary gamma>`。
- 定義13.4 の extension holonomy accounting を、`kappa_U` の加法性を
  defining property とする会計規約(構造体)として定義する。定理13.2 から
  自動的に従う系ではないことを docstring に明記する。
- 完了条件: 定理13.2 が sorry なしで証明され、`proof_obligations.md` で
  `proved` に昇格している。

### R12. Aggregation と Scale-Stable Debt(定義14.1、定理候補14.2、定義14.3)

- 有限 site 射 `pi : X_fine -> X_coarse` と pushforward `pi_* Ob` を
  定義する。`R^q pi_* Ob` は定理候補14.2 の statement に必要な範囲で
  Čech 式に定義する。
- cohomology の比較写像 `H^1(X_coarse, pi_* Ob) -> H^1(X_fine, Ob)` を
  構成する。
- 定理候補14.2 を五項完全列の形の statement として形式化する。証明は
  しない。
- scale-stable debt(定義14.3)を、selected aggregation family `Pi` の
  すべての `pi` で比較写像の image に入ることとして定義する。
- 完了条件: 定義と statement がコンパイルされている。

### R13. 台帳整備

- `lean_theorem_index.md` の AG 節に第IV部の宣言を追加する(本文ラベル列は
  `IV.` 付き)。
- `proof_obligations.md` に第IV部の証明対象ラベル(R2 一致定理、定理7.1、
  9.2、11.1、系11.2、12.2、系12.3、12.4、系12.5、13.2、example theorem 群)を
  登録し、進行に応じて status を更新する。定理候補10.4 / 14.2 は future
  proof obligation として登録する。
- 完了条件: 両台帳が最終実装と一致している。

## 非主張(claim boundary)

- 本PRDは abelian 係数の obstruction cohomology のみを扱う。non-abelian
  torsor の自明性、gerbe / stack obstruction(原則2.3 の第二・第三層)は
  第VI部の領分であり、abelianized class から元の torsor の自明性を復元
  できるとは主張しない。
- `H^n(X, Ob_U)` が sheaf cohomology を計算することを無条件に主張しない。
  比較は明示された仮定(Leray 条件、acyclic cover、refinement system)の
  下の記法である。
- `DerOb_U`、余接複体、derived category の MV triangle は形式化しない
  (第V部へ委譲)。スペクトル系列の一般機構も形式化しない。
- cohomology は metric ではない(原則4.3)。`H^1` 非零という群の性質だけ
  からは具体的な貼り合わせ失敗を主張せず、定理は具体的 cocycle / class を
  仮定に取る(原則4.4)。uncomputed != nonzero、unseen != zero
  (原則11.3)。
- 定義13.4 の accounting 等式は規約であり、定理13.2 の系ではない。境界
  class だけによる lawfulness の完全判定は、定理9.2 の完備性仮定
  (NoHigherBoundaryObstruction 等)なしには主張しない。
- 尺度安定性は selected aggregation family に相対化され、すべての分解・
  module boundary・runtime grouping への不変性を主張しない(原則14.4)。
- Stokes identity は構成済み AAT geometry 内部の会計であり、外部手続きの
  正しさを主張しない(原則13.3)。

## 完了条件(Acceptance Criteria)

- [ ] AC1. `Formal/AG/Cohomology` が新設され、CI の `lake build` でビルド
      される。先行PRD依存の blocked 判定が運用されている(R0)
- [ ] AC2. `Ob_U` の係数型と標準 package(`Def_U` / `ConDef_U` /
      `DerOb_U` placeholder)が形式化されている(R1)
- [ ] AC3. 一般 Čech complex が定義され、`d∘d = 0` が証明されている(R2)
- [ ] AC4. PRD-2 の有限 poset 版 Čech complex との一致定理が sorry なしで
      証明されている(R2)
- [ ] AC5. cover-relative `H^n(𝒰)` と条件付き記法 `H^n(X)` が定義されて
      いる(R3)
- [ ] AC6. gluing mismatch・pseudo-torsor 正規化・cocycle 自動成立補題・
      descent class が形式化されている(R4)
- [ ] AC7. 定理7.1 Local Flatness Gap が sorry なしで証明されている(R5)
- [ ] AC8. 2-chart connecting homomorphism が Čech 水準で構成され、boundary
      holonomy が定義されている(R6)
- [ ] AC9. 定理9.2 Boundary Residue が、仮定ブロックを明示して sorry なしで
      証明されている(R6)
- [ ] AC10. 定義10.1 と定理候補10.4 の statement(五項完全列形)が
      コンパイルされている(R7)
- [ ] AC11. 定理11.1 と系11.2 が sorry なしで証明されている(R8)
- [ ] AC12. cover nerve が定義され、定理12.2 / 系12.3 / 定理12.4 / 系12.5 が
      sorry なしで証明されている(R9)
- [ ] AC13. 擬円周ゴールデン例(H^0 では見えず H^1 で見える)が example
      theorem として検証され、ArchSig R14 との対応が記録されている(R10)
- [ ] AC14. 定理9.2 両方向の実例と forest / cycle nerve の実例が検証されて
      いる(R10)
- [ ] AC15. pairing と定理13.2 が sorry なしで証明され、定義13.4 が規約と
      して形式化されている(R11)
- [ ] AC16. aggregation 射・比較写像・定理候補14.2 statement・scale-stable
      debt が形式化されている(R12)
- [ ] AC17. `Formal/AG` 全体に `axiom` / `admit` / `sorry` / `unsafe` が
      存在しない
- [ ] AC18. `lean_theorem_index.md` の AG 節が第IV部の宣言を `IV.` 付き
      本文ラベルで含み、最終実装と一致している(R13)
- [ ] AC19. `proof_obligations.md` に第IV部の証明対象ラベルが登録され、
      証明済み分が `proved`、定理候補10.4 / 14.2 が future proof obligation
      になっている(R13)

## 実行順序の指針

prd-loop のギャップ分析で対象を選ぶ際は、次の依存順を推奨する。

```text
R0 -> R1 -> R2 -> R3 -> R4 -> R5 -> (R6, R8, R9 は並行可)
   -> (R7, R11, R12 は並行可) -> R10 -> R13
```

R13(台帳)は各周回で増分更新してよい。R9(nerve と位相的負債)は R2 のみに
依存し、R4〜R8 を待たずに着手できる。R10 の擬円周例は R5(定理7.1)の
merge が前提である。R6 / R8 の仮定ブロックが本文の記述だけでは型にできない
場合(仮定の定式化に選択の余地がある場合)は、選択肢を添えてループを停止し、
人間の判断を仰ぐ。
