# 代数的アーキテクチャ論 & ソフトウェアの場の理論

[English version](README.md)

このリポジトリは、**Algebraic Architecture Theory**（AAT / 代数的アーキテクチャ論）と
**Software Field Theory**（SFT / ソフトウェアの場の理論）の Lean 形式化、研究ノート、
tooling 設計を管理するための独立リポジトリです。

大きな目的は、ソフトウェアアーキテクチャを静的な形だけでなく、
変更・レビュー・CI・運用・AI agent の proposal によって変化し続ける対象として扱い、
何が保存され、何が破れ、どの未来へ進みやすくなったのかを診断できる理論と
ツールチェーンを作ることです。

この研究の圧縮表現として、次の三つを置いています。

- AAT は、アーキテクチャを局所代数として扱う。
- ArchSig は、アーキテクチャを観測可能な signature として取り出す。
- SFT は、ソフトウェア進化を計算可能な transition として扱う。

英語で発信するときの短い標語は次です。

```text
AAT makes architecture locally algebraic.
ArchSig makes architecture observable.
SFT makes software evolution computable.
```

全体像は [研究の全体目標](docs/research_goal.md) を入口とします。

## 研究の問い

この研究は、アーキテクチャレビューを「感想」から「診断」へ近づけることを目指します。
中心にある問いは次です。

```text
この変更は、選択された architecture invariant を保存しているか。
保存していないなら、どの obstruction witness がそれを示しているか。
その破れはどの ArchitectureSignature axis に現れるか。
この PRD / Issue / PR は、どの future architecture を開きやすくするか。
どの review / CI / policy / governance が危険な trajectory を狭めるか。
```

この問いに答えるため、次を明確に分けます。

- Lean で証明する構造的主張。
- tooling が artifact から観測・推定する主張。
- 実証研究で検証する仮説。
- 明示された theorem boundary / forecast boundary の外に残す non-conclusions。

## 層の分担

| 層 | 役割 | Source of truth |
| --- | --- | --- |
| AAT | architecture object、operation、invariant、obstruction witness、signature、theorem boundary を扱う局所代数。 | [AAT 数学理論](docs/aat/mathematical_theory.md) |
| AAT / SFT Interface | AAT の局所主張を SFT の projection、observable coordinate、governance 側でどう読むかを定める境界。 | [AAT / SFT Interface](docs/sft/aat_interface.md) |
| ArchSig / FieldSig Tooling | ArchSig は AAT structural signature、witness、review cue を抽出する。FieldSig は ArchSig refs と workflow evidence から SFT software evolution evidence を測定する。 | [AAT Tooling Documentation](docs/tool/README.md) |
| SFT | PRD、Spec、Issue、PR、review、CI、organization、AI、feedback が reachable future をどう変えるかを扱う計算理論。 | [ソフトウェアの場の理論](docs/sft/software_field_theory.md) |
| Lean 形式化 | 前提を明示できる構造的命題、finite universe、lawfulness bridge、bounded theorem package。 | [Lean 定義・定理索引](docs/aat/lean_theorem_index.md) |
| Proof / empirical ledger | theorem boundary、未解決 proof obligation、empirical hypothesis、Issue との対応。 | [証明義務と実証仮説](docs/aat/proof_obligations.md) |
| Website | AAT、SFT、ArchSig を公開向けに読むための no-build Cloudflare Pages サイト。 | [Website 運用メモ](docs/website/README.md) と [website source](website/index.html) |

README は詳細な theorem 一覧や進捗台帳を重複して持ちません。
現在の Lean status、non-conclusion boundary、未解決 proof obligation は
[証明義務と実証仮説](docs/aat/proof_obligations.md) と
[Lean 定義・定理索引](docs/aat/lean_theorem_index.md) で管理します。

## 読む順序

1. [研究の全体目標](docs/research_goal.md)
2. [AAT 数学理論](docs/aat/mathematical_theory.md)
3. [AAT / SFT Interface](docs/sft/aat_interface.md)
4. [ソフトウェアの場の理論](docs/sft/software_field_theory.md)
5. [証明義務と実証仮説](docs/aat/proof_obligations.md)
6. [Lean 定義・定理索引](docs/aat/lean_theorem_index.md)
7. [AAT Tooling Documentation](docs/tool/README.md)
8. 必要に応じて [docs 読み方](docs/README.md),
   [AAT directory guide](docs/aat/README.md),
   [SFT directory guide](docs/sft/README.md),
   [Website 運用メモ](docs/website/README.md)

## AAT

AAT は、ソフトウェアアーキテクチャを bounded な `ArchitectureObject` として切り出し、
その上の操作がどの不変量を保存し、どの obstruction witness を生み、
どの signature axis に現れるかを扱う理論です。

```text
software architecture
  = ArchitectureObject
  + ArchitectureOperation
  + InvariantFamily
  + ObstructionWitness
  + ArchitectureSignature
  + theorem boundary / non-conclusions
```

AAT は設計原則をスローガンではなく operation として読みます。
SOLID、Layered / Clean Architecture、Event Sourcing、Saga、Circuit Breaker、
Replicated Log などを万能な格言として並べるのではなく、
それぞれがどの invariant、operation、observation、theorem boundary に関係するかを問います。

## SFT

SFT は、ソフトウェア進化を計算可能な対象として扱う理論です。
コードベースは、変更を受け取って終わる静的な構造ではありません。
PRD、Spec、Issue、PR、review、CI、organization、AI、lifecycle decision は、
次に起こりやすい変更、見落とされやすい破れ、蓄積する制約、減衰される shortcut を作ります。

SFT は AAT の局所代数を、field model の architecture projection、observable coordinate、
local transition law、governance input として使います。
ただし、AAT theorem はそのまま empirical forecast にはなりません。
`ForecastCone`、`ConsequenceEnvelope`、`FieldUpdate`、AI proposal governance は、
明示された computable core と claim boundary の下で扱います。

## Tooling

tooling の目標は、AAT と SFT の語彙を実際の開発 artifact に接続することです。
ArchSig は、コードベース、PR、report、policy から観測できるものを取り出し、
signature axis、obstruction witness、theorem boundary status、forecast boundary を
レビューや CI が扱える evidence に変換します。

ただし、tooling は理論そのものではありません。
measured zero と unmeasured を混同せず、tool pass を Lean theorem として読みません。

## Website

`website/` は、AAT、SFT、ArchSig を公開向けに読むための Cloudflare Pages
reading surface です。研究本文、Lean status、proof obligation の台帳そのものではなく、
`docs/` で管理する claim boundary を保ったまま、AAT / SFT を web-native preprint /
monograph として、ArchSig を公開 manual として読める形にします。

website の計画と編集ルールは [docs/website](docs/website/README.md) で管理します。
現在の stack は no-build の静的構成で、HTML、CSS、小さな JavaScript、MathJax、
`website/assets` 以下の local assets を使います。

## Lean 形式化

現在 Lean 側に存在する主要な定義・定理は
[Lean 定義・定理索引](docs/aat/lean_theorem_index.md) を参照してください。
定理名、bounded reading、non-conclusion boundary は
[証明義務と実証仮説](docs/aat/proof_obligations.md) と
[Lean 定義・定理索引](docs/aat/lean_theorem_index.md) で管理します。

アーキテクチャ零曲率定理の static structural core は Lean で証明済みですが、
runtime metrics、empirical hypotheses、一般数値 curvature、実コード extractor の完全性は
この QED には含めません。

## リポジトリ構成

- `Formal.lean`
  - Lean ライブラリの public entry point。
- `Formal/Arch`
  - `Core`, `Law`, `Signature`, `Extension`, `Operation`, `Patterns`, `Repair`, `Evolution`, `Examples`
    に分けた Lean 形式化。
  - 主要な定義・定理と module path は [Lean 定義・定理索引](docs/aat/lean_theorem_index.md) を参照。
- `docs`
  - 第一級理論文書、Lean status、proof obligations、tool docs、empirical protocol。
- `docs/aat`
  - AAT の数学理論、proof obligations、Lean theorem index。
- `docs/sft`
  - AAT / SFT interface と SFT 本文。
- `docs/tool`
  - AIR、extractor、report、claim boundary、workflow、schema compatibility。
- `docs/website`
  - 公開 website の sitemap、design、tone、publication rule を管理する内部運用メモ。
- `website`
  - AAT / SFT / ArchSig の公開 reading surface を提供する no-build static Cloudflare Pages site。
- `Main.lean`
  - 実行ターゲット `aatv2` の最小 entry point。
- `lakefile.toml`
  - Lake build 設定。
- `lean-toolchain`
  - Lean バージョン固定。

## Build

```bash
lake build
lake build Formal
lake exe aatv2
```

`lake exe aatv2` の出力は次の通りです。

```text
Algebraic Architecture Theory V2
```

## 証明と文書の扱い

- Lean ソースに `axiom`, `admit`, `sorry`, `unsafe` を導入しない。
- 未証明の主張は `docs/aat/proof_obligations.md` または GitHub Issues に明示する。
- Lean で証明済みの主張、定義のみの概念、将来の証明義務、実証仮説を混同しない。
- AAT theorem、tooling output、SFT forecast、empirical hypothesis を同一視しない。
- `docs/aat/proof_obligations.md` は GitHub Issues への索引としても使う。

## タスク管理

未解決課題は GitHub Issues で管理します。
Issue は研究の依存構造に沿って milestone と
`type:*`, `area:*`, `priority:*`, `status:*` label で整理します。
README には Issue 一覧を重複して持たせません。

## ライセンス

このリポジトリは MIT License で公開します。詳細は [LICENSE](LICENSE) を参照してください。


## FieldSig

FieldSig is the SFT-based software evolution measurement crate under `tools/fieldsig`. Run `cargo test --manifest-path tools/fieldsig/Cargo.toml` for FieldSig changes. ArchSig remains the AAT structural telemetry generator under `tools/archsig`.
