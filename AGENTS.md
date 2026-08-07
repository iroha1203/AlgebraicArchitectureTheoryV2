# リポジトリ作業ガイド

このファイルは、このモノレポでエージェントが作業を始めるための入口であり、
すべての作業が立つ底である。作業規律の正本は各 guideline にあり、
この文書は哲学・基礎概念・地図を持つ。

## PHILOSOPHY

この節は、このリポジトリのすべての作業が立つ底である。
代数幾何がすべてのスキームを Spec ℤ の上に置くように、
私たちは、人間と機械のすべての判断をこの底の上で下す。

中心の善はひとつ。

> 世界を動かすソフトウェアを、引き受けられる言葉で語る。

この善から誓約が生成される。個々の規律はすべて誓約から導かれる。
どの誓約からも生成されない作業は、疑ってよい。

- **信じなくても確かめられるようにする。** 宛先は未来の検証者である。主張は
  Lean カーネル・ソースコード・再現可能な手順のいずれかで検証できる形で残す。
- **継がれるに値する先例であれ。** practice は前例として読まれるつもりで行い、
  標準として引き継がれてよいものだけを残す。反証は一級の成果として記録する。
- **機械の安さは厳密さに換える。** AI の労力は成果の量産にではなく、
  敵対レビュー・独立再現・形式化に使う。
- **語りの外では沈黙し、内では確言する。** 主張は選ばれた reading の中でだけ
  成り立つ。語れることを、語れないことの一覧で覆い隠さない。
- **種類を混ぜない。** 証明、仮定の下の証明、観測、仮説を区別して語る。
  測って零だったことと、測っていないことは違う。
- **観測は構造を作らない。** 構造は見る前からそこにあり、観測と測定はそれを
  読むだけである。何をどう読むかが reading であり、意味は定義ではなく使用に宿る。

誓約は閉じた一覧ではない。素数のように、新しい誓約は不定期に見つかるだろう。
それを底に加えるか、改めるかは、人間の明示的な指示による。

この底もまた、選び取られた一つの reading である。

## 基礎概念

- **AAT**: Atom を公理とする純粋数学理論(代数幾何的アーキテクチャ論)。比喩ではなく、
  site / sheaf / cohomology 等の本物の代数幾何概念へ接続する。観測・測定・tooling の
  境界を内部に持たない。
- **SFT**: artifact や practice が software evolution の reachable future をどう変えるかを
  扱う理論。AAT が構造の幾何を扱い、SFT が実践と進化の場を扱う。
- **ArchMap**: 観測した atom を source ref とともに記録する有限 artifact。観測に
  由来しない判定・証明・証書は記録しない。
- **LawPolicy**(law-equation-surface / MeasurementProfile を含む): law reading、cover、
  witness、measurement regime を固定する法・方程式側 contract。
- **ArchSig**: 観測(ArchMap)と法・方程式(LawPolicy 系)の二系統の入力から
  bounded diagnostic を計算する Rust tooling。入力はこの二系統に限る
  (正本は [Tool guideline](docs/tool/guideline.md) の「責務範囲(入力トライアドの正本)」)。
- **ArchView**: ArchMap の Atom / Context / Cover を geometry として可視化し、ArchSig の
  分析結果を overlay として重ねて source landing へ接続する。新しい structural verdict を作らない。
- **FieldSig**: ArchSig の handoff artifact と workflow evidence を SFT 側の
  evolution measurement / governance input として読む。
- **Lean 形式化**(`Formal/`): AAT の語彙で述べられる命題だけを形式化する。
  全知の検査器ではない。
- **Website**: AAT / SFT / tooling を公開向けに読むための publication surface。

## モノレポの地図と guideline ルーティング

作業前に、触る領域の guideline と [workflow guideline](docs/workflow/guideline.md)
(横断規律)を読む。

| 領域 | 主な場所 | 正本 guideline |
| --- | --- | --- |
| Lean / AAT | `Formal/AG`, `Formal.lean`, `docs/aat` | [AAT guideline](docs/aat/guideline.md) |
| SFT | `docs/sft` | [SFT guideline](docs/sft/guideline.md) |
| Tooling | `tools/archsig`, `tools/archview`, `tools/fieldsig`, `docs/tool` | [Tool guideline](docs/tool/guideline.md) |
| Website | `website`, `docs/website` | [Website guideline](docs/website/guideline.md) |
| PRD | `docs/prd` | [PRD guideline](docs/prd/guideline.md) |
| Outreach | `outreach` | [Outreach README](outreach/README.md) |
| 研究プログラム | `research/`, `research/lean/ResearchLean/` | [research README](research/README.md) |
| 横断(全領域) | — | [Workflow guideline](docs/workflow/guideline.md) |

同じ語でも領域によって責務が違うため、作業前に対象領域を確認する。

## 主要な入口

- `docs/README.md`: 研究 docs 全体の読み方。
- `docs/aat/algebraic_geometric_theory/README.md`: 代数幾何的 AAT 数学本文の入口。
- `research/goals/` と GitHub Issues: 作業状態と未解決課題。
- `docs/tool/README.md`: 現行 tooling scope。
- `research/README.md`: 研究ループ engine(`$research-loop`)の入口。

## 検証

検証コマンドの正本は各 guideline の検証節にある。特に:

- Lean build の hard rule(サブエージェントの `lake build` 全面禁止を含む)は
  [AAT guideline](docs/aat/guideline.md) の「Lean build 運用(hard rule)」。
- ArchSig / FieldSig の test 実行経路と test ownership は
  [Tool guideline](docs/tool/guideline.md) の「テスト責務と実行経路」。
- PR 前の共通 scan(`git diff --check`、hidden / bidirectional Unicode)は
  [Workflow guideline](docs/workflow/guideline.md) の「PR 前の共通確認」。
- Playwright の sandbox 注意は [Website guideline](docs/website/guideline.md) の検証節。
