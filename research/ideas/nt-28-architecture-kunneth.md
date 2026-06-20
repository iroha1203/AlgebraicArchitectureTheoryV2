---
status: idea
origin: NT-28
tags: [kunneth, composite-system, cohomology]
created: 2026-06-14
---

# NT-28 アーキテクチャ Künneth 定理: 合成システムの障害は因子の障害のテンソル積で決まる

_〔定理候補・証明可能見込み〕 / 出典: docs/note の候補50_

## 主張

二つの AAT site X = Site_AAT(S_1, V, U, J_1)、Y = Site_AAT(S_2, V, U, J_2) が有限 poset regime にあり、係数 k が体、obstruction sheaf がそれぞれ Ob_U^X, Ob_U^Y であるとする。積 site X ⊠ Y(context は (W, W′) の積、cover は積 cover、係数は外部テンソル Ob_U^X ⊠ Ob_U^Y)を相対化基底とする。このとき体係数の有限 poset regime において Künneth 同型 H^n(X ⊠ Y, Ob_U^X ⊠ Ob_U^Y) ≅ ⊕_{p+q=n} H^p(X, Ob_U^X) ⊗_k H^q(Y, Ob_U^Y) が成り立つ(Tor 項は体係数ゆえ消える)。系として: (i) 二系統が独立に統合された複合システムの第一隠れ結合容量は dim H^1(X ⊠ Y) = dim H^1(X) + dim H^1(Y)(各系統の容量の単純和)、(ii) X が大域 flat(H^{>0} = 0)なら H^n(X ⊠ Y) ≅ H^n(Y)(flat 因子は複合系の障害を増やさない)、(iii) 二つの flat でない系統の積では H^2(X ⊠ Y) ⊇ H^1(X) ⊗ H^1(Y) という「交差項」障害が必然的に出現する。すべて選ばれた係数体・積 cover・law universe に相対化され、非積 cover(系統間に追加 overlap がある統合)には適用しない。

## 依拠

第II部 仮定4.3 Pullback and Overlap / context overlap W_i ×_W W_j、第II部 命題7.2C Finite Poset Computation(有限線形代数 Čech)、第IV部 定義3.1–3.3 Čech Obstruction Complex、第IV部 定理12.2 Topological Debt Capacity(dim H^1 の容量読み)、第VIII部 定理4.2 Finite AAT Computability、個別予想ノート: cover nerve / b_1(N(U)) の容量読み(G2)。

## 非自明性

既存 G2 は単一 site の nerve から H^1 容量を読むが、「二つの独立システムを合成したとき障害がどう合成されるか」を扱う定理は存在しない。Künneth は標準代数幾何 / 位相幾何の柱だが、AAT には product site すら明示構成されていない(map に product site なし)。系 (iii) の「二つの非 flat 系統の積では交差項 H^1 ⊗ H^1 が H^2 に必然出現」は、独立に見える二系統の合成が新しい三項整合障害を強制的に生むという非自明な構造主張で、Massey 予想とも整合する。G2 の χ 保存則は単一 site 内の次数間移動だが、本定理は site 間の積に対する乗法的会計則 χ(X ⊠ Y) = χ(X)·χ(Y) を与える点で独立である。

## CS / SWE 帰結

マイクロサービス系統・モノレポ内の独立サブシステム・別チームが開発した二つのモジュール群を「合成」したときの統合障害容量を、各因子を別々に測った値から予測できる(再解析不要)。具体的には、flat な基盤(H^{>0} = 0)の上に feature 系統を載せても障害は増えない(系 ii)を保証でき、逆に二つの「それぞれは健全だが H^1 ≠ 0」な系統を合成すると、交差 H^2 障害が dim H^1(X)·dim H^1(Y) 次元ぶん必ず生まれる(系 iii)という、合成設計の下界を与える。これは「独立に開発・テストした二系統を結合するとなぜ新種の統合バグが出るか」の代数的説明であり、合成前にコスト(交差項の次元)を見積もる新しい道である(移植仮定: 積 site の構成が ArchMap 側で表現可能であること)。

## 証明・根拠の見込み

有限 poset regime では Čech complex C^•(X)、C^•(Y) はともに有限次元 k-cochain complex。積 cover の Čech complex はテンソル積複体 C^•(X) ⊗_k C^•(Y) と擬同型(Eilenberg–Zilber / shuffle 写像の有限版、acyclic cover を仮定)。体係数なので代数的 Künneth 定理(Tor_1 = 0)が直接適用でき H^n(C^•(X) ⊗ C^•(Y)) ≅ ⊕ H^p ⊗ H^q。系 (i)–(iii) は次元計算の即時帰結。χ の乗法性は dim(C^• ⊗ C^•) = dim C^• · dim C^• から従う。支持証拠: 擬円周(H^1 ≅ Z)二つの積 = 擬トーラスで H^1 ≅ Z^2, H^2 ≅ Z という古典トーラスの cohomology に一致する有限例が構成でき、Massey 予想の最小 non-formal 例とも符合する。境界: Eilenberg–Zilber 同型には、積 cover が両因子の acyclic cover の積で acyclic という Leray 型条件が必要で、これを相対化パラメータとして明示する(map の開放端「acyclic cover の十分条件が空白」に対する部分的解答)。

## 関連

NT-27、G5、第IV部 hidden coupling。

## 進捗ログ

- 2026-06-14: docs/note の候補50(NT-28)から転記。定式化・証明見込みは記載済み、in-repo の証明・数値検算はこれから。
