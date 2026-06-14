---
status: idea
origin: NT-24
tags: [discrete-morse, free-resolution, betti, lawconflict]
created: 2026-06-14
---

# NT-24 代数的 Morse 縮約による LawConflict の最小化と Betti 下界

_〔定理候補・証明可能見込み〕 / 出典: docs/note の候補50_

## 主張

monomial law conflict regime で common ambient $R=k[E]$ 上の monomial ideals $I_U,I_V$ を固定し、$\mathrm{LawConflict}_i(U,V)=\mathrm{Tor}_i^R(R/I_U,R/I_V)$ を計算する Taylor 複体(または lcm-lattice 上の multigraded 複体)$F_\bullet$ をとる。$F_\bullet$ 上に Batzies-Welker 型の acyclic matching を選ぶと、Morse 縮約により $F_\bullet$ とホモトピー同値で、より小さい多重次数付き複体 $F_\bullet^M$(Morse 複体)が得られ、その $n$ 鎖の多重次数付き基底は critical cell に対応する。このとき次が成り立つ。
- (1) $\mathrm{LawConflict}_i$ は $F_\bullet^M$ を $R/I_V$ で tensor した複体のホモロジーで計算できる。
- (2) $i$ 次 multigraded Betti 数 $\beta_{i,\sigma}(\mathrm{LawConflict})$ は対応する critical cell の個数で上から押さえられる。
- (3) Morse matching が完全(critical cell が極小自由分解の rank に一致)なら極小多重次数付き分解が得られ、Betti 数は厳密値となる。
- 相対化: common ambient / monomial regime / 選んだ matching に相対化。

## 依拠

第V部 命題5.5(Monomial Conflict Calculation: Taylor/Scarf/lcm-lattice)、定義5.1(First Law Conflict Sheaf $\mathrm{LawConflict}_1$)、定理6.1(Derived Law Conflict)、第VIII部 定理4.2(Finite AAT Computability: monomial Tor)、拡張ノート B1(lcm-lattice)。

## 非自明性

命題5.5 は「Taylor/Scarf/lcm-lattice resolution が使える」と列挙するだけで、それらをどう縮約して最小の conflict 表示を得るかの定理が無い(第V部開放端で「lcm-lattice からの LawConflict の閉じた表示や Betti 数公式が空白」と明記)。本候補は代数的離散 Morse 理論を AAT へ持ち込み、Taylor 複体を Morse 縮約して LawConflict の最小化と Betti 下界を与える。G5(Hilbert 級数 = Tor 交代和)は次数ごとの交代和しか勘定しないが、本候補は各 $\mathrm{Tor}_i$ を個別に critical cell で縛る(交代和の打ち消しを起こさない、第I部 no-cancellation discipline と整合)。離散 Morse を組合せ位相だけでなく可換代数の分解計算へ使う点が深い橋である。

## CS / SWE 帰結

二つの law universe(例: layering と authority)の derived conflict $\mathrm{LawConflict}_i$ を、Taylor 複体に対する1本の acyclic matching の critical cell を数えるだけで multidegree 別に Betti 上界として読める新しい道が開く。CS 読み: $\beta_{i,\sigma}>0$ となる最小の $|\sigma|$(= witness support の lcm サイズ)が「この二法則が初めて非横断に交わるのに必要な設計要素の最小同時数」を与え、conflict の本質的アリティ(2法則だが3要素絡みの干渉か等)を判定できる。これは defect count では測れなかった構造量である。移植仮定付き計測接続として、Macaulay2 の monomial resolution + 代数的 Morse 縮約で計算可能。verdict: $\beta_{i,\sigma}=0$ の次数・多重次数で「その粒度では二法則は derived-transverse」と肯定判定(第V部 定義7.2)。

## 証明・根拠の見込み

Taylor 複体は $R/I_U$ の(一般に非極小)自由分解であり、Batzies-Welker (2002)『Discrete Morse theory for cellular resolutions』により acyclic matching を選ぶと Morse 複体 $F_\bullet^M$ がやはり cellular resolution となりホモトピー同値。$R/I_V$ で tensor して $i$ 次ホモロジーが $\mathrm{Tor}_i=\mathrm{LawConflict}_i$。critical cell の多重次数別個数が各 $F_i^M$ の rank なので $\beta_{i,\sigma}\le$(critical cells in multidegree $\sigma$)。matching が極小分解を与える(lcm-lattice が十分「一般」、または Scarf 複体が分解になる)場合は等号。AAT 側仮定は monomial regime(命題5.5)のみで追加原始概念なし。証拠: 付録B $I_U=\langle pq\rangle$、$I_V=\langle qr\rangle$ の Taylor 複体は短く、Morse 縮約で $\mathrm{Tor}_1\cong \langle pqr\rangle/\langle pq^2r\rangle$(B.5)の単一 multidegree 生成元 $pqr$ が1個の critical cell として残ることを手計算で確認できる(共有因子 $q$ に沿う conflict residue)。

## 関連

G5、B10、NT-25。

## 進捗ログ

- 2026-06-14: docs/note の候補50(NT-24)から転記。定式化・証明見込みは記載済み、in-repo の証明・数値検算はこれから。
