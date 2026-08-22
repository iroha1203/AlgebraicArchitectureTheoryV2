#!/usr/bin/env python3
"""
Toy: 還元 (G-107 (i)) をコードで見る。

  「サービス単位の読みが、どの観点(law)についても安全か」
   ⟺ 「全ての概念領域 A で、定数係数の A-subnerve 比較 H¹ が全単射」
   ⟺ 「全 A で J_A = (phantom, hidden) = (0, 0)」

簡略化: 概念(位置)は両水準で同じ(π = id)。粗視化は「モジュール→サービス」の
chart の併合だけ。サービス内部のモジュール間依存は退化成分(ズームアウトで消える)。
係数は ℚ。外部ライブラリなし。
"""
from fractions import Fraction as Fr
from itertools import combinations

# ---------------------------------------------------------------- toy system
MODULES = {
    # module            : (service,   このモジュールが触る概念)
    "orders.api":        ("Orders",   {"order_id", "eta"}),
    "orders.worker":     ("Orders",   {"order_id"}),
    "orders.pricing":    ("Orders",   {"price"}),
    "orders.discount":   ("Orders",   {"price"}),
    "orders.tax":        ("Orders",   {"price"}),
    "billing.charge":    ("Billing",  {"order_id", "price"}),
    "billing.invoice":   ("Billing",  {"price"}),
    "billing.ledger":    ("Billing",  {"price"}),
    "shipping.dispatch": ("Shipping", {"order_id"}),
    "shipping.eta":      ("Shipping", {"eta"}),
    "notify.mail":       ("Notify",   {"eta"}),
}
DEPS = [  # モジュール水準の依存(重なり)。無向
    # Orders 内部: price を巡る輪(三者合意なし) → 見えない輪
    ("orders.pricing", "orders.discount"), ("orders.discount", "orders.tax"), ("orders.tax", "orders.pricing"),
    ("orders.pricing", "billing.charge"),
    # Billing 内部: price を巡る輪、ただし三者で一つの金額スキーマを共有(面あり)
    ("billing.charge", "billing.invoice"), ("billing.invoice", "billing.ledger"), ("billing.ledger", "billing.charge"),
    # order_id: Orders → Billing → Shipping → Orders に見える輪。
    #   しかし Orders 側の入口(api)と出口(worker)はモジュール水準で繋がっていない
    ("orders.api", "billing.charge"), ("billing.charge", "shipping.dispatch"), ("shipping.dispatch", "orders.worker"),
    # eta: Orders → Shipping → Notify → Orders の輪。モジュール水準でも閉じている
    ("orders.api", "shipping.eta"), ("shipping.eta", "notify.mail"), ("notify.mail", "orders.api"),
]
AGREEMENTS = [  # 三者が同時に噛む合意(共通スキーマ)= 面。輪を「埋める」
    {"billing.charge", "billing.invoice", "billing.ledger"},
]
CONCEPTS = sorted(set().union(*(s for _, s in MODULES.values())))
svc = lambda m: MODULES[m][0]

# ---------------------------------------------------------------- nerves
class Nerve:
    def __init__(self):
        self.V, self.E, self.F = {}, {}, {}   # cell -> derived support (K1)
    def sub(self, A):
        """A-subnerve: 台が A と交わる cell だけ残す(K1 により閉じている)"""
        n = Nerve()
        n.V = {v: s for v, s in self.V.items() if s & A}
        n.E = {e: s for e, s in self.E.items() if s & A}
        n.F = {f: s for f, s in self.F.items() if s & A}
        return n

def fine_nerve():
    n, key = Nerve(), (lambda m: (svc(m), m))
    for m, (_, supp) in MODULES.items():
        n.V[m] = frozenset(supp)
    for a, b in DEPS:
        t, h = sorted((a, b), key=key)
        n.E[(t, h)] = n.V[t] & n.V[h]                      # K1: 辺の台 = 端点の台の交わり
    for tri in AGREEMENTS:
        a, b, c = sorted(tri, key=key)
        for e in [(a, b), (a, c), (b, c)]:
            assert e in n.E, f"agreement needs dependency {e}"
        n.F[(a, b, c)] = n.E[(a, b)] & n.E[(a, c)] & n.E[(b, c)]
    return n

def coarse_nerve(fine):
    n = Nerve()
    for m, s in fine.V.items():                            # C0: サービスの台 = モジュールの台の合併
        n.V[svc(m)] = n.V.get(svc(m), frozenset()) | s
    for (t, h) in fine.E:
        S, T = svc(t), svc(h)
        if S != T:                                         # サービス内部の辺はズームアウトで消える
            n.E[(S, T)] = n.V[S] & n.V[T]
    for (a, b, c) in fine.F:
        ss = (svc(a), svc(b), svc(c))
        if len(set(ss)) == 3:
            n.F[ss] = n.E[(ss[0], ss[1])] & n.E[(ss[0], ss[2])] & n.E[(ss[1], ss[2])]
        else:
            assert len(set(ss)) == 1, "toy では混在 face を避ける"
    return n

def phi_edge(e):
    S, T = svc(e[0]), svc(e[1])
    return None if S == T else (S, T)

# ---------------------------------------------------------------- ℚ 線形代数
def rref(M):
    M = [r[:] for r in M]; piv = []; r = 0
    rows, cols = len(M), (len(M[0]) if M else 0)
    for c in range(cols):
        if r >= rows: break
        p = next((i for i in range(r, rows) if M[i][c] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        pv = M[r][c]; M[r] = [x / pv for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c] != 0:
                f = M[i][c]; M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        piv.append(c); r += 1
    return M, piv

def rank(vectors):
    vectors = [v for v in vectors if any(x != 0 for x in v)]
    return len(rref(vectors)[1]) if vectors else 0

def nullspace(M, ncols):
    if not M:
        return [[Fr(int(i == j)) for j in range(ncols)] for i in range(ncols)]
    R, piv = rref(M)
    basis = []
    for fc in [c for c in range(ncols) if c not in piv]:
        v = [Fr(0)] * ncols; v[fc] = Fr(1)
        for i, pc in enumerate(piv):
            v[pc] = -R[i][fc]
        basis.append(v)
    return basis

# ---------------------------------------------------------------- Čech 複体と比較
def complex_of(n):
    V, E, F = list(n.V), list(n.E), list(n.F)
    vi = {v: i for i, v in enumerate(V)}; ei = {e: i for i, e in enumerate(E)}
    d0 = [[Fr(0)] * len(V) for _ in E]            # (d0 c)(t→h) = c(h) − c(t)
    for (t, h), i in ei.items():
        d0[i][vi[h]] += 1; d0[i][vi[t]] -= 1
    d1 = [[Fr(0)] * len(E) for _ in F]            # (d1 c)(a,b,c) = c(ab) − c(ac) + c(bc)
    for k, (a, b, c) in enumerate(F):
        d1[k][ei[(a, b)]] += 1; d1[k][ei[(a, c)]] -= 1; d1[k][ei[(b, c)]] += 1
    Z1 = nullspace(d1, len(E))
    B1 = [[d0[i][j] for i in range(len(E))] for j in range(len(V))]   # d0 の列
    return dict(V=V, E=E, ei=ei, Z1=Z1, B1=B1, h1=len(Z1) - rank(B1))

def J(coarse, fine, edge_map):
    """
    比較写像 H¹(coarse) → H¹(fine) の (dim ker, dim coker) = (phantom, hidden)。
    edge_map: fine edge -> coarse edge or None(退化)。pullback (φ*c)(e') = c(φ e')。
    """
    C, Fc = complex_of(coarse), complex_of(fine)
    def pull(z):
        out = [Fr(0)] * len(Fc["E"])
        for e2, i in Fc["ei"].items():
            e = edge_map(e2)
            if e is not None and e in C["ei"]:
                out[i] = z[C["ei"][e]]
        return out
    img = [pull(z) for z in C["Z1"]]
    r = rank(img + Fc["B1"]) - rank(Fc["B1"])   # H¹(fine) の中での像の次元
    return (C["h1"] - r, Fc["h1"] - r), C["h1"], Fc["h1"]

# ---------------------------------------------------------------- 観点(law)を入れた直接計算
def law_complex(n, law):
    """K0: 座標 = (cell, 値)。値は law が cell の台の上に取る値。label 同士は恒等、不在は零。"""
    m = Nerve()
    vals = lambda supp: {law[p] for p in supp}
    for v, s in n.V.items():
        for x in vals(s): m.V[(v, x)] = frozenset({x})
    for (t, h), s in n.E.items():
        for x in vals(s): m.E[((t, x), (h, x))] = frozenset({x})
    for (a, b, c), s in n.F.items():
        for x in vals(s): m.F[((a, x), (b, x), (c, x))] = frozenset({x})
    return m

def law_edge_map(e2):
    (t, x), (h, _) = e2
    e = phi_edge((t, h))
    return None if e is None else ((e[0], x), (e[1], x))

# ---------------------------------------------------------------- run
def run(title, laws):
    global CONCEPTS
    CONCEPTS = sorted(set().union(*(s for _, s in MODULES.values())))
    fine = fine_nerve(); coarse = coarse_nerve(fine)
    print(f"==== {title} ====")
    print("サービス水準の辺:", sorted(coarse.E))
    print("-- 深さマップ(観点なし。配線だけから計算)  J_A = (phantom, hidden)")
    depth = {}
    for k in range(1, len(CONCEPTS) + 1):
        for A in combinations(CONCEPTS, k):
            A = frozenset(A)
            j, hc, hf = J(coarse.sub(A), fine.sub(A), phi_edge)
            depth[A] = j
            print(f"  A={{{', '.join(sorted(A))}}}".ljust(36),
                  f"H¹(service)={hc} H¹(module)={hf}  → phantom={j[0]} hidden={j[1]}")
    print("  一様不変(どの観点でもサービス単位で読んでよい)?",
          "YES" if all(j == (0, 0) for j in depth.values()) else "NO")
    print("-- 観点(law)を入れて直接計算 → 深さマップの値の和に一致する")
    for name, law in laws.items():
        j, hc, hf = J(law_complex(coarse, law), law_complex(fine, law), law_edge_map)
        classes = {}
        for p_, x in law.items(): classes.setdefault(x, set()).add(p_)
        parts = [depth[frozenset(A)] for A in classes.values()]
        total = (sum(q[0] for q in parts), sum(q[1] for q in parts))
        terms = " + ".join(f"J_{{{','.join(sorted(A))}}}" for A in classes.values())
        print(f"  law={name:14s} 直接計算 J={j}   {terms} = {total}   {'OK' if j == total else 'MISMATCH'}")
    print()
    return depth

if __name__ == "__main__":
    run("系 A", {
        "currency_unit": {"price": "cents", "order_id": "-", "eta": "-"},
        "owner_team":    {"price": "payments", "order_id": "payments", "eta": "logistics"},
        "constant":      {"price": "x", "order_id": "x", "eta": "x"},
        "identity":      {"price": "p", "order_id": "o", "eta": "e"},
    })
    # 変種 B: Orders 内部の輪を「price の辺2本 + tax_rate の辺2本」の4角形にする。
    #   pricing -(price)- discount -(price)- tax -(tax_rate)- taxtable -(tax_rate)- pricing
    MODULES["orders.pricing"] = ("Orders", {"price", "tax_rate"})
    MODULES["orders.tax"]     = ("Orders", {"price", "tax_rate"})
    MODULES["orders.taxtable"] = ("Orders", {"tax_rate"})
    DEPS.remove(("orders.tax", "orders.pricing"))
    DEPS.extend([("orders.tax", "orders.taxtable"), ("orders.taxtable", "orders.pricing")])
    run("系 B(Orders 内部の輪が2概念にまたがる)", {
        "currency_unit": {"price": "cents", "tax_rate": "-", "order_id": "-", "eta": "-"},
        "money_as_one":  {"price": "money", "tax_rate": "money", "order_id": "-", "eta": "-"},
        "owner_team":    {"price": "payments", "tax_rate": "payments", "order_id": "payments", "eta": "logistics"},
        "identity":      {"price": "p", "tax_rate": "t", "order_id": "o", "eta": "e"},
    })
