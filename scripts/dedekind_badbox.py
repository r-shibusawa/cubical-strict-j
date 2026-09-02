"""O28 stage 3g: does a BAD-S box break chain approximation?

Attach to W one box (S into cube^3) x delta^0 where S is a
(T0)-violating atom (ambient chain cells without sorted parents
in S).  The prescribed part P = S x cube^1 u cube^3 x {0} then
contains ambient chain cells outside Ch(P), whose values become
"premature" chain cells of X' (they are instances of the new
sorted filler).  X' is homotopy equivalent to W (~ point), so
chain approximation at X' demands Sing-Betti(X') = (1,0,0).
Test with a constant datum and with a cone datum.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, restrict, Quotient
from dedekind_triangulate import coface as wall_coface, rank2

K = 3
W = Quotient(2, [(1, ((0,0),(0,1)), ((0,1),(0,0))),
                 (1, ((0,1),(0,1)), ((0,1),(1,1)))], K)
def o_stat_t(j, m):
    pts, _ = F(m)
    if j <= 0: return tuple(1 for _ in pts)
    if j > m: return tuple(0 for _ in pts)
    return tuple(1 if sum(p) >= j else 0 for p in pts)
def sort_sub(q): return tuple(o_stat_t(j, q) for j in range(1, q+1))
def act(cls_, u, j, k): return W.cls(k, restrict(cls_, u, 2, j, k))
def rest(cell, u, j, k):
    return tuple(compose(c, u, j, k) for c in cell)
def leq_t(a, b): return all(x <= y for x, y in zip(a, b))
def comparable(a, b): return leq_t(a, b) or leq_t(b, a)
def coface_T(i, q):
    f = tuple(x if x < i else x + 1 for x in range(q))
    idx = []
    for ii in range(1, q + 1):
        ks = [kk for kk in range(q) if f[kk] >= ii]
        idx.append(min(ks) if ks else q)
    return tuple(o_stat_t(kk, q - 1) for kk in idx)

# the bad atom: regenerate the (T0) sweep's fail #2
import random
u3 = tuple(p[0] for p in F(3)[0]); v3 = tuple(p[1] for p in F(3)[0])
w3 = tuple(p[2] for p in F(3)[0])
def mt3(*xs):
    o = xs[0]
    for x in xs[1:]: o = tuple(a & b for a, b in zip(o, x))
    return o
def jn3(*xs):
    o = xs[0]
    for x in xs[1:]: o = tuple(a | b for a, b in zip(o, x))
    return o
pool = [mt3(u3,v3,w3), mt3(u3,v3), mt3(u3,w3), mt3(v3,w3),
        u3, v3, w3, jn3(u3,v3), jn3(u3,w3), jn3(v3,w3),
        mt3(u3,jn3(v3,w3)), mt3(v3,jn3(u3,w3)), jn3(u3,mt3(v3,w3))]
random.seed(3)
zs = [tuple(random.choice(pool) for _ in range(3)) for _ in range(25)]
zbad = zs[2]
S = {}
for k in range(K + 1):
    _, Dk = F(k)
    S[k] = {rest(zbad, u, 3, k)
            for u in itertools.product(Dk, repeat=3)}
print("bad atom S sizes:", [len(S[k]) for k in range(K+1)], flush=True)

ZE = {q: tuple(0 for _ in F(q)[0]) for q in range(K + 1)}
def inP(c, q):
    return c[3] == ZE[q] or (c[0], c[1], c[2]) in S[q]

def run(datum_name, b_val):
    # X' cells: ('o', class) or ('n', free position)
    def resolve(c, q):
        if inP(c, q): return ('o', b_val(c, q))
        return ('n', c)
    def cells(q, sorted_only):
        _, Dq = F(q)
        out = []
        for c in W.level(q):
            if sorted_only and act(c, sort_sub(q), q, q) != c:
                continue
            out.append(('o', c))
        for c in itertools.product(Dq, repeat=4):
            if inP(c, q): continue
            if sorted_only and tuple(
                compose(x, sort_sub(q), q, q) for x in c) != c:
                continue
            out.append(('n', c))
        return out
    def face(sym, i, q, cof):
        kind, v = sym
        if kind == 'o':
            return ('o', act(v, cof(i, q), q, q - 1))
        fc = tuple(compose(x, cof(i, q), q, q - 1) for x in v)
        return resolve(fc, q - 1)
    def betti(sorted_only):
        cof = coface_T if sorted_only else wall_coface
        lv = {q: cells(q, sorted_only) for q in range(K + 1)}
        ind = {q: {c: i for i, c in enumerate(lv[q])} for q in lv}
        r = {}
        for q in range(1, K + 1):
            cols = []
            for s in lv[q]:
                x = 0
                for i in range(q + 1):
                    fs = face(s, i, q, cof)
                    if fs not in ind[q - 1]: return None
                    x ^= 1 << ind[q - 1][fs]
                cols.append(x)
            r[q] = rank2(cols)
        b = [len(lv[0]) - r[1]]
        for q in range(1, K):
            b.append(len(lv[q]) - r[q] - r[q + 1])
        return b
    bt = betti(False); bs = betti(True)
    tag = "EQUAL" if bt == bs else "MISMATCH"
    print(f"{datum_name}: T {bt} vs Sing {bs} [{tag}]", flush=True)

v00 = W.cls(0, (ZE[0], ZE[0]))
def const_val(c, q):
    return W.cls(q, (ZE[q], ZE[q]))
run("constant datum", const_val)

# cone datum: b(c) = iota . (c1 ^ c4, c2 ^ c4) (kills at t=0)
def cone_val(c, q):
    m1 = tuple(a & b for a, b in zip(c[0], c[3]))
    m2 = tuple(a & b for a, b in zip(c[1], c[3]))
    return W.cls(q, (m1, m2))
run("cone datum", cone_val)
