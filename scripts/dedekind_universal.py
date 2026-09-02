"""O28 stage 3h: probing UNIVERSAL chain approximation.

Hypothesis: Ch(X) into X is a type equivalence for EVERY
Dedekind presheaf X (no fibrancy).  Necessary condition testable
by machine: Sing-Betti = T-Betti.  Battery: adversarial
quotients by NON-chain pairs -- the sort-fold, twisted generic
identifications, random non-chain 2-cell pairs, the
incomparable-pair merge C of the atom frontier (vertices
(1,0,1) ~ (0,1,1) in cube^3), and random cube^3 non-chain
quotients (level cap 3).
"""
import sys, itertools, random
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, restrict, Quotient
from dedekind_triangulate import coface as wall_coface, rank2

def o_stat_t(j, m):
    pts, _ = F(m)
    if j <= 0: return tuple(1 for _ in pts)
    if j > m: return tuple(0 for _ in pts)
    return tuple(1 if sum(p) >= j else 0 for p in pts)
def sort_sub(q): return tuple(o_stat_t(j, q) for j in range(1, q+1))
def coface_T(i, q):
    f = tuple(x if x < i else x + 1 for x in range(q))
    idx = []
    for ii in range(1, q + 1):
        ks = [kk for kk in range(q) if f[kk] >= ii]
        idx.append(min(ks) if ks else q)
    return tuple(o_stat_t(kk, q - 1) for kk in idx)

def betti(W, n, Q, sorted_only):
    reps = {}
    for q in range(Q + 1):
        lv = W.level(q)
        if sorted_only:
            lv = [c for c in lv
                  if W.cls(q, restrict(c, sort_sub(q), n, q, q)) == c]
        reps[q] = lv
    ind = {q: {c: i for i, c in enumerate(reps[q])} for q in reps}
    cof = coface_T if sorted_only else wall_coface
    r = {}
    for q in range(1, Q + 1):
        cols = []
        for cell in reps[q]:
            v = 0
            for i in range(q + 1):
                fc = W.cls(q-1, restrict(cell, cof(i,q), n, q, q-1))
                if fc not in ind[q-1]: return None
                v ^= 1 << ind[q-1][fc]
            cols.append(v)
        r[q] = rank2(cols)
    b = [len(reps[0]) - r[1]]
    for q in range(1, Q):
        b.append(len(reps[q]) - r[q] - r[q+1])
    return b

def check(name, n, idents, K=3):
    W = Quotient(n, idents, K)
    bt = betti(W, n, K, False); bs = betti(W, n, K, True)
    tag = "EQUAL" if bt == bs else "*** MISMATCH ***"
    print(f"{name}: T {bt} vs Sing {bs} [{tag}]", flush=True)
    return bt == bs

xx = tuple(p[0] for p in F(2)[0]); yy = tuple(p[1] for p in F(2)[0])
mt = tuple(a & b for a, b in zip(xx, yy))
jn = tuple(a | b for a, b in zip(xx, yy))

ok = True
ok &= check("sort-fold (x,y)~(x&y,x|y)", 2, [(2, (xx,yy), (mt,jn))])
ok &= check("(x,y)~(y,x|y)", 2, [(2, (xx,yy), (yy,jn))])
ok &= check("(x,y)~(x|y,x&y) antisort", 2, [(2, (xx,yy), (jn,mt))])
ok &= check("(x,y)~(x&y,x) shear", 2, [(2, (xx,yy), (mt,xx))])
ok &= check("swap+sortfold", 2, [(2, (xx,yy), (yy,xx)),
                                 (2, (xx,yy), (mt,jn))])
random.seed(11)
_, D2 = F(2)
pool2 = list(itertools.product(D2, repeat=2))
def comparable(a, b):
    return (all(x<=y for x,y in zip(a,b))
            or all(y<=x for x,y in zip(a,b)))
nonchain = [c for c in pool2 if not comparable(c[0], c[1])]
for t in range(8):
    A = random.choice(nonchain); B = random.choice(pool2)
    if A == B: continue
    ok &= check(f"rand nonchain #{t}: {A}~{B}", 2, [(2, A, B)])

# incomparable-pair merge C: cube^3 vertices (1,0,1)~(0,1,1)
vA = (tuple([1]), tuple([0]), tuple([1]))
vA = ((1,), (0,), (1,))
vB = ((0,), (1,), (1,))
ok &= check("merge C (101~011)", 3, [(0, vA, vB)])

print(f"ALL {'EQUAL' if ok else 'HAS MISMATCH'}", flush=True)
