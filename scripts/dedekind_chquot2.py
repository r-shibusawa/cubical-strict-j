"""O28 stage 3e: T-Betti vs Sing-Betti on QUOTIENTS.

thm:chainquot predicts Sing-Betti = T-Betti for every chain-cell
quotient, including homotopy-NONtrivial ones (torus, S^2 =
square/boundary).  The swap quotient SP^2 = square/(x ~ x.swap)
identifies NON-chain cells and lies outside the theorem: the
first genuine probe of whether chain approximation could be
universal.

Conventions: full complex = all classes, wall cofaces (validated
test invariant); Sing complex = sort-fixed classes, o-stat
cofaces (the simplicial structure of Sing_D).
"""
import sys, itertools
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
                if fc not in ind[q-1]:
                    return None   # face left the subcomplex
                v ^= 1 << ind[q-1][fc]
            cols.append(v)
        r[q] = rank2(cols)
    b = [len(reps[0]) - r[1]]
    for q in range(1, Q):
        b.append(len(reps[q]) - r[q] - r[q+1])
    return b

x1 = tuple(p[0] for p in F(1)[0])
c01 = tuple(0 for _ in F(1)[0]); c11 = tuple(1 for _ in F(1)[0])
xx = tuple(p[0] for p in F(2)[0]); yy = tuple(p[1] for p in F(2)[0])
v0 = ((0,), (0,))

K = 3
tests = [
  ("torus (opp edges)", 2,
   [(1, (c01, x1), (c11, x1)), (1, (x1, c01), (x1, c11))],
   "chain-cell quotient: thm:chainquot applies, expect equal (1,2,1)"),
  ("S^2 = square/bdry", 2,
   [(1, (c01, x1), v0[:1]*0 or ((0,)*2, (0,)*2)),
    (1, (c11, x1), ((0,)*2, (0,)*2)),
    (1, (x1, c01), ((0,)*2, (0,)*2)),
    (1, (x1, c11), ((0,)*2, (0,)*2))],
   "chain-cell quotient, expect equal (1,0,1)"),
  ("SP^2 square (swap)", 2,
   [(2, (xx, yy), (yy, xx))],
   "NON-chain pair: outside thm:chainquot"),
  ("Klein-ish (one flip pair)", 2,
   [(1, (c01, x1), (c11, x1))],
   "cylinder glue, chain cells, expect equal (1,1,0)"),
]
for name, n, idents, note in tests:
    W = Quotient(n, idents, K)
    bt = betti(W, n, K, False)
    bs = betti(W, n, K, True)
    tag = ("EQUAL" if bt == bs else "MISMATCH")
    print(f"{name}: T {bt} vs Sing {bs} [{tag}]  ({note})",
          flush=True)
