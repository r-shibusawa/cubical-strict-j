"""O28: full F2-Betti of Sing(W) (sorted-cell simplicial chain
complex, unnormalized) up to degree 3 (levels 0..4).

This is the homotopy-CORRECT chain model of Ch(W) = Real Sing W:
Real_D is left Quillen (prop:triangres + rem:horns), so the type
(and test) homotopy type of Real Sing W is that of the simplicial
set Sing W, whose homology is computed here.  Together with
prop:tau1 (pi_1(Sing W) = pi_1(W) = 1), Betti (1,0,0,0) proves
Sing W ~ point and hence Ch(W) type-contractible.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, restrict, Quotient

K = 4
W = Quotient(2, [(1, ((0,0), (0,1)), ((0,1), (0,0))),
                 (1, ((0,1), (0,1)), ((0,1), (1,1)))], K)

def o_stat_t(j, m):
    pts, _ = F(m)
    if j <= 0: return tuple(1 for _ in pts)
    if j > m: return tuple(0 for _ in pts)
    return tuple(1 if sum(p) >= j else 0 for p in pts)
def sort_sub(q): return tuple(o_stat_t(j, q) for j in range(1, q+1))
def act(cls_, u, j, k): return W.cls(k, restrict(cls_, u, 2, j, k))
def coface_T(i, q):
    f = tuple(x if x < i else x + 1 for x in range(q))
    idx = []
    for ii in range(1, q + 1):
        ks = [kk for kk in range(q) if f[kk] >= ii]
        idx.append(min(ks) if ks else q)
    return tuple(o_stat_t(kk, q - 1) for kk in idx)

S = {q: [c for c in W.level(q)
         if act(c, sort_sub(q), q, q) == c] for q in range(K + 1)}
print("Sing(W) simplices per level:", [len(S[q]) for q in range(K+1)],
      flush=True)
ind = {q: {c: i for i, c in enumerate(S[q])} for q in range(K + 1)}
def rank2(cols):
    rank = 0; piv = []
    for c in cols:
        cur = c
        for p in piv: cur = min(cur, cur ^ p)
        if cur: piv.append(cur); rank += 1
    return rank
ranks = {}
for q in range(1, K + 1):
    cols = []
    for cell in S[q]:
        v = 0
        for i in range(q + 1):
            fc = act(cell, coface_T(i, q), q, q - 1)
            assert fc in ind[q - 1], "face left Sing!"
            v ^= 1 << ind[q - 1][fc]
        cols.append(v)
    ranks[q] = rank2(cols)
    print(f"rank d{q} = {ranks[q]}", flush=True)
b = [len(S[0]) - ranks[1]]
for q in range(1, K):
    b.append(len(S[q]) - ranks[q] - ranks[q + 1])
print("Sing(W) F2-Betti (deg 0..%d): %s" % (K - 1, b), flush=True)
