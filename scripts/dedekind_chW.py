"""O27 stage 16: the chain stratum of the monotone dunce hat.

Ch(W) = instances of sorted classes of W = the image of the counit
(= Real Sing W by section 164).  W is type- and test-contractible;
Ch(W) is a proper subobject (24 of 26 classes at level 2).
Compute the F2-homology of Ch(W) (chains to level 3) to measure
the gap that fibrancy must fill in the chain approximation lemma.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, restrict, Quotient
from collections import defaultdict

K = 3
W = Quotient(2, [(1, ((0,0), (0,1)), ((0,1), (0,0))),
                 (1, ((0,1), (0,1)), ((0,1), (1,1)))], K)

def o_stat_t(j, m):
    pts, _ = F(m)
    if j <= 0: return tuple(1 for _ in pts)
    if j > m: return 0 * len(pts) or tuple(0 for _ in pts)
    return tuple(1 if sum(p) >= j else 0 for p in pts)

def sort_sub(q):
    return tuple(o_stat_t(j, q) for j in range(1, q + 1))

def act(cls_, u, j, k):
    return W.cls(k, restrict(cls_, u, 2, j, k))

# sorted classes per level
sorted_cls = {q: [c for c in W.level(q)
                  if act(c, sort_sub(q), q, q) == c]
              for q in range(K + 1)}

def leq_t(a, b): return all(x <= y for x, y in zip(a, b))
def chain_subs(q, k):
    """chain-valued substitutions [k] -> [q] = q-tuples over F(k),
    pairwise comparable"""
    _, Dk = F(k)
    if q == 0: return [()]
    out = []
    for c in itertools.product(Dk, repeat=q):
        if all(leq_t(a, b) or leq_t(b, a)
               for a, b in itertools.combinations(c, 2)):
            out.append(c)
    return out

# Ch(W) at each level: instances of sorted cells along chain subs
ChW = {}
for k in range(K + 1):
    cells = set()
    for q in range(K + 1):
        for s in sorted_cls[q]:
            for u in chain_subs(q, k):
                cells.add(act(s, u, q, k) if q > 0 else
                          W.cls(k, restrict(s, tuple(), 2, 0, k)))
    ChW[k] = sorted(cells)
print("W levels:", [len(W.level(k)) for k in range(K+1)])
print("Ch(W) levels:", [len(ChW[k]) for k in range(K+1)], flush=True)

# F2 homology of Ch(W), chains to level 3 (T(delta)-faces)
def coface_T(i, q):
    f = tuple(x if x < i else x + 1 for x in range(q))
    idx = []
    for ii in range(1, q + 1):
        ks = [kk for kk in range(q) if f[kk] >= ii]
        idx.append(min(ks) if ks else q)
    return tuple(o_stat_t(kk, q - 1) for kk in idx)

def rank2(cols):
    rank = 0; pivots = []
    for c in cols:
        cur = c
        for p in pivots:
            cur = min(cur, cur ^ p)
        if cur: pivots.append(cur); rank += 1
    return rank

ind = {q: {c: i for i, c in enumerate(ChW[q])} for q in range(K+1)}
ranks = {}
ok = True
for q in range(1, K + 1):
    cols = []
    for cell in ChW[q]:
        v = 0
        for i in range(q + 1):
            Tf = coface_T(i, q)
            fc = act(cell, Tf, q, q - 1)
            if fc not in ind[q - 1]:
                ok = False; continue
            v ^= 1 << ind[q - 1][fc]
        cols.append(v)
    ranks[q] = rank2(cols)
print("faces stay in Ch(W):", ok)
b0 = len(ChW[0]) - ranks[1]
b1 = len(ChW[1]) - ranks[1] - ranks[2]
b2 = len(ChW[2]) - ranks[2] - ranks[3]
print(f"Ch(W) F2-Betti (deg 0..2): {b0}, {b1}, {b2}")
# compare: W itself
from dedekind_triangulate import tri_homology
print("W F2-Betti (deg 0..2):", tri_homology(W, 2, K))
