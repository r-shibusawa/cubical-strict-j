"""O27 stage 14: the finite probe -- Real_D Sing_D of the monotone
dunce hat.

W = cube^2/((0,u)~(u,0), (u,u)~(u,1)).  Compute, at levels k <= 2:
 - sorted cells of W at levels q <= QMAX (classes fixed by sort_q);
 - cells of Real Sing W at level k = classes of pairs (q, s, c),
   s a sorted class, c a decreasing q-tuple over D(k), modulo the
   T-moves (s.T(h), c') ~ (s, T(h)<>c');
 - the counit value map (q,s,c) |-> s.c in W and its fibers:
   pattern splitting = cells of Real Sing W with equal counit
   value not identified by T-moves.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, cube_cells, all_maps, restrict, Quotient
from collections import defaultdict

QMAX = 4
KMAX = 2
W = Quotient(2, [(1, ((0,0), (0,1)), ((0,1), (0,0))),
                 (1, ((0,1), (0,1)), ((0,1), (1,1)))], QMAX)
# idents: swap fold (0,u)~(u,0); diag fold (u,u)~(u,1)
# cells as pairs of F(k)-tuples

def o_stat_t(j, m):
    """order statistic as F(m)-tuple"""
    pts, _ = F(m)
    if j <= 0: return tuple(1 for _ in pts)
    if j > m: return tuple(0 for _ in pts)
    return tuple(1 if sum(p) >= j else 0 for p in pts)

def sort_sub(q):
    return tuple(o_stat_t(j, q) for j in range(1, q + 1))

def act(cellcls, u, j, k):
    """class of level j acted by u: [k]->[j] (j-tuple over F(k))"""
    return W.cls(k, restrict(cellcls, u, 2, j, k))

# sorted classes at each q
sorted_cls = {}
for q in range(0, QMAX + 1):
    srt = sort_sub(q)
    sc = [c for c in W.level(q) if act(c, srt, q, q) == c]
    sorted_cls[q] = sc
    print(f"W sorted classes at q={q}: {len(sc)} of {len(W.level(q))}",
          flush=True)

def leq_t(a, b): return all(x <= y for x, y in zip(a, b))

def decreasing_tuples(q, k):
    _, Dk = F(k)
    if q == 0: return [()]
    out = []
    for c in itertools.product(Dk, repeat=q):
        if all(leq_t(c[i+1], c[i]) for i in range(q - 1)):
            out.append(c)
    return out

def ordinal_maps(a, b):
    res = []
    for vals in itertools.product(range(b + 1), repeat=a + 1):
        if all(vals[i] <= vals[i+1] for i in range(a)):
            res.append(vals)
    return res

def Tmap(f, a, b):
    """T(f): [a]->[b] = b-tuple over F(a)"""
    idx = []
    for i in range(1, b + 1):
        ks = [kk for kk in range(a + 1) if f[kk] >= i]
        idx.append(min(ks) if ks else a + 1)
    return tuple(o_stat_t(kk, a) for kk in idx)

for k in range(0, KMAX + 1):
    pairs = []
    for q in range(0, QMAX + 1):
        for s in sorted_cls[q]:
            for c in decreasing_tuples(q, k):
                pairs.append((q, s, c))
    idx = {p: i for i, p in enumerate(pairs)}
    parent = list(range(len(pairs)))
    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]; i = parent[i]
        return i
    def union(i, j):
        ri, rj = find(i), find(j)
        if ri != rj: parent[ri] = rj
    for (q, s, c) in pairs:
        i = idx[(q, s, c)]
        for qp in range(0, QMAX + 1):
            for h in ordinal_maps(qp, q):
                Th = Tmap(h, qp, q)   # [qp]->[q]: q-tuple over F(qp)
                # move: (q, s, Th<>c') ~ (qp, s.Th, c')
                for cp in decreasing_tuples(qp, k):
                    Thc = tuple(compose(comp, cp, qp, k) for comp in Th)
                    if Thc == c:
                        s2 = act(s, Th, q, qp)
                        if act(s2, sort_sub(qp), qp, qp) == s2:
                            key = (qp, s2, cp)
                            if key in idx: union(i, idx[key])
    classes = defaultdict(list)
    for p in pairs:
        classes[find(idx[p])].append(p)
    # counit values
    vals = {}
    for root, ps in classes.items():
        q, s, c = ps[0]
        v = act(s, c, q, k) if q > 0 else W.cls(k, restrict(
            s, tuple(), 2, 0, k)) if False else None
        if q == 0:
            # 0-level s: value = degenerate instance: s at level k
            # via the unique map [k]->[0] = empty tuple: restrict
            u0 = tuple()   # 0-tuple over F(k)
            v = W.cls(k, restrict(s, u0, 2, 0, k))
        vals[root] = v
    byval = defaultdict(list)
    for root, v in vals.items(): byval[v].append(root)
    split = {v: rs for v, rs in byval.items() if len(rs) > 1}
    nch = len(byval)
    print(f"level {k}: RealSingW cells = {len(classes)}, distinct "
          f"counit values = {nch}, SPLIT values (pattern "
          f"fibers > 1): {len(split)}", flush=True)
    if split and k == KMAX:
        v, rs = sorted(split.items(), key=lambda t: -len(t[1]))[0]
        print(f"  biggest fiber: value {v} with {len(rs)} Real-cells")
