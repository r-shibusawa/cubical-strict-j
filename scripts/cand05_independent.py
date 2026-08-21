"""INDEPENDENT verification of the cand-05 core claims (O22).

Different formulation: by the universal property of the
coequalizer, a map W -> Y for W = y[2]/(A1~B1, A2~B2) is exactly
an element h of Y([2]) with h.A_i = h.B_i (precomposition by the
GENERATING cells only -- no congruence closure needed); a
homotopy (W x cube^1) -> Y is exactly H in Y([3]) with
H.(A_i x id) = H.(B_i x id).  For Y = W itself, equalities are
W-class equalities; we recompute W's congruence independently by
a DIFFERENT algorithm (fixed-point closure over generator
precompositions with explicit worklist, instead of the original
union-find over all site maps).

Checks:
 1. level sizes of W;
 2. endo count and node count (descent maps W -> W);
 3. cylinders H in W(3) with slice0 = id: expect exactly the
    constant one to be valid, and the total candidate count to
    match the forensics (restricted to old cells);
 4. the two-fold blocking of both connection cones.
"""
import itertools

def monotone(k):
    pts = list(itertools.product((0,1), repeat=k))
    out = []
    for bits in itertools.product((0,1), repeat=len(pts)):
        f = dict(zip(pts, bits))
        if all(f[p] <= f[q] for p in pts for q in pts
               if all(a <= b for a, b in zip(p, q))):
            out.append(tuple(bits))
    return pts, out

FC = {}
def FF(k):
    if k not in FC: FC[k] = monotone(k)
    return FC[k]

def subst(phi, args, ks, kt):
    """phi in F(ks) applied to ks-tuple args over F(kt)"""
    pts_t, _ = FF(kt); pts_s, _ = FF(ks)
    idx = {p: i for i, p in enumerate(pts_s)}
    return tuple(phi[idx[tuple(a[j] for a in args)]]
                 for j, p in enumerate(pts_t))

def pre(cell, u, ks, kt):
    """cell = n-tuple over F(ks); u = ks-tuple over F(kt)"""
    return tuple(subst(c, u, ks, kt) for c in cell)

# generators of cand-05: A1 = (0, x) ~ B1 = (x, 0);
# A2 = (x, x) ~ B2 = (x, 1)   (level-1 cells of cube^2)
x = (0, 1); c0 = (0, 0); c1 = (1, 1)
A1, B1 = (c0, x), (x, c0)
A2, B2 = (x, x), (x, c1)

# independent congruence: worklist closure of generator
# precompositions, then union-find per level
def congruence(K):
    classes = {}
    for k in range(K + 1):
        _, fk = FF(k)
        cells = list(itertools.product(fk, repeat=2))
        parent = {c: c for c in cells}
        def find(c):
            while parent[c] != c:
                parent[c] = parent[parent[c]]; c = parent[c]
            return c
        for (A, B) in ((A1, B1), (A2, B2)):
            for u in fk:                     # maps [k] -> [1]
                a = pre(A, (u,), 1, k); b = pre(B, (u,), 1, k)
                ra, rb = find(a), find(b)
                if ra != rb: parent[ra] = rb
        classes[k] = {c: find(c) for c in cells}
    return classes

CL = congruence(3)
def cls(k, c): return CL[k][c]
sizes = [len(set(CL[k].values())) for k in range(4)]
print("1. level sizes:", sizes, "(original: [2, 5, ?, ?])",
      flush=True)

# 2. endos: h in W(2)-classes with h.A_i ~ h.B_i:
# h as a class rep (2-tuple over F(2)); h.A = pre(h, A, 2, 1)
_, f2 = FF(2)
reps2 = sorted(set(CL[2].values()))
def ok_map(h):
    return (cls(1, pre(h, A1, 2, 1)) == cls(1, pre(h, B1, 2, 1))
        and cls(1, pre(h, A2, 2, 1)) == cls(1, pre(h, B2, 2, 1)))
nodes = [h for h in reps2 if ok_map(h)]
print("2. endo nodes:", len(nodes), "(original: 7)", flush=True)

# 3. cylinders in W(3): H with H.(A_i x id) ~ H.(B_i x id),
# slice0 = id
_, f3 = FF(3)
_, f1 = FF(1)
def times_id(cell1):
    """(A x id): [2] -> [3]... as a 2+1-tuple? A is a level-1 cell
    of cube^2 = 2-tuple over F(1); A x id = the 3-tuple over F(2):
    components (A_1(s), A_2(s), t)."""
    pts2 = FF(2)[0]
    a1 = tuple(cell1[0][(p[0],) == (1,)] if False else
               cell1[0][FF(1)[0].index((p[0],))] for p in pts2)
    a2 = tuple(cell1[1][FF(1)[0].index((p[0],))] for p in pts2)
    tv = tuple(p[1] for p in pts2)
    return (a1, a2, tv)
X1 = times_id((A1[0], A1[1])); Y1 = times_id((B1[0], B1[1]))
X2 = times_id((A2[0], A2[1])); Y2 = times_id((B2[0], B2[1]))
pts2 = FF(2)[0]
idcell = (tuple(p[0] for p in pts2), tuple(p[1] for p in pts2))
idcls = cls(2, idcell)
valid = []; withid0 = 0
t0 = (tuple(p[0] for p in pts2), tuple(p[1] for p in pts2),
      tuple(0 for p in pts2))
t1 = (tuple(p[0] for p in pts2), tuple(p[1] for p in pts2),
      tuple(1 for p in pts2))
for H in itertools.product(f3, repeat=2):
    s0 = cls(2, pre(H, t0, 3, 2))
    if s0 != idcls: continue
    withid0 += 1
    if (cls(2, pre(H, X1, 3, 2)) == cls(2, pre(H, Y1, 3, 2)) and
        cls(2, pre(H, X2, 3, 2)) == cls(2, pre(H, Y2, 3, 2))):
        valid.append(cls(2, pre(H, t1, 3, 2)))
print(f"3. W(3)-cylinders with slice0=id: {withid0} candidates, "
      f"valid: {len(valid)}, slice1 classes: "
      f"{[v == idcls for v in valid]}", flush=True)

# 4. cones
def cone_or():   # (x v t, y v t)
    pts3 = FF(3)[0]
    return (tuple(p[0] | p[2] for p in pts3),
            tuple(p[1] | p[2] for p in pts3))
def cone_and():  # (x ^ t, y ^ t)
    pts3 = FF(3)[0]
    return (tuple(p[0] & p[2] for p in pts3),
            tuple(p[1] & p[2] for p in pts3))
for nm, C in (("v-cone", cone_or()), ("^-cone", cone_and())):
    e1 = cls(2, pre(C, X1, 3, 2)) == cls(2, pre(C, Y1, 3, 2))
    e2 = cls(2, pre(C, X2, 3, 2)) == cls(2, pre(C, Y2, 3, 2))
    print(f"4. {nm}: swap-cond={e1} diag-cond={e2}", flush=True)
