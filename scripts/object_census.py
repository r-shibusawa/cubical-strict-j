"""Object-level census for W = square/K: the machine cross-checks of the
object-level sections of the separation paper.

Verifies, exhaustively:
  (1) edge census: W([1]) has 12 classes, 8 of them reversal-invariant
      (strict circle maps L -> W); the two strata loops are
      delta = [(u,u)] and gamma = [(u,~u)];
  (2) stage-zero rigidity: no strict disc in W([2]) has boundary
      delta + three constant faces (all 4 positions of the delta face;
      168^2 states);
  (3) invariant-square census: the free-homotopy graph on the 8
      invariant edges (edges = (v0-face, v1-face) pairs of u-reversal-
      invariant squares) is connected; delta is joined to the constant
      edge at the far vertex by a single invariant square, realized by
      the explicit square (u&v, u|~v); likewise gamma;
  (4) the strict endomorphism classes factoring through the collage
      Phi (classes [(F(d,a,t), F(d,~a,t))], 168^3 triples) number 42,
      and the strict-homotopy component of the identity (recomputed
      via the boundary-constrained CSP of homotopy_csp.py) is disjoint
      from them;
  (5) deck freeness: no element of DM(n) is self-negated (n <= 2).
"""
import sys
sys.path.insert(0, 'scripts')
from collage_type_lib import build, monotone_masks, NOT, gen
from homotopy_csp import homotopy_exists, N2, dm2, not2, n2c, orb2

# ---------- level-1 and level-2 machinery ----------
N1, leq1, rho1 = build(1)
dm1 = monotone_masks(N1, leq1)
not1 = {m: NOT(m, N1, rho1) for m in dm1}
X1 = gen(0, 1, N1)
X2, Y2 = gen(0, 2, N2), gen(1, 2, N2)

def rev1(m):
    """substitution u := ~u on DM(u)"""
    r = 0
    for p in range(N1):
        vu, vnu = p & 1, (p >> 1) & 1
        q = vnu | (vu << 1)
        if (m >> q) & 1:
            r |= 1 << p
    return r

def n1c(c):
    A, B = c
    return min((A, B), (B, A), (not1[A], not1[B]), (not1[B], not1[A]))

# (1) edge census
edges = sorted({n1c((A, B)) for A in dm1 for B in dm1})
inv_edges = [e for e in edges if n1c((rev1(e[0]), rev1(e[1]))) == e]
delta = n1c((X1, X1))
gamma = n1c((X1, not1[X1]))
c00 = n1c((0, 0))                        # constant at the (0,0)-vertex
c01 = n1c((0, (1 << N1) - 1))            # constant at the (0,1)-vertex
assert len(edges) == 12, len(edges)
assert len(inv_edges) == 8, len(inv_edges)
assert delta in inv_edges and gamma in inv_edges
print(f"(1) edge classes: {len(edges)}; reversal-invariant: {len(inv_edges)}")

# level-2 face maps (to level-1 classes)
def face2(m, var, e):
    """face var=e of a DM(u,v)-mask, as a DM(w)-mask (w = other var)"""
    r = 0
    for vw in (0, 1):
        for vnw in (0, 1):
            if var == 0:
                p = (0b10 if e == 0 else 0b01) | (vw << 2) | (vnw << 3)
            else:
                p = vw | (vnw << 1) | ((0b1000 if e == 0 else 0b0100))
            if (m >> p) & 1:
                r |= 1 << (vw | (vnw << 1))
    return r

def faces(c):
    A, B = c
    return {(var, e): n1c((face2(A, var, e), face2(B, var, e)))
            for var in (0, 1) for e in (0, 1)}

# (2) stage-zero rigidity of delta
count = 0
for A in dm2:
    for B in dm2:
        f = faces((A, B))
        for var in (0, 1):
            for e in (0, 1):
                if f[(var, e)] != delta:
                    continue
                rest = [f[k] for k in f if k != (var, e)]
                if all(r == c00 for r in rest):
                    count += 1
assert count == 0, count
print(f"(2) strict discs with boundary delta + 3 constants: {count}")

# (3) invariant squares and the free-homotopy graph
def urev2(m):
    """substitution u := ~u on DM(u,v)"""
    r = 0
    for p in range(N2):
        vu, vnu, vv, vnv = p & 1, (p >> 1) & 1, (p >> 2) & 1, (p >> 3) & 1
        q = vnu | (vu << 1) | (vv << 2) | (vnv << 3)
        if (m >> q) & 1:
            r |= 1 << p
    return r

graph = {e: set() for e in inv_edges}
for A in dm2:
    for B in dm2:
        k = n2c((A, B))
        if n2c((urev2(A), urev2(B))) != k:
            continue                     # not an L-cylinder square
        f = faces((A, B))
        f0, f1 = f[(1, 0)], f[(1, 1)]    # v = 0, 1 faces
        if f0 in graph and f1 in graph:
            graph[f0].add(f1)
            graph[f1].add(f0)
# connectivity
seen = {inv_edges[0]}
stack = [inv_edges[0]]
while stack:
    for nb in graph[stack.pop()]:
        if nb not in seen:
            seen.add(nb)
            stack.append(nb)
assert len(seen) == len(inv_edges), (len(seen), len(inv_edges))
assert c01 in graph[delta] and c00 in graph[gamma]
# the explicit square (u&v, u|~v)
V2 = Y2
sq = (X2 & V2, X2 | not2[V2])
assert n2c((urev2(sq[0]), urev2(sq[1]))) == n2c(sq)
fs = faces(sq)
assert {fs[(1, 0)], fs[(1, 1)]} == {delta, c01}
print(f"(3) free-homotopy graph on {len(inv_edges)} invariant edges: "
      f"connected; delta--const01 and gamma--const00 direct; "
      f"explicit square (u&v, u|~v) verified")

# (4) Phi-factoring classes vs the identity component
FULL = (1 << N2) - 1
def F(d, a, t):
    return (d & not2[t]) | (a & t) | (d & a)

def swsub2(m):
    r = 0
    for p in range(N2):
        vu, vnu, vv, vnv = p & 1, (p >> 1) & 1, (p >> 2) & 1, (p >> 3) & 1
        q = vv | (vnv << 1) | (vu << 2) | (vnu << 3)
        if (m >> q) & 1:
            r |= 1 << p
    return r

def nbsub2(m):
    r = 0
    for p in range(N2):
        vu, vnu, vv, vnv = p & 1, (p >> 1) & 1, (p >> 2) & 1, (p >> 3) & 1
        q = vnu | (vu << 1) | (vnv << 2) | (vv << 3)
        if (m >> q) & 1:
            r |= 1 << p
    return r

# strict maps g: W -> J/K = source-invariant classes of (J/K)([2]):
# interior cylinders (d,a,t) mod the deck group K_J
# {id, (d,~a,t), (~d,~a,t), (~d,a,t)}, plus the two ends (d mod ~d).
FULL2 = (1 << N2) - 1

def njc(c):
    d, a, t = c
    return min((d, a, t), (d, not2[a], t),
               (not2[d], not2[a], t), (not2[d], a, t))

factoring = set()
seen_g = set()
for t in dm2:
    if t in (0, FULL2):
        continue
    for d in dm2:
        for a in dm2:
            k = njc((d, a, t))
            if k in seen_g:
                continue
            seen_g.add(k)
            if njc((swsub2(d), swsub2(a), swsub2(t))) == k and \
               njc((nbsub2(d), nbsub2(a), nbsub2(t))) == k:
                factoring.add(n2c((F(d, a, t), F(d, not2[a], t))))
for m in dm2:                                  # the two ends of J/K
    km = min(m, not2[m])
    if min(swsub2(m), not2[swsub2(m)]) == km and \
       min(nbsub2(m), not2[nbsub2(m)]) == km:
        factoring.add(n2c((m, m)))             # D-end: diagonal embed
        factoring.add(n2c((m, not2[m])))       # A-end: antidiagonal
assert len(factoring) == 42, len(factoring)
idc = n2c((X2, Y2))
assert idc not in factoring
print(f"(4) Phi-factoring strict endomorphism classes: {len(factoring)}")

# identity component via the CSP (as in homotopy_csp.py)
inv2 = []
seen4 = set()
for A in dm2:
    for B in dm2:
        k = n2c((A, B))
        if k in seen4:
            continue
        seen4.add(k)
        if n2c((swsub2(A), swsub2(B))) == k and \
           n2c((nbsub2(A), nbsub2(B))) == k:
            inv2.append(k)
assert len(inv2) == 72, len(inv2)
comp = {idc}
frontier = [idc]
while frontier:
    e = frontier.pop()
    for e2 in inv2:
        if e2 in comp:
            continue
        if homotopy_exists(e, e2):
            comp.add(e2)
            frontier.append(e2)
assert len(comp) == 3, len(comp)
assert not (comp & factoring)
print(f"    identity component: {len(comp)} classes; "
      f"intersection with factoring set: empty")

# (5) deck freeness: no self-negated elements
for (n, dmn, notn) in ((1, dm1, not1), (2, dm2, not2)):
    assert all(notn[m] != m for m in dmn)
print("(5) no self-negated elements in DM(n), n <= 2")

print("ALL OBJECT-LEVEL CHECKS PASSED")
