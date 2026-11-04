"""Alternation of two template domains on R^2 and Z^2 (exact rational arithmetic).

rho_T(S) = { x : t.x <= sup_S t.x for t in T } for a finite set T of directions (template polyhedra;
T = {+-e1,+-e2} is the interval domain, T' = {+-(1,1), +-(1,-1)} the interval domain in the diagonal
coordinates; their reduced product is the 2D octagon domain).  Polygons are kept as vertex lists."""
from fractions import Fraction as Fr
import itertools as it

def clip(poly, t, c):
    """Sutherland-Hodgman: keep points with t.x <= c."""
    out = []
    n = len(poly)
    if n == 0: return out
    for i in range(n):
        P, Q = poly[i], poly[(i + 1) % n]
        fp, fq = t[0]*P[0] + t[1]*P[1] - c, t[0]*Q[0] + t[1]*Q[1] - c
        if fp <= 0: out.append(P)
        if (fp < 0 < fq) or (fq < 0 < fp):
            s = fp / (fp - fq)
            out.append((P[0] + s*(Q[0]-P[0]), P[1] + s*(Q[1]-P[1])))
    # remove duplicates
    res = []
    for p in out:
        if not res or res[-1] != p: res.append(p)
    if len(res) > 1 and res[0] == res[-1]: res.pop()
    return res

def hull_box(poly):
    xs = [p[0] for p in poly]; ys = [p[1] for p in poly]
    return [(min(xs), min(ys)), (max(xs), min(ys)), (max(xs), max(ys)), (min(xs), max(ys))]

def rho(T, poly):
    """template hull of a polygon (bounded; T must positively span, we assume T contains the box directions
    or T = diagonal box).  Start from a big box containing poly and clip by each direction."""
    sup = {t: max(t[0]*p[0] + t[1]*p[1] for p in poly) for t in T}
    M = 10**6
    P = [(Fr(-M), Fr(-M)), (Fr(M), Fr(-M)), (Fr(M), Fr(M)), (Fr(-M), Fr(M))]
    for t in T: P = clip(P, t, sup[t])
    return P

BOX = [(1, 0), (-1, 0), (0, 1), (0, -1)]
DIA = [(1, 1), (-1, -1), (1, -1), (-1, 1)]

def alt_sequence(T, T2, S, steps):
    seq = [S]; P = S
    for k in range(steps):
        P = rho(T, rho(T2, P)); seq.append(P)
    return seq

print("== one extra direction: T = box + (1,2), T' = box + (2,1), S = [0,1]^2 cap {x+2y <= 5/2}")
T = BOX + [(1, 2)]; T2 = BOX + [(2, 1)]
S = clip([(Fr(0), Fr(0)), (Fr(1), Fr(0)), (Fr(1), Fr(1)), (Fr(0), Fr(1))], (1, 2), Fr(5, 2))
for k, P in enumerate(alt_sequence(T, T2, S, 6)):
    a = max(p[0] + 2*p[1] for p in P)
    print(f"  k={k}: alpha_k = {a}  (3 - 4^-k/2 = {3 - Fr(1,2)/4**k})  vertices {len(P)}")

# integer scaling: T = box + (1,2), T' = box + (2,1) on Z^2, S_N = integer points of N*Q cap {x+2y <= 5N/2};
# the number of rounds until a common fixed point is reached should be floor(log_4 N)
print("== integer scaling of the one-extra-direction pair on Z^2: rounds at S_N")
def int_rounds(N, a=(1, 2), b=(2, 1)):
    pts = [(x, y) for x in range(N+1) for y in range(N+1)]
    cur = {q for q in pts if 2*(a[0]*q[0] + a[1]*q[1]) <= 5*N}
    k = 0
    while True:
        beta = max(b[0]*q[0] + b[1]*q[1] for q in cur)
        mid = {q for q in pts if b[0]*q[0] + b[1]*q[1] <= beta}
        alpha = max(a[0]*q[0] + a[1]*q[1] for q in mid)
        nxt = {q for q in pts if a[0]*q[0] + a[1]*q[1] <= alpha}
        if nxt == cur: return k, 3*N - alpha
        cur = nxt; k += 1
for N in [2, 4, 8, 16, 32, 64, 128, 256, 512]:
    k, gap = int_rounds(N)
    expected = 0
    while 4**(expected+1) <= N: expected += 1
    print("  N=%d: rounds %d (floor(log_4 N) = %d), final gap %d" % (N, k, expected, gap))
# arc condition: for planar pairs T = C + A, T' = C + B with C containing the box directions, finite
# alternation at every bounded full-dimensional set holds iff no open arc between cyclically consecutive
# directions of C contains both a direction of A and a direction of B; the join of a stabilised run is rho_C(S)
print("== arc condition on random planar pairs (C contains the box directions)")
import random, math
from math import gcd, atan2
def prim(v):
    g = gcd(abs(v[0]), abs(v[1])); return (v[0]//g, v[1]//g)
pool = sorted({prim((x, y)) for x in range(-3, 4) for y in range(-3, 4) if (x, y) != (0, 0)})
def ang(v): return atan2(v[1], v[0]) % (2*math.pi)
def arc_condition(C, A, B):
    Cs = sorted(C, key=ang)
    for i in range(len(Cs)):
        lo, hi = ang(Cs[i]), ang(Cs[(i+1) % len(Cs)])
        def inside(v):
            a = ang(v); return (lo < a < hi) if lo < hi else (a > lo or a < hi)
        if any(inside(v) for v in A) and any(inside(v) for v in B): return False
    return True
def canon(P): return tuple(sorted(P))
def random_pair(rng):
    C = BOX + rng.sample([v for v in pool if v not in BOX], rng.randint(0, 2))
    rest = [v for v in pool if v not in C]
    A = rng.sample(rest, rng.randint(1, 2)); B = rng.sample([v for v in rest if v not in A], rng.randint(1, 2))
    return C, A, B
rng = random.Random(7); fin = inf = contra = joinbad = 0
for trial in range(300):
    C, A, B = random_pair(rng)
    pts = [(Fr(rng.randint(-5, 5)), Fr(rng.randint(-5, 5))) for _ in range(rng.randint(3, 6))]
    if len({p[0] for p in pts}) < 2 or len({p[1] for p in pts}) < 2: continue
    P = rho(C + A, rho(C + B, pts))
    if len(P) < 3: continue
    stab = False
    for k in range(60):
        Q = rho(C + A, rho(C + B, P))
        if canon(Q) == canon(P): stab = True; break
        P = Q
    if stab:
        fin += 1
        if canon(P) != canon(rho(C, P)): joinbad += 1
    else:
        inf += 1
        if arc_condition(C, A, B): contra += 1
print("  stabilised runs:", fin, " join != rho_C(S):", joinbad, " non-stabilised runs (60 rounds):", inf,
      " of which satisfy the arc condition (should be 0):", contra)
rng = random.Random(11); built = bad = 0
for trial in range(200):
    C, A, B = random_pair(rng)
    if arc_condition(C, A, B): continue
    Cs = sorted(C, key=ang); t = None
    for i in range(len(Cs)):
        lo, hi = ang(Cs[i]), ang(Cs[(i+1) % len(Cs)])
        def inside(v):
            a = ang(v); return (lo < a < hi) if lo < hi else (a > lo or a < hi)
        a_dirs = [v for v in A if inside(v)]; b_dirs = [v for v in B if inside(v)]
        if a_dirs and b_dirs: t = a_dirs[0]; break
    P = [(Fr(0), Fr(0)), (Fr(1), Fr(0)), (Fr(1), Fr(1)), (Fr(0), Fr(1))]      # the unit square is C-closed
    vals = sorted({t[0]*p[0] + t[1]*p[1] for p in P})
    alpha = vals[-1] - (vals[-1] - vals[-2]) / 100
    Pk = clip(P, t, alpha); stab = False
    for k in range(40):
        Q = rho(C + A, rho(C + B, Pk))
        if canon(Q) == canon(Pk): stab = True; break
        Pk = Q
    built += 1; bad += stab
print("  pairs violating the arc condition:", built, " sets P cap {t.x <= alpha} that stabilised (should be 0):", bad)

# three-dimensional example: C = box, T = C + (1,2,1), T' = C + (2,1,0): no box has a critical face, so
# every bounded full-dimensional set stabilises, while the plane x_3 = 0 carries the planar pair (1,2), (2,1)
print("== R^3 example: box + (1,2,1) against box + (2,1,0) (exact vertex enumeration)")
import itertools
def solve3(rows):
    # rows: three (t, c); solve t.x = c exactly; return None if singular
    M = [list(map(Fr, t)) + [Fr(c)] for t, c in rows]
    n = 3
    for i in range(n):
        piv = next((r for r in range(i, n) if M[r][i] != 0), None)
        if piv is None: return None
        M[i], M[piv] = M[piv], M[i]
        for r in range(n):
            if r != i and M[r][i] != 0:
                f = M[r][i] / M[i][i]
                M[r] = [M[r][j] - f * M[i][j] for j in range(n + 1)]
    return tuple(M[i][n] / M[i][i] for i in range(n))
def vertices(cons):
    V = set()
    for rows in itertools.combinations(cons, 3):
        x = solve3(rows)
        if x is None: continue
        if all(sum(t[i]*x[i] for i in range(3)) <= c for t, c in cons): V.add(x)
    return V
def support(V, t): return max(sum(t[i]*v[i] for i in range(3)) for v in V)
BOX3 = [(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)]
a, b = (1,2,1), (2,1,0)
def closure(T, V):
    """template closure of the point set / vertex set V: constraints t.x <= sup_V t for t in T."""
    cons = [(t, support(V, t)) for t in T]
    return cons, vertices(cons)
def alternate(pts, rounds):
    V = set(pts); sigs = None
    for k in range(rounds):
        _, V = closure(BOX3 + [b], V)      # rho_{T'}
        cons, V = closure(BOX3 + [a], V)   # rho_T
        sig = tuple(c for _, c in cons)
        if sig == sigs: return k          # stabilised (same T-polyhedron)
        sigs = sig
    return None
random.seed(5); worst = 0; unstable = 0
for trial in range(150):
    pts = [tuple(Fr(random.randint(-4, 4)) for _ in range(3)) for _ in range(random.randint(4, 7))]
    # full-dimensional: make sure the points are not coplanar
    if len({p[0] for p in pts}) < 2 or len({p[1] for p in pts}) < 2 or len({p[2] for p in pts}) < 2: continue
    r = alternate(pts, 25)
    if r is None: unstable += 1
    else: worst = max(worst, r)
print("random full-dimensional sets in R^3: max rounds", worst, " non-stabilised (25 rounds, should be 0):", unstable)
# planar set S = [0,1]^2 x {0} cap {x + 2y <= 5/2}
pts = [(Fr(0),Fr(0),Fr(0)), (Fr(1),Fr(0),Fr(0)), (Fr(0),Fr(1),Fr(0)), (Fr(1),Fr(3,4),Fr(0)), (Fr(1,2),Fr(1),Fr(0))]
V = set(pts)
for k in range(6):
    _, V = closure(BOX3 + [b], V); cons, V = closure(BOX3 + [a], V)
    print("  planar S, round", k + 1, ": alpha =", support(V, a), " (3 - 4^-k/2 =", 3 - Fr(1,2)/4**(k+1), ") z-range", min(v[2] for v in V), max(v[2] for v in V))
print("== different quadrants: T = box + (1,2), T' = box + (-1,2): alternation from random S")
import random
random.seed(1)
T = BOX + [(1, 2)]; T2 = BOX + [(-1, 2)]
worst = 0
for trial in range(300):
    pts = [(Fr(random.randint(-20, 20), random.randint(1, 4)), Fr(random.randint(-20, 20), random.randint(1, 4))) for _ in range(random.randint(1, 5))]
    # convex hull via rho with all directions? just use polygon = rho_all of points: use box+many directions
    allT = BOX + DIA + [(1, 2), (2, 1), (-1, 2), (1, -2), (2, -1), (-2, 1)]
    P = rho(allT, pts)  # a polygon containing pts (fine: alternation of rho(allT,pts) tests a different S)
    for S0 in (P, hull_box(pts) if len(pts) > 1 else P):
        seq = [S0]; Q = S0
        for k in range(12):
            Q2 = rho(T, rho(T2, Q))
            if sorted(Q2) == sorted(Q): break
            Q = Q2; seq.append(Q)
        else:
            print("  NOT stabilised within 12:", pts); break
        worst = max(worst, len(seq) - 1)
print("  max number of rounds to stabilise:", worst)

print("== box vs diagonal box on Z^2 from {(0,0),(2,0)}: sizes of iterates")
def zhull(T, S):
    sup = {t: max(t[0]*p[0] + t[1]*p[1] for p in S) for t in T}
    inf = {t: -sup[(-t[0], -t[1])] for t in T}
    xs = [p[0] for p in S]; ys = [p[1] for p in S]
    R = 2*max(max(map(abs, xs)), max(map(abs, ys))) + 2
    return frozenset((x, y) for x in range(-R, R+1) for y in range(-R, R+1)
                     if all(t[0]*x + t[1]*y <= sup[t] for t in T))
S = frozenset({(0, 0), (2, 0)}); sizes = []
for k in range(6):
    S = zhull(BOX, zhull(DIA, S)); sizes.append(len(S))
print("  sizes:", sizes)
S = frozenset({(0, 0), (1, 0)}); print("  {(0,0),(1,0)} fixed by both:", zhull(DIA, S) == S == zhull(BOX, S))

print("== congruences vs intervals / octagons on Z^2: alternation from random finite S (window check)")
from math import gcd
def lattice_closure(S):
    """affine lattice generated by S: (p, basis) with basis in Hermite normal form (2D), by Euclid."""
    S = list(S); p = S[0]
    rows = [[q[0]-p[0], q[1]-p[1]] for q in S[1:] if q != p]
    rows = [r for r in rows if r != [0, 0]]
    # Euclid on the first coordinates
    while sum(1 for r in rows if r[0] != 0) > 1:
        nz = sorted([r for r in rows if r[0] != 0], key=lambda r: abs(r[0]))
        piv = nz[0]; rest = [r for r in rows if r is not piv]
        rows = [piv] + [[r[0] - (r[0] // piv[0]) * piv[0], r[1] - (r[0] // piv[0]) * piv[1]] if r[0] != 0 else r for r in rest]
        rows = [r for r in rows if r != [0, 0]]
    g = 0
    for r in rows:
        if r[0] == 0: g = gcd(g, abs(r[1]))
    basis = [r for r in rows if r[0] != 0]
    if g: basis.append([0, g])
    if basis and basis[0][0] != 0 and g: basis[0][1] %= g
    if basis and basis[0][0] < 0: basis[0] = [-basis[0][0], -basis[0][1]]
    return p, [tuple(b) for b in basis]

def lattice_points(p, basis, R):
    pts = set()
    rng = range(-2*R, 2*R+1)
    if len(basis) == 0: return {p}
    if len(basis) == 1:
        for i in rng:
            x, y = p[0] + i*basis[0][0], p[1] + i*basis[0][1]
            if abs(x) <= R and abs(y) <= R: pts.add((x, y))
    else:
        for i in rng:
            for j in rng:
                x = p[0] + i*basis[0][0] + j*basis[1][0]; y = p[1] + i*basis[0][1] + j*basis[1][1]
                if abs(x) <= R and abs(y) <= R: pts.add((x, y))
    return pts

OCT = BOX + DIA
random.seed(3); worst = 0
for trial in range(40):
    pts = {(random.randint(-6, 6), random.randint(-6, 6)) for _ in range(random.randint(1, 4))}
    for T in (BOX, OCT):
        R = 16
        cur = pts; hist = []
        for k in range(8):
            p, basis = lattice_closure(cur)
            L = lattice_points(p, basis, R)          # kappa(cur) within the window
            # template hull of the lattice: sup over the window approximates sup over the lattice:
            # for directions not orthogonal to the lattice directions the sup is +infinity; detect by window growth
            sup = {}
            for t in T:
                vals = [t[0]*q[0] + t[1]*q[1] for q in L]
                m = max(vals)
                unbounded = any(t[0]*b[0] + t[1]*b[1] != 0 for b in basis)
                sup[t] = None if unbounded else m
            H = {(x, y) for x in range(-R, R+1) for y in range(-R, R+1)
                 if all(sup[t] is None or t[0]*x + t[1]*y <= sup[t] for t in T)}
            key = (p, tuple(basis), len(H))
            if hist and hist[-1] == key: break
            hist.append(key); cur = H
        worst = max(worst, len(hist))
print("  max rounds (kappa then rho_T) before stabilisation, window 16:", worst)
