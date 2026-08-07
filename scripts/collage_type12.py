"""(T-C) part 12: torus-sweep search over projectively equivariant pairs.

P := { phi in DM(2) : phi^sw in {phi, ~phi}  and  phi^nb in {phi, ~phi} }
(the quotient identifications sa∘¬ = sa of the true R(J/K) absorb the
sign, so projective equivariance is the right strictness condition on
the seg-arguments alpha, beta).

For (alpha, beta) in P x P compute the EXACT mod-2 degree of the PL
realization (alpha, beta) : ([0,1]^2, d) -> ([0,1]^2, d):
DM functions are locally literals on the 12 regions cut by
x=y, x=1-y, x=1/2, y=1/2; a piece contributes iff it is a local
homeomorphism (one x-family literal, one y-family literal) whose
inverse image of the generic point c lies in the region.

Outcome: existence of deg=1 pairs decides whether K-invariant
torus-sweeping material is available (T-C positive path) or the
parity wall persists (separation scenario).
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from collage_type_lib import build, monotone_masks, NOT, gen

N, leq, rho = build(2)
dm = monotone_masks(N, leq)
notf = {m: NOT(m, N, rho) for m in dm}
X, Y = gen(0,2,N), gen(1,2,N)
def swp(p):
    vx,vnx,vy,vny = p&1,(p>>1)&1,(p>>2)&1,(p>>3)&1
    return vy|(vny<<1)|(vx<<2)|(vnx<<3)
def SW(m):
    r=0
    for p in range(N):
        if (m>>swp(p))&1: r|=1<<p
    return r
def lswap(p):
    vx,vnx,vy,vny = p&1,(p>>1)&1,(p>>2)&1,(p>>3)&1
    return vnx|(vx<<1)|(vny<<2)|(vy<<3)
def NB(m):
    r=0
    for p in range(N):
        if (m>>lswap(p))&1: r|=1<<p
    return r

P = [m for m in dm if SW(m) in (m, notf[m]) and NB(m) in (m, notf[m])]
print("|P| =", len(P))

# ---- PL realization from minimal points ----
def min_points(m):
    pts = [p for p in range(N) if (m>>p)&1]
    mins = []
    for p in pts:
        if not any(q != p and (m>>q)&1 and
                   all(((q>>i)&1) <= ((p>>i)&1) for i in range(4))
                   for q in range(N)):
            mins.append(p)
    return mins

def evalf(m, x, y):
    """max over minimal points of min of set literals."""
    best = 0.0
    lits = (x, 1-x, y, 1-y)
    got = False
    for p in min_points_cache[m]:
        vals = [lits[i] for i in range(4) if (p>>i)&1]
        v = min(vals) if vals else 1.0
        best = max(best, v); got = True
    return best if got else 0.0

min_points_cache = {m: min_points(m) for m in P}

# ---- regions and local literals ----
import random
random.seed(7)
LITS = [lambda x,y: x, lambda x,y: 1-x, lambda x,y: y, lambda x,y: 1-y,
        lambda x,y: 0.0, lambda x,y: 1.0]
LITNAMES = ['x','1-x','y','1-y','0','1']
def sigof(x,y):
    return (x>y, x>1-y, x>0.5, y>0.5)
# region representatives
reps = {}
for _ in range(20000):
    x, y = random.random(), random.random()
    s0 = sigof(x,y)
    if s0 not in reps:
        reps[s0] = (x,y)
print("regions found:", len(reps))

def local_lit(m, x, y):
    """identify which literal m equals near (x,y) (3-point match)."""
    pts = [(x,y), (x+1e-4,y+2e-4), (x-2e-4,y+1e-4)]
    for li, f in enumerate(LITS):
        if all(abs(evalf(m,a,b) - f(a,b)) < 1e-9 for a,b in pts):
            return li
    return None

def local_table(m):
    return {sig: local_lit(m, *pt) for sig, pt in reps.items()}

tables = {m: local_table(m) for m in P}
bad = [m for m in P if None in tables[m].values()]
print("P elements with unidentified local literal:", len(bad))

C1, C2 = 0.31371, 0.27183   # generic target point
def deg2(a, b):
    count = 0
    for sig in reps:
        la, lb = tables[a][sig], tables[b][sig]
        if la is None or lb is None: continue
        fam_a = 0 if la in (0,1) else (1 if la in (2,3) else None)
        fam_b = 0 if lb in (0,1) else (1 if lb in (2,3) else None)
        if fam_a is None or fam_b is None or fam_a == fam_b: continue
        # solve
        if fam_a == 0:
            xx = C1 if la == 0 else 1-C1
            yy = C2 if lb == 2 else 1-C2
        else:
            yy = C1 if la == 2 else 1-C1
            xx = C2 if lb == 0 else 1-C2
        if sigof(xx,yy) == sig:
            count += 1
    return count % 2

hits = []
for a in P:
    for b in P:
        if deg2(a,b) == 1:
            hits.append((a,b))
print("deg2 = 1 pairs in P x P:", len(hits))
for a,b in hits[:10]:
    print("  alpha mask", a, "(minpts", min_points_cache[a], ") beta mask", b,
          "(minpts", min_points_cache[b], ")")
