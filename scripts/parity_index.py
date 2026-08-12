"""Classification program, step 1: the parity index for n = 2.

For each h in B_2 (signed permutations of {x,y}, order 8) decide:
  - fp(h): does rho.sigma_h have a fixed point on the literal cube?
    (if yes, phi.h = ~phi is unsatisfiable pointwise - the general
    form of the two parity lemmas of the separation paper)
  - sol(h): does a monotone phi in DM(2) with phi.h = ~phi exist?
    (exhaustive; monotonicity can obstruct beyond parity)
For each subgroup H of B_2: enumerate characters chi: H -> Z/2 and
decide realizability: exists phi with phi.h = neg^{chi(h)} phi for
all h.  Cross-check the isotropy pattern (free / fixed-cell /
fixed-layer) recorded in O12.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from collage_type_lib import build, monotone_masks, NOT, gen

N, leq, rho_ = build(2)
dm = monotone_masks(N, leq)
notf = {m: NOT(m, N, rho_) for m in dm}
X, Y = gen(0,2,N), gen(1,2,N)

def coords(p): return [(p>>i)&1 for i in range(4)]
def frompt(c): return sum(b<<i for i,b in enumerate(c))

# signed permutation h = (perm, signs): perm a permutation of (0,1)
# (pair indices), signs in {0,1}^2 (1 = reversal on that slot).
# Action on literal-cube points: the substitution x_i := (~)^{s} x_{perm(i)}
# acts on a point p by: new pair j gets old pair ... implement via mask
# transform on functions: (phi.h)(p) = phi(h*p) with h* the induced
# point map: pair i of h*p = pair perm(i) of p, swapped iff sign_i.
def point_map(perm, signs):
    mp = []
    for p in range(N):
        c = coords(p)
        d = [0]*4
        for i in (0,1):
            src = perm[i]
            a, b = c[2*src], c[2*src+1]
            if signs[i]: a, b = b, a
            d[2*i], d[2*i+1] = a, b
        mp.append(frompt(d))
    return mp

def act(m, mp):
    r = 0
    for p in range(N):
        if (m >> mp[p]) & 1: r |= 1 << p
    return r

ELEMS = []
for perm in [(0,1),(1,0)]:
    for signs in itertools.product((0,1),(0,1)):
        ELEMS.append((perm, signs))
PM = {e: point_map(*e) for e in ELEMS}
NAMES = {}
for e in ELEMS:
    perm, signs = e
    nm = ('sw' if perm==(1,0) else '') + ('.nx' if signs[0] else '') + ('.ny' if signs[1] else '')
    NAMES[e] = nm if nm else 'id'

# sanity: check against known SW and NB
def swp(p):
    vx,vnx,vy,vny = p&1,(p>>1)&1,(p>>2)&1,(p>>3)&1
    return vy|(vny<<1)|(vx<<2)|(vnx<<3)
assert PM[((1,0),(0,0))] == [swp(p) for p in range(N)]

# rho on points (pair-swap-with-complement per pair)
rho_pt = []
for p in range(N):
    c = coords(p)
    d = [1-c[1], 1-c[0], 1-c[3], 1-c[2]]
    rho_pt.append(frompt(d))

print("h : fp(rho.sigma_h)  antidual-solvable  #antiduals")
sol = {}
for e in ELEMS:
    mp = PM[e]
    fp = any(rho_pt[mp[p]] == p or mp[rho_pt[p]] == p for p in range(N))
    ads = [m for m in dm if act(m, mp) == notf[m]]
    sol[e] = ads
    print(f"{NAMES[e]:8s}: fixed-point={str(fp):5s}  solvable={str(len(ads)>0):5s}  n={len(ads)}")

# ---- subgroups of B_2 (order 8, dihedral) ----
def mul(e1, e2):
    """composite h1.h2 as substitution: point map = pm2 then pm1?  Define
    via composition of point maps and match to an element."""
    m = [PM[e1][PM[e2][p]] for p in range(N)]
    for e in ELEMS:
        if PM[e] == m: return e
    raise RuntimeError
def close(gens):
    S = {((0,1),(0,0))}
    frontier = set(gens)
    while frontier:
        S |= frontier
        frontier = {mul(a,b) for a in S for b in S} - S
    return frozenset(S)

subgroups = set()
for r in range(4):
    for gens in itertools.combinations(ELEMS, r):
        subgroups.add(close(gens))
subgroups = sorted(subgroups, key=len)
print(f"\nsubgroups of B_2: {len(subgroups)}")

# isotropy pattern: fixed cells of h = monotone m with act(m-pair...)
# cell of square = pair (m1,m2); h fixes a cell iff (m1,m2).h = (m1,m2).
# For pattern classification use level-1/2 fixed-cell existence per h != id.
def has_fixed_cell(H):
    """does some h != id in H fix a nonempty cell of square^2?
    The action on cells is POST-composition: h.(m1,m2) = h∘(m1,m2)
    = ((¬)^{s0} m_{perm(0)}, (¬)^{s1} m_{perm(1)}), ¬ = full negation."""
    out = {}
    for e in H:
        if e == ((0,1),(0,0)): continue
        perm, signs = e
        found = False
        for m1 in dm:
            for m2 in dm:
                comp = [m1, m2]
                r1 = comp[perm[0]]
                r2 = comp[perm[1]]
                if signs[0]: r1 = notf[r1]
                if signs[1]: r2 = notf[r2]
                if (r1, r2) == (m1, m2):
                    found = True; break
            if found: break
        out[e] = found
    return out

# character realizability for subgroup H: chi: H -> Z/2 hom;
# realizable iff exists m in dm with act(m, PM[h]) == (notf[m] if chi(h) else m) for all h
def characters(H):
    Hl = sorted(H, key=lambda e: NAMES[e])
    chis = []
    for bits in itertools.product((0,1), repeat=len(Hl)):
        chi = dict(zip(Hl, bits))
        if chi[((0,1),(0,0))] != 0: continue
        if all(chi[mul(a,b)] == (chi[a]+chi[b])%2 for a in Hl for b in Hl):
            chis.append(chi)
    return chis

print("\nH (gens) | order | some h!=id fixes a cell? | realizable characters (nontrivial count)")
for H in subgroups:
    Hs = sorted(H, key=lambda e: NAMES[e])
    names = ",".join(NAMES[e] for e in Hs if e != ((0,1),(0,0)))
    fx = has_fixed_cell(H)
    anyfix = any(fx.values()) if fx else False
    allfix = all(fx.values()) if fx else True
    chis = characters(H)
    real = []
    for chi in chis:
        ok = any(all(act(m, PM[h]) == (notf[m] if chi[h] else m) for h in H) for m in dm)
        if ok: real.append(chi)
    ntriv = sum(1 for chi in real if any(chi[h] for h in H))
    print(f"|H|={len(H):2d} [{names:20s}] fix-cell(any h)={str(anyfix):5s} all-h-fix={str(allfix):5s} "
          f"chars={len(chis)} realizable={len(real)} nontrivial-realizable={ntriv}")
