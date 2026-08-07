"""(T-C) part 8: invariant pure cells of J/K([2]).

Search all classes [c] in J/K([2]) (c = (d,a,t) in DM(x,y)^3, modulo
end-collapse and K_J) that are fixed by BOTH domain substitutions
sw: (i,j)->(j,i) and nb: (i,j)->(~i,~j) — the candidates for the
strictly K-invariant square g(w) that are pure reparametrizations.
"""
import sys
sys.path.insert(0, 'scripts')
from collage_type_lib import build, monotone_masks, NOT, gen

N, leq, rho = build(2)
dm = monotone_masks(N, leq)
notf = {m: NOT(m, N, rho) for m in dm}
X, Y = gen(0,2,N), gen(1,2,N)
FULL = (1<<N)-1

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

def norm(c):
    """Normal form of the class of c = (d,a,t) in J/K([2])."""
    d,a,t = c
    if t == 0:
        # end: only d matters, modulo residual negation
        return ('D', min(d, notf[d]))
    if t == FULL:
        return ('A', min(a, notf[a]))
    orbit = [(d,a,t), (d,notf[a],t), (notf[d],notf[a],t), (notf[d],a,t)]
    return ('C', min(orbit))

inv = []
for d in dm:
    for a in dm:
        for t in dm:
            c = (d,a,t)
            n0 = norm(c)
            if norm((SW(d),SW(a),SW(t))) != n0: continue
            if norm((NB(d),NB(a),NB(t))) != n0: continue
            inv.append(c)

# summarize by class
from collections import Counter
classes = Counter(norm(c) for c in inv)
kinds = Counter(k for (k, *_ ) in classes)
print("invariant pure classes:", len(classes), " by layer:", dict(kinds))
interior = [cl for cl in classes if cl[0] == 'C']
print("interior (cylinder) invariant classes:", len(interior))
for cl in interior[:10]:
    print("  ", cl)
