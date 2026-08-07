"""(T-C) part 11: quotient-essential invariant classes.

A K-invariant class [c] of J/K([2]) factors through the contractible
cover J iff some representative c' in its K_J-orbit satisfies
c'∘sw = c' and c'∘nb = c' strictly (as cells of J, i.e., component-wise
up to end-collapse).  Such classes give NULL maps W -> R(J/K)
(type(J) = join(*,*) = *).  Census: which of the invariant classes are
*essential* (no strictly invariant representative), and which of those
have the required crossing boundary pattern [l, l.rev, l, l.rev]?
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
def face(m, var, e):
    r=0
    for p in range(N):
        if var==0: q=(p&~0b11)|(0b10 if e==0 else 0b01)
        else: q=(p&~0b1100)|(0b1000 if e==0 else 0b0100)
        if (m>>q)&1: r|=1<<p
    return r
def to1(m2, var, e):
    f2 = face(m2, var, e); r=0
    for vy in (0,1):
        for vny in (0,1):
            if var==0: p = 0b10 | (vy<<2) | (vny<<3)
            else: p = (vy) | (vny<<1) | 0b1000
            if (f2>>p)&1: r |= 1 << (vy | (vny<<1))
    return r
N1, leq1, rho1 = build(1)
not1 = {m: NOT(m,N1,rho1) for m in monotone_masks(N1,leq1)}
X1 = gen(0,1,N1); FULL1=(1<<N1)-1
def norm1(c):
    d,a,t = c
    if t==0: return ('D', min(d,not1[d]))
    if t==FULL1: return ('A', min(a,not1[a]))
    return ('C', min([(d,a,t),(d,not1[a],t),(not1[d],not1[a],t),(not1[d],a,t)]))
L = norm1((0,0,X1)); LR = norm1((0,0,not1[X1]))

def norm2(c):
    d,a,t = c
    if t==0: return ('D', min(d,notf[d]))
    if t==FULL: return ('A', min(a,notf[a]))
    return ('C', min([(d,a,t),(d,notf[a],t),(notf[d],notf[a],t),(notf[d],a,t)]))

def orbit(c):
    d,a,t = c
    return [(d,a,t),(d,notf[a],t),(notf[d],notf[a],t),(notf[d],a,t)]

seen = {}
for d in dm:
    for a in dm:
        for t in dm:
            if t == 0 or t == FULL: continue
            c = (d,a,t); n0 = norm2(c)
            if n0 in seen: continue
            if norm2((SW(d),SW(a),SW(t))) != n0: continue
            if norm2((NB(d),NB(a),NB(t))) != n0: continue
            # essential? check all 4 representatives for strict invariance
            strict = any(SW(dd)==dd and SW(aa)==aa and SW(tt)==tt and
                         NB(dd)==dd and NB(aa)==aa and NB(tt)==tt
                         for (dd,aa,tt) in orbit(c))
            # boundary pattern
            faces = [norm1((to1(d,v,e), to1(a,v,e), to1(t,v,e)))
                     for v in (0,1) for e in (0,1)]
            good_bdy = faces == [L,LR,L,LR]
            seen[n0] = (strict, good_bdy, c)

ess = [(k,v) for k,v in seen.items() if not v[0]]
essb = [(k,v) for k,v in ess if v[1]]
strb = [(k,v) for k,v in seen.items() if v[0] and v[1]]
print(f"interior invariant classes: {len(seen)}; essential: {len(ess)}; "
      f"essential with l-boundary: {len(essb)}; factoring with l-boundary: {len(strb)}")
for k,v in essb[:10]:
    print("  essential+boundary:", v[2])
