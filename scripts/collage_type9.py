"""(T-C) part 9: strict quotient-level sections of Phi-bar.

Among K-invariant interior classes [c] of J/K([2]) (part 8), find
those with Phi-bar([c]) = w = [(x,y)] in W([2]):
  (F(d,a,t), F(d,~a,t))  in  K-orbit {(x,y),(y,x),(~x,~y),(~y,~x)}.
Such a class defines a strict presheaf map g: W -> J/K with
Phi-bar . g = id_W  — a strict section at the quotient level.
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
    d,a,t = c
    if t == 0:   return ('D', min(d, notf[d]))
    if t == FULL:return ('A', min(a, notf[a]))
    return ('C', min([(d,a,t),(d,notf[a],t),(notf[d],notf[a],t),(notf[d],a,t)]))

def F(d,a,t): return (d & notf[t]) | (a & t) | (d & a)

W_TARGET = {(X,Y),(Y,X),(notf[X],notf[Y]),(notf[Y],notf[X])}

hits = []
for d in dm:
    for a in dm:
        for t in dm:
            if t == 0 or t == FULL: continue
            F1, F2 = F(d,a,t), F(d,notf[a],t)
            if (F1,F2) not in W_TARGET: continue
            c = (d,a,t); n0 = norm(c)
            if norm((SW(d),SW(a),SW(t))) != n0: continue
            if norm((NB(d),NB(a),NB(t))) != n0: continue
            hits.append((d,a,t,F1,F2))
print("strict quotient-level sections:", len(hits))
names = {0:'0', FULL:'1', X:'x', Y:'y', notf[X]:'~x', notf[Y]:'~y'}
def nm(m): return names.get(m, str(m))
for d,a,t,F1,F2 in hits[:12]:
    print(f"  d={nm(d)}({d}) a={nm(a)}({a}) t={nm(t)}({t})  Phi=({nm(F1)},{nm(F2)})")
