"""(T-C) part 10: the De Morgan XOR square — an explicit strict g.

Candidate: g(w) := s* = [(0, 0, t*)],  t* = (x&~y)|(~x&y).
Checks:
 (1) t* is sw-symmetric and nb-invariant; faces of t* are (y,~y;x,~x).
 (2) s* is a K-invariant class of J/K([2])  (so g: W -> J/K strict).
 (3) faces of s* are the crossing edge l = [(0,0,i)] and its reverse,
     matching the forced boundary pattern (l,l,l.rev,l.rev).
 (4) Phi-bar(s*) = [(0, t*)] and its four faces agree, as W-classes,
     with the faces of w = [(x,y)]  (same-boundary squares in W).
 (5) the composite g.Phi-bar on the generator: t*(F1,F2) in DM(d,a,t),
     and its face comparison with gamma's faces (same-boundary 3-cells
     in J/K) — the data for the remaining homotopy on the J-side.
"""
import sys
sys.path.insert(0, 'scripts')
from collage_type_lib import build, monotone_masks, NOT, gen

# ---------- DM(2) ----------
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

TSTAR = (X & notf[Y]) | (notf[X] & Y)
assert TSTAR in dm
print("(1) t* sym:", SW(TSTAR)==TSTAR, " nb-inv:", NB(TSTAR)==TSTAR)
print("    faces:", face(TSTAR,0,0)==Y, face(TSTAR,0,1)==notf[Y],
      face(TSTAR,1,0)==X, face(TSTAR,1,1)==notf[X])

def norm2(c):
    d,a,t = c
    if t==0: return ('D', min(d,notf[d]))
    if t==FULL: return ('A', min(a,notf[a]))
    return ('C', min([(d,a,t),(d,notf[a],t),(notf[d],notf[a],t),(notf[d],a,t)]))

s = (0,0,TSTAR)
print("(2) s* K-invariant class:",
      norm2((SW(0),SW(0),SW(TSTAR)))==norm2(s),
      norm2((NB(0),NB(0),NB(TSTAR)))==norm2(s))

# (3) faces of s* as J/K([1])-classes vs l=[(0,0,i)] and reversed
N1, leq1, rho1 = build(1)
dm1 = monotone_masks(N1, leq1)
not1 = {m: NOT(m,N1,rho1) for m in dm1}
X1 = gen(0,1,N1); FULL1=(1<<N1)-1
def norm1(c):
    d,a,t = c
    if t==0: return ('D', min(d,not1[d]))
    if t==FULL1: return ('A', min(a,not1[a]))
    return ('C', min([(d,a,t),(d,not1[a],t),(not1[d],not1[a],t),(not1[d],a,t)]))
L = norm1((0,0,X1)); LR = norm1((0,0,not1[X1]))
fx0 = norm1((0,0,Y and 0 or 0, ))
# faces of s*: substitute in DM(2)->DM(1): var x:=e gives t*-face in y etc.
def to1(m2, var, e):
    """face of a DM(2) mask, re-expressed as DM(1) mask in the surviving var."""
    f2 = face(m2, var, e)
    # surviving variable: y if var==0 else x ; project 16-bit to 4-bit
    r=0
    for vy in (0,1):
        for vny in (0,1):
            if var==0: p = 0b10 | (vy<<2) | (vny<<3)  # x-pair fixed by face; read (vy,vny)
            else: p = (vy) | (vny<<1) | 0b1000
            if (f2>>p)&1: r |= 1 << (vy | (vny<<1))
    return r
faces_s = [norm1((0,0,to1(TSTAR,0,0))), norm1((0,0,to1(TSTAR,0,1))),
           norm1((0,0,to1(TSTAR,1,0))), norm1((0,0,to1(TSTAR,1,1)))]
print("(3) faces of s* = [l, l.rev, l, l.rev]:", faces_s == [L,LR,L,LR],
      " (l != l.rev:", L != LR, ")")

# (4) Phi(s*) and boundary agreement with w
def F(d,a,t): return (d & notf[t]) | (a & t) | (d & a)
P1, P2 = F(0,0,TSTAR), F(0,FULL,TSTAR)
print("(4) Phi(s*) = (0, t*):", P1==0 and P2==TSTAR)
def wnorm2(c):
    x,y = c
    return min([(x,y),(y,x),(notf[x],notf[y]),(notf[y],notf[x])])
def wnorm1(c):
    x,y = c
    return min([(x,y),(y,x),(not1[x],not1[y]),(not1[y],not1[x])])
def wface1(cell, var, e):
    x,y = cell
    return (to1(x,var,e), to1(y,var,e))
ok4 = all(wnorm1(wface1((P1,P2),v,e)) == wnorm1(wface1((X,Y),v,e))
          for v in (0,1) for e in (0,1))
print("    boundary classes of Phi(s*) == boundary of w:", ok4)

# (5) g.Phi-bar on the generator: t*(F1,F2) in DM(d,a,t) (3 vars)
N3, leq3, rho3 = build(3)
D3, A3, T3 = gen(0,3,N3), gen(1,3,N3), gen(2,3,N3)
def not3(m): return NOT(m,N3,rho3)
F1g = (D3 & not3(T3)) | (A3 & T3) | (D3 & A3)
F2g = (D3 & not3(T3)) | (not3(A3) & T3) | (D3 & not3(A3))
TS3 = (F1g & not3(F2g)) | (not3(F1g) & F2g)
print("(5) t*(F1,F2) computed; equals t alone?", TS3 == T3,
      "; equals t*(d,a)-independent of t?", TS3 == ((D3&not3(A3))|(not3(D3)&A3)))
