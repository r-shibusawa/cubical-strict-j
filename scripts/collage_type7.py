"""(T-C) part 7: design space of equivariant approximate sections.

sigma_0 = (d,a,t) in DM(x,y)^3 with:
  sw:  d^sw = d,  a^sw = ~a,  t^sw = t     (sw = swap generators x<->y)
  nb:  d^nb = ~d, a^nb = ~a,  t^nb = t     (nb = negate both generators)
Then gamma . sigma_0 is a strictly K-invariant square of R(J/K) up to
the J-side action identification (sw_J = (d,~a,t), nb_J = (~d,~a,t)).

For each equivariant triple, measure the boundary defect of
Phi . sigma_0 = (F(d,a,t), F(d,~a,t)) against the generic cell (x,y):
count which of the 4 faces (x:=0,1 / y:=0,1) agree strictly.
"""
import sys
sys.path.insert(0, 'scripts')
from collage_type_lib import build, monotone_masks, NOT, gen

N, leq, rho = build(2)
dm = monotone_masks(N, leq)
notf = {m: NOT(m, N, rho) for m in dm}
X, Y = gen(0, 2, N), gen(1, 2, N)
FULL = (1 << N) - 1

# generator swap on L_2 points: (vx,vnx,vy,vny) -> (vy,vny,vx,vnx)
def swp(p):
    vx, vnx, vy, vny = p & 1, (p >> 1) & 1, (p >> 2) & 1, (p >> 3) & 1
    return vy | (vny << 1) | (vx << 2) | (vnx << 3)
def SW(m):
    r = 0
    for p in range(N):
        if (m >> swp(p)) & 1:
            r |= 1 << p
    return r
# negate-both on masks: substitution x->~x, y->~y.  On the up-set
# representation this is m -> mask over points with both pairs swapped
# (literal swap WITHOUT complement: x<->~x means coordinate swap):
def lswap(p):
    vx, vnx, vy, vny = p & 1, (p >> 1) & 1, (p >> 2) & 1, (p >> 3) & 1
    return vnx | (vx << 1) | (vny << 2) | (vy << 3)
def NB(m):
    r = 0
    for p in range(N):
        if (m >> lswap(p)) & 1:
            r |= 1 << p
    return r

# sanity: NB(X) == ~x-mask == NOT(X)?  substitution x:=~x sends the
# generator x to ~x, so NB(X) must equal notf[X]:
assert NB(X) == notf[X] and NB(Y) == notf[Y]
assert SW(X) == Y and SW(Y) == X
assert SW(X & Y) == (X & Y)

def F(d, a, t): return (d & notf[t]) | (a & t) | (d & a)

# face substitutions x:=e, y:=e on masks: evaluate mask with pair forced.
def face(m, var, e):
    # var 0 = x (bits 0,1), 1 = y (bits 2,3); e in {0,1}
    # substitution x:=0 sets pair (vx,vnx)=(0,1); result in DM(y) but we
    # keep it embedded in DM(x,y) as a mask independent of x-pair:
    r = 0
    for p in range(N):
        if var == 0:
            q = (p & ~0b11) | (0b10 if e == 0 else 0b01)
        else:
            q = (p & ~0b1100) | (0b1000 if e == 0 else 0b0100)
        if (m >> q) & 1:
            r |= 1 << p
    return r

eqv = []
for d in dm:
    if SW(d) != d or NB(d) != notf[d]:
        continue
    for a in dm:
        if SW(a) != notf[a] or NB(a) != notf[a]:
            continue
        for t in dm:
            if SW(t) != t or NB(t) != t:
                continue
            eqv.append((d, a, t))
print("equivariant triples:", len(eqv))

best = []
for (d, a, t) in eqv:
    F1, F2 = F(d, a, t), F(d, notf[a], t)
    score = 0
    # faces of (F1,F2) vs faces of (x,y):
    for var, e, tx, ty in ((0,0,0,Y),(0,1,FULL,Y),(1,0,X,0),(1,1,X,FULL)):
        fx = face(F1, var, e); fy = face(F2, var, e)
        wx = face(tx if isinstance(tx,int) else tx, var, e) if False else None
        # target faces of (x,y): x:=0 -> (0, y); x:=1 -> (1, y);
        # y:=0 -> (x, 0); y:=1 -> (x, 1)
        tgt1 = face(X, var, e); tgt2 = face(Y, var, e)
        if fx == tgt1 and fy == tgt2:
            score += 1
    best.append((score, d, a, t, F1, F2))

best.sort(reverse=True)
from collections import Counter
print("face-match distribution:", Counter(s for s,*_ in best))
for s, d, a, t, F1, F2 in best[:8]:
    print(f"  score {s}: d={d} a={a} t={t}  Phi=({F1},{F2})")
# name a few masks for readability
names = {0:'0', FULL:'1', X:'x', Y:'y', notf[X]:'~x', notf[Y]:'~y',
         X&Y:'x&y', X|Y:'x|y', X&notf[X]:'x&~x', (X&notf[X])|(Y&notf[Y]):'x&~x|y&~y'}
print("legend:", {v:k for k,v in names.items()})
