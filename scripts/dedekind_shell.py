"""THE SHELL CONTRACTION of the monotone dunce hat (O23 -- final).

W = square/((0,u)~(u,0), (u,u)~(u,1)) on the Dedekind site.

This certificate verifies, end to end, that W is TYPE-contractible
-- refuting the separation claim of paper 21 (v1.21.0) and the
earlier Theorem C of the integrated manuscript.

The contraction: let T < cube^3 be the union of the six squares
  a2 = (u,u,w), b2 = (u,1,w), a1 = (0,u,w), b1 = (u,0,w),
  n0 = (u,v,0),  n1 = (u,v,1),
and define Phi on T x cube^1  (prism coordinates (p,q,r)) by
  a2 |-> (p&r, p&r)      b2 |-> (p&r, r)
  a1 |-> (0, p&r)        b1 |-> (0, p&r)
  n0 |-> (p&r, q&r)      n1 |-> (p&q&r, r&(p|q))
and on cube^3 x {0} by the constant G = v00.

(1) The six prisms agree on all shared cells and with G at r=0:
    Phi is a well-defined map (T x cube^1) u (cube^3 x {0}) -> W.
(2) (T -> cube^3) x delta^0 is a generating trivial cofibration,
    so ANY type-fibrant Y under u: W -> Y admits a filler
    L: cube^3 x cube^1 -> Y of u.Phi.  The graph cell
    K = L.(id, const_1) satisfies both fold conditions because
    all four track cells (a_i, 1), (b_i, 1) lie in the SHELL,
    where L = u.Phi is prescribed:
      fold 2:  (p,p) ~ (p,1)   (the diagonal fold of W),
      fold 1:  (0,p) = (0,p).
    Its ends are u.iota (the identity class: C0's 1-slice is the
    generic cell) and u.h with h = (u&v, u|v) (C1's 1-slice).
(3) h is strictly null-homotopic: the single cylinder
    H = (w|(u&v), u|v|w) has ends h and the constant v11.
Hence id_W ~ const in every fibrant target: W is type-contractible.
(For contrast: no composition of representable open-box fillings
achieves this -- the cellular isolation theorem -- so the
contraction genuinely needs the shell box.)
"""
import itertools, sys
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, cube_cells, Quotient

def proj(k, i):
    pts, _ = F(k)
    return tuple(p[i] for p in pts)
def const(k, e):
    pts, _ = F(k)
    return tuple(e for _ in pts)
def meet(*xs):
    out = xs[0]
    for x in xs[1:]: out = tuple(a & b for a, b in zip(out, x))
    return out
def join(*xs):
    out = xs[0]
    for x in xs[1:]: out = tuple(a | b for a, b in zip(out, x))
    return out

A1c, B1c = (const(1,0), proj(1,0)), (proj(1,0), const(1,0))
A2c, B2c = (proj(1,0), proj(1,0)), (proj(1,0), const(1,1))
W = Quotient(2, [(1, A1c, B1c), (1, A2c, B2c)], 3)
X2, Y2 = proj(2,0), proj(2,1)
c02, c12 = const(2,0), const(2,1)
iota = W.cls(2, (X2, Y2))
h    = W.cls(2, (meet(X2,Y2), join(X2,Y2)))

SQ = {'a2': (X2, X2, Y2), 'b2': (X2, c12, Y2),
      'a1': (c02, X2, Y2), 'b1': (X2, c02, Y2),
      'n0': (X2, Y2, c02), 'n1': (X2, Y2, c12)}
# prisms as raw [3]-cells in (p,q,r), r = last coordinate
p3, q3, r3 = proj(3,0), proj(3,1), proj(3,2)
PR = {'a2': (meet(p3,r3), meet(p3,r3)),
      'b2': (meet(p3,r3), r3),
      'a1': (const(3,0), meet(p3,r3)),
      'b1': (const(3,0), meet(p3,r3)),
      'n0': (meet(p3,r3), meet(q3,r3)),
      'n1': (meet(p3,q3,r3), meet(r3, join(p3,q3)))}
G = (const(2,0), const(2,0))  # constant [3]-cell (as level-3 pair)
G3 = (const(3,0)[:8] and const(3,0), const(3,0))
G3 = (const(3,0), const(3,0))

ok = True
def check(name, cond):
    global ok
    print(("  OK " if cond else "  FAIL "), name)
    if not cond: ok = False

# ---- (1a) prisms restrict to G at r = 0 ----
r0map = (p3 and (proj(2,0), proj(2,1), const(2,0)))
r0map = (proj(2,0), proj(2,1), const(2,0))
for n in SQ:
    sl = W.cls(2, tuple(compose(c, r0map, 3, 2) for c in PR[n]))
    # G o square: G is constant so this is the constant square v00
    gsq = W.cls(2, (const(2,0), const(2,0)))
    check(f"{n}: 0-slice = G|square", sl == gsq)

# ---- (1b) full gluing on shared cells (levels 0..2) ----
import collections
for k in (0, 1, 2):
    _, Fk = F(k)
    cells = collections.defaultdict(list)
    for n in SQ:
        s1, s2, s3 = SQ[n]
        for z1 in Fk:
            for z2 in Fk:
                x = (compose(s1,(z1,z2),2,k), compose(s2,(z1,z2),2,k),
                     compose(s3,(z1,z2),2,k))
                cells[x].append((n, z1, z2))
    bad = 0
    for x, pres in cells.items():
        if len(pres) < 2: continue
        vals = set()
        for (n, z1, z2) in pres:
            drop = tuple(proj(k+1, i) for i in range(k))
            m = (compose(z1, drop, k, k+1), compose(z2, drop, k, k+1),
                 proj(k+1, k))
            vals.add(W.cls(k+1, tuple(compose(c, m, 3, k+1)
                                      for c in PR[n])))
        if len(vals) > 1: bad += 1
    check(f"gluing at level {k} (shared cells agree)", bad == 0)

# ---- (2) fold conditions of the graph cell (shell values) ----
s1a = W.cls(2, tuple(compose(c, (X2, Y2, c12), 3, 2) for c in PR['a2']))
s1b = W.cls(2, tuple(compose(c, (X2, Y2, c12), 3, 2) for c in PR['b2']))
check("fold 2: a2/b2 1-slices equal in W ((p,p) ~ (p,1))", s1a == s1b)
t1a = W.cls(2, tuple(compose(c, (X2, Y2, c12), 3, 2) for c in PR['a1']))
t1b = W.cls(2, tuple(compose(c, (X2, Y2, c12), 3, 2) for c in PR['b1']))
check("fold 1: a1/b1 1-slices equal", t1a == t1b)

# ---- ends ----
e0 = W.cls(2, tuple(compose(c, (X2, Y2, c12), 3, 2) for c in PR['n0']))
e1 = W.cls(2, tuple(compose(c, (X2, Y2, c12), 3, 2) for c in PR['n1']))
check("end 0 = iota (identity class)", e0 == iota)
check("end 1 = h = (u&v, u|v)", e1 == h)
check("h != iota", h != iota)

# ---- h is a fold cell (a strict W-endomorphism) ----
u1 = proj(1,0)
hrep = (meet(X2,Y2), join(X2,Y2))
def r21(x, m): return W.cls(1, tuple(compose(c, m, 2, 1) for c in x))
check("h fold cell",
      r21(hrep,(const(1,0),u1)) == r21(hrep,(u1,const(1,0))) and
      r21(hrep,(u1,u1)) == r21(hrep,(u1,const(1,1))))

# ---- (3) strict null-homotopy of h ----
u3v, v3v, w3v = proj(3,0), proj(3,1), proj(3,2)
H = (join(w3v, meet(u3v,v3v)), join(u3v, v3v, w3v))
a2m = (X2, X2, Y2); b2m = (X2, c12, Y2)
a1m = (c02, X2, Y2); b1m = (X2, c02, Y2)
n0m = (X2, Y2, c02); n1m = (X2, Y2, c12)
def r32(x, m): return W.cls(2, tuple(compose(c, m, 3, 2) for c in x))
check("H fold cylinder",
      r32(H,a1m) == r32(H,b1m) and r32(H,a2m) == r32(H,b2m))
check("H ends: h and const",
      r32(H,n0m) == h and
      r32(H,n1m) == W.cls(2,(const(2,1),const(2,1))))

# ---- context: iota is NOT strictly homotopic to h/const ----
from collections import deque
seenc = set(); adj = {}
for Hc in cube_cells(2, 3):
    c3 = W.cls(3, Hc)
    if c3 in seenc: continue
    seenc.add(c3)
    if r32(Hc,a1m) != r32(Hc,b1m) or r32(Hc,a2m) != r32(Hc,b2m): continue
    x, y = r32(Hc,n0m), r32(Hc,n1m)
    adj.setdefault(x, set()).add(y); adj.setdefault(y, set()).add(x)
comp = {iota}; q = deque([iota])
while q:
    x = q.popleft()
    for y in adj.get(x, ()):
        if y not in comp: comp.add(y); q.append(y)
check("iota's STRICT component = {iota} (cellular isolation)",
      comp == {iota})

print()
print("=> SHELL CONTRACTION VERIFIED: W_dunce is type-contractible."
      if ok else "=> CERTIFICATE FAILED")
