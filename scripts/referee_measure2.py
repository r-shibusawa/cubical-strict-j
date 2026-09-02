"""Decisive counterexample to 'proper inclusion of atoms strictly
decreases |L|' (thm:usub induction, lem:minpres measure):
  A  := <z2> for z2 = (u^v^w, u^v, u): [3]->[3]   (retractive
        five-chain embedding: atom = full 5-chain spectrum)
  y  := z2 o (xvy, x, y) = (x^y, x, xvy)  in A([2])
  <y> ~ cube^2 (prop:fivesquare), a PROPER subatom of A,
  yet |L(y)| = |L(z2)| = 5.
Check: cell counts of A and <y> at levels 0..3, membership, |L|'s.
"""
import sys, itertools
sys.path.insert(0, '/Users/shibusawa/Dev/DIT/FormalizedMathematics/scripts')
from dedekind_site import F, compose

def rest(cell, u, j, k):
    return tuple(compose(c, u, j, k) for c in cell)

pts3, D3 = F(3)
u3 = tuple(p[0] for p in pts3); v3 = tuple(p[1] for p in pts3)
w3 = tuple(p[2] for p in pts3)
mt = lambda a,b: tuple(x&y for x,y in zip(a,b))
jn = lambda a,b: tuple(x|y for x,y in zip(a,b))
z2 = (mt(mt(u3,v3),w3), mt(u3,v3), u3)

pts2, D2 = F(2)
x2 = tuple(p[0] for p in pts2); y2 = tuple(p[1] for p in pts2)
vsub = (jn(x2,y2), x2, y2)   # [2]->[3]
y = rest(z2, vsub, 3, 2)
print("y =", y, "(expect (x^y, x, xvy))")

def atom(z, j, lmax=3):
    out = {}
    for k in range(lmax+1):
        Dk = F(k)[1]
        out[k] = {rest(z, uu, j, k)
                  for uu in itertools.product(Dk, repeat=j)}
    return out

A = atom(z2, 3)
Y = atom(y, 2)
for k in range(4):
    sub = Y[k] <= A[k]
    print(f"level {k}: |A|={len(A[k])} |<y>|={len(Y[k])} "
          f"<y> subset of A: {sub}")

def subl(comps, k):
    npts = 1 << k
    S = set(comps) | {tuple(0 for _ in range(npts)),
                      tuple(1 for _ in range(npts))}
    ch = True
    while ch:
        ch = False
        cur = list(S)
        for a in cur:
            for b in cur:
                m = tuple(p&q for p,q in zip(a,b))
                j = tuple(p|q for p,q in zip(a,b))
                if m not in S: S.add(m); ch = True
                if j not in S: S.add(j); ch = True
    return len(S)

print("|L(z2)| =", subl(z2, 3), " |L(y)| =", subl(y, 2))
