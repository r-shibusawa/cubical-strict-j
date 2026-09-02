"""Referee: concrete counterexample to thm:chext observation (i).
X := <z> for z = (x^y, x, xvy): [2]->[3].
 (a) every cell of X (levels <= 3) has pairwise comparable
     components  ==>  X is contained in Ch_3 (ambient chain part of
     the presentation atom B = X is ALL of B);
 (b) the generator cell z is NOT in Ch(X) (not an instance of any
     sorted cell of X, sorted parents at levels <= 3);
 (c) ker of z's classifying map cube^2 -> X is trivial at levels <= 3
     (so <x> = cube^2 and |L| = 5 beats the cube presentation's 6).
Hence at the chext step for x = z (with A = Ch(X)): S = preimage of
Ch(X) does NOT contain B cap Ch_3 = B  (z itself is ambient-chain but
maps to x, which is fresh).
"""
import sys, itertools
sys.path.insert(0, '/Users/shibusawa/Dev/DIT/FormalizedMathematics/scripts')
from dedekind_site import F, compose

pts2, D2 = F(2)
x = tuple(p[0] for p in pts2); y = tuple(p[1] for p in pts2)
mt = lambda a,b: tuple(u&v for u,v in zip(a,b))
jn = lambda a,b: tuple(u|v for u,v in zip(a,b))
z = (mt(x,y), x, jn(x,y))

def rest(cell, u, j, k):
    return tuple(compose(c, u, j, k) for c in cell)
def leq(a,b): return all(p<=q for p,q in zip(a,b))
def chain(t):
    return all(leq(a,b) or leq(b,a)
               for a,b in itertools.combinations(t,2))

K = 3
X = {}
for k in range(K+1):
    Dk = F(k)[1]
    X[k] = {rest(z, u, 2, k) for u in itertools.product(Dk, repeat=2)}

# (a)
alla = all(chain(c) for k in X for c in X[k])
print(f"(a) all cells of <z> (levels<=3) pairwise comparable: {alla}")

# (b) sorted cells of X and their instances at level 2
def sortsub(q):
    # sort_q = (o_1,...,o_q) as q-tuple over D(q)
    ptsq, _ = F(q)
    out = []
    for i in range(1, q+1):
        f = tuple(1 if sum(p) >= i else 0 for p in ptsq)
        out.append(f)
    return tuple(out)
chain_inst = set()
for q in range(K+1):
    sq = sortsub(q) if q > 0 else ()
    for s in X[q]:
        if q > 0 and rest(s, sq, q, q) != s: continue
        # s sorted; instances at level 2
        for d in itertools.product(D2, repeat=q):
            chain_inst.add(rest(s, d, q, 2))
print(f"(b) z in Ch(X) (via sorted parents at levels<=3): "
      f"{z in chain_inst}")

# (c) kernel triviality at levels <= 3
ok = True
for k in range(K+1):
    Dk = F(k)[1]
    seen = {}
    for u in itertools.product(Dk, repeat=2):
        c = rest(z, u, 2, k)
        if c in seen and seen[c] != u: ok = False
        seen[c] = u
print(f"(c) classifying map cube^2 -> <z> injective (levels<=3): {ok}")
