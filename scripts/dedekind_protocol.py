"""O27 stage 12: protocol design at n = 2 -- the canonical chamber
datum and its equivariance identities.

(1) SORT ABSORPTION: sort2 <> sortop = sort2, sortop <> sort2 =
    sortop, sort2 <> sort2 = sort2, sortop <> sortop = sortop;
    hence every sorted cell is fixed by BOTH sort idempotents,
    and f is defined on both chamber restrictions x.sort2,
    x.sortop, with automatic diagonal agreement.
(2) LEVEL-1 CHAIN FACT: D(1) is a chain, so every substitution
    [k<=1] -> [2] is a chain cell of cube^2: Ch_2 contains the
    full 1-truncation.
(3) CONFLICT LOCUS at level 2: enumerate pairs (x-presentation)
    of chain-instances: for cells of cube^2 itself (X = cube^2,
    universal case): a level-2 cell y in D(2)^2 is a chain
    instance if y = x <> sigma with sigma chain-valued
    ([2]->[2], comparable components) and x in D(2)^2.  Count
    cells with MULTIPLE essentially-different chain
    presentations (the well-definedness locus for forced
    values), modulo presentations with x' = x.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F
from collections import defaultdict

def to_int(t):
    n = 0
    for i, b in enumerate(t): n |= b << i
    return n

D = {k: [to_int(f) for f in F(k)[1]] for k in range(0, 3)}
pts2 = F(2)[0]
x1 = to_int(tuple(p[0] for p in pts2))
x2 = to_int(tuple(p[1] for p in pts2))
sort2 = (x1 | x2, x1 & x2)
sortop = (x1 & x2, x1 | x2)

def comp1(p, v, l, m):
    out = 0
    for x in range(1 << m):
        idx = 0
        for i in range(l):
            idx |= ((v[i] >> x) & 1) << i
        if (p >> idx) & 1: out |= 1 << x
    return out

def dia(u, v, l, m):
    """u = tuple over D(l) (map [l]->[n]); v = l-tuple over D(m):
    u <> v"""
    return tuple(comp1(c, v, l, m) for c in u)

# (1) absorption
print("sort2<>sortop == sort2:", dia(sort2, sortop, 2, 2) == sort2)
print("sortop<>sort2 == sortop:", dia(sortop, sort2, 2, 2) == sortop)
print("sort2<>sort2 == sort2:", dia(sort2, sort2, 2, 2) == sort2)
print("sortop<>sortop == sortop:", dia(sortop, sortop, 2, 2) == sortop)

# (2) level-<=1 restrictions are chain cells
def leq(a, b): return (a & b) == a
def chainv(c): return all(leq(a,b) or leq(b,a)
                          for a,b in itertools.combinations(c,2))
allchain = all(chainv(s) for s in itertools.product(D[1], repeat=2))
print("all [1]->[2] substitutions chain-valued:", allchain,
      "(D(1) is a chain)")

# (3) conflict locus on X = cube^2 at level 2
chain_subs = [s for s in itertools.product(D[2], repeat=2) if chainv(s)]
nonchain_subs = [s for s in itertools.product(D[2], repeat=2)
                 if not chainv(s)]
print(f"chain-valued [2]->[2] substitutions: {len(chain_subs)} "
      f"of 36")
# presentations: y = x <> sigma, sigma chain, x arbitrary cell of
# cube^2 (= substitution tuple), EXCLUDING trivial x = y itself
# via identity-like sigma?  identity is NOT chain (x1, x2
# incomparable) -- good: chain presentations are never identity.
pres = defaultdict(set)
for x in itertools.product(D[2], repeat=2):
    for sg in chain_subs:
        y = dia(x, sg, 2, 2)
        pres[y].add((x, sg))
multi = 0; nonchain_multi = []
for y, ps in pres.items():
    xs = set(p[0] for p in ps)
    if len(xs) > 1:
        multi += 1
        if not chainv(y): nonchain_multi.append(y)
print(f"level-2 cells that are chain-instances: {len(pres)} of 400; "
      f"with multiple source-x presentations: {multi}; "
      f"of these NON-chain (genuine conflict candidates): "
      f"{len(nonchain_multi)}")
# how bad: for a genuine conflict y, the forced value depends on
# (x, sigma); show an example
if nonchain_multi:
    y = nonchain_multi[0]
    ps = sorted(pres[y])[:3]
    print("  example y:", y, " presentations:", ps[:2])
