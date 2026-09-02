"""O27 stage 8: the sorted-cell description of the singular functor.

Claim (lem:singsort): for any Dedekind cubical set X,
  Sing_D(X)_q = Hom(Delta^q_[], X)  ~=  {x in X([q]) : x . sort_q = x},
the fixed points of the sort substitution
  sort_q = (o_1, ..., o_q)  (order statistics),
with simplicial operators x |-> x . T(f) (which preserve
sortedness).  Verify on X = cube^n and on quotients:
 (i)  bijection between maps Delta^q -> X and sorted cells;
 (ii) closure: sorted cell . T(f) is sorted;
 (iii) counts for the cubical circle S^1 = cube^1/(v0 ~ v1).
Everything at the vertex/pointwise level (complete for identities;
for quotients we use the congruence-class representation).
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F

def to_int(t):
    n = 0
    for i, b in enumerate(t): n |= b << i
    return n

D = {k: [to_int(f) for f in F(k)[1]] for k in range(0, 5)}

def order_stat(k, x, m):
    if k <= 0: return (1 << (1 << m)) - 1  # constant 1 over 2^m pts
    if k > m: return 0
    out = 0
    for pt in range(1 << m):
        ones = bin(pt).count('1')
        if ones >= k: out |= 1 << pt
    return out

def sort_sub(q):
    """sort_q as a q-tuple of D(q)-ints: (o_1, ..., o_q)"""
    return tuple(order_stat(k, None, q) for k in range(1, q + 1))

def compose1(p, rho, l, k):
    out = 0
    for x in range(1 << k):
        idx = 0
        for i in range(l):
            idx |= ((rho[i] >> x) & 1) << i
        if (p >> idx) & 1: out |= 1 << x
    return out

def subst(cell, rho, l, k):
    """cell = n-tuple over D(l); rho = l-tuple over D(k)"""
    return tuple(compose1(c, rho, l, k) for c in cell)

# (i)+(ii) on X = cube^2 at q = 2, 3
for n in (1, 2):
    for q in (1, 2, 3):
        cells = list(itertools.product(D[q], repeat=n))
        srt = sort_sub(q)
        sorted_cells = [c for c in cells if subst(c, srt, q, q) == c]
        # maps Delta^q -> cube^n = cells factoring through the sort
        # retract = image of (- . sort) = same set (idempotent) ✓
        image = set(subst(c, srt, q, q) for c in cells)
        print(f"cube^{n}, q={q}: cells {len(cells)}, "
              f"sorted(fix) {len(sorted_cells)}, image(sort) {len(image)}, "
              f"fix == image: {set(sorted_cells) == image}")
        # closure under simplicial operators: sample all ordinal maps
        def ordinal_maps(m, nn):
            out = []
            for vals in itertools.product(range(nn + 1), repeat=m + 1):
                if all(vals[i] <= vals[i+1] for i in range(m)):
                    out.append(vals)
            return out
        def Tmap(f, m, nn):
            idx = []
            for i in range(1, nn + 1):
                ks = [k for k in range(m + 1) if f[k] >= i]
                idx.append(min(ks) if ks else m + 1)
            return tuple(order_stat(k, None, m) for k in idx)
        ok = True
        for m in (1, 2):
            for f in ordinal_maps(m, q):
                tf = Tmap(f, m, q)   # tf: q-tuple over D(m) = map [m]->[q]
                for c in sorted_cells:
                    inst = subst(c, tf, q, m)
                    if subst(inst, sort_sub(m), m, m) != inst:
                        ok = False
        print(f"  simplicial instances of sorted cells are sorted: {ok}")

# (iii) cubical circle: cells at level q = pairs-of-... S^1 = cube^1/(v0~v1)
# cells of S^1 at level q = D(q) with the two constants identified.
# sorted cells: p . sort = p with sort acting by o-substitution on 1 var:
# level-q cells of cube^1 = D(q), instance along sort = p o sort.
for q in (1, 2, 3):
    cells = D[q]
    srt = sort_sub(q)
    fix = [p for p in cells if compose1(p, srt, q, q) == p]
    # S^1: identify the two constants (0 and full)
    full = (1 << (1 << q)) - 1
    fixS1 = set(fix) - {0, full} | {0}  # merged constant repr as 0
    print(f"S^1-ish, q={q}: |D(q)| = {len(cells)}, sorted = {len(fix)}, "
          f"sorted classes in S^1 = {len(fixS1)}")
