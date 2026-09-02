"""O28 stage 7c: are atoms of cube^n determined by their cells at
levels <= 2?

If yes, nu(A) := (|A(1)|, |A(2)|) strictly drops on every proper
containment (containment makes counts weakly drop levelwise, and
equality at <=2 would force equality) -- the corrected
well-founded measure for the extension theorem, replacing the
refuted |L|.

Test: group sampled generators (levels 3 and 4, cube^3; level 3,
cube^2 exhaustive) by their (level-1, level-2) cell SETS; within
each group, compare level-3 cell sets.  Report any group whose
members have distinct level-3 sets.
"""
import sys, itertools, random, time
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose
from collections import defaultdict

def rest(cell, u, j, k):
    return tuple(compose(c, u, j, k) for c in cell)
def cells(z, m, n, k, cap=None):
    _, Dk = F(k)
    subs = itertools.product(Dk, repeat=m)
    out = set()
    for u in subs:
        out.add(rest(z, u, m, k))
    return frozenset(out)

random.seed(29)
t0 = time.time()
for n, levels, sizes in ((2, (3,), (4000,)), (3, (3,), (2500,)),
                          (3, (4,), (600,))):
    for m, sz in zip(levels, sizes):
        _, Dm = F(m)
        gens = list(itertools.product(Dm, repeat=n))
        if len(gens) > sz: gens = random.sample(gens, sz)
        groups = defaultdict(list)
        for z in gens:
            fp = (cells(z, m, n, 1), cells(z, m, n, 2))
            groups[fp].append(z)
        multi = {fp: zs for fp, zs in groups.items() if len(zs) > 1}
        # within groups: distinct level-3 sets?
        bad = 0; checked = 0
        for fp, zs in multi.items():
            if len(zs) > 6: zs = random.sample(zs, 6)
            l3 = set()
            for z in zs:
                if m <= 3:
                    l3.add(cells(z, m, n, 3))
                else:
                    # sampled level-3 set for level-4 generators
                    _, D3 = F(3)
                    s = frozenset(rest(z, tuple(random.choice(D3)
                        for _ in range(m)), m, 3)
                        for _ in range(3000))
                    l3.add(s)   # sampled: only equal-sample = hint
            checked += 1
            if len(l3) > 1: bad += 1
        tag = "exact" if m <= 3 else "SAMPLED level-3 (hint only)"
        print(f"cube^{n}, gens level {m} ({len(gens)}): "
              f"{len(groups)} fingerprint groups, {len(multi)} "
              f"multi-member; groups with DISTINCT level-3 sets: "
              f"{bad} [{tag}]  ({time.time()-t0:.0f}s)", flush=True)
