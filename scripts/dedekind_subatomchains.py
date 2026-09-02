"""O28 stage 7a: well-foundedness of the subatom order -- probe.

Question (the audit's open point): can atoms of a cube form an
infinite strictly descending chain?  Images in 2^n stabilize, so
the danger is infinitely many atoms over a FIXED image poset P.
Probe in ambient cube^2 and cube^3:
 (a) enumerate atoms generated at levels m <= 4 (sampled at the
     costly sizes), fingerprint by cell sets at levels <= 2,
     count distinct fingerprints per generator level -- do new
     atoms keep appearing?
 (b) build the containment order among sampled atoms (z' in <z>
     tested exactly at z''s level) and measure the longest
     strictly descending chains;
 (c) hunt for descending pairs whose LEVEL<=2 cell counts do NOT
     drop (the measure-failure pattern of referee_measure2).
"""
import sys, itertools, random, time
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose

def rest(cell, u, j, k):
    return tuple(compose(c, u, j, k) for c in cell)

def atom_cells(z, m, n, k):
    _, Dk = F(k)
    return frozenset(rest(z, u, m, k)
                     for u in itertools.product(Dk, repeat=m))

def fingerprint(z, m, n):
    return (atom_cells(z, m, n, 1), atom_cells(z, m, n, 2))

random.seed(17)
t0 = time.time()
for n in (2, 3):
    print(f"=== ambient cube^{n} ===", flush=True)
    seen = {}          # fingerprint -> (level, generator)
    per_level_new = {}
    reps = []
    for m in range(1, 5):
        _, Dm = F(m)
        gens = list(itertools.product(Dm, repeat=n))
        if len(gens) > 4000:
            gens = random.sample(gens, 4000)
        new = 0
        for z in gens:
            fp = fingerprint(z, m, n)
            if fp not in seen:
                seen[fp] = (m, z); new += 1
                reps.append((m, z, fp))
        per_level_new[m] = new
        print(f"  level {m}: {len(gens)} gens, {new} new "
              f"fingerprints (cum {len(seen)}), "
              f"{time.time()-t0:.0f}s", flush=True)
    # (b) containment among representatives (up to fingerprint):
    # z' (level m') contained in <z> iff z' in atom_cells(z,m,n,m')
    # -- only feasible for m' <= 3; restrict to reps with m' <= 3
    small = [(m, z, fp) for (m, z, fp) in reps if m <= 3]
    if len(small) > 350: small = random.sample(small, 350)
    idx = range(len(small))
    contains = {}
    for i in idx:
        mi, zi, fpi = small[i]
        cache = {}
        for j in idx:
            if i == j: continue
            mj, zj, fpj = small[j]
            if mj not in cache:
                cache[mj] = atom_cells(zi, mi, n, mj)
            if zj in cache[mj]:
                contains.setdefault(i, set()).add(j)
    # strict containment i > j (j in atom i, and not conversely
    # -- approximate: fingerprints differ or i not in atom j)
    strict = {}
    for i in idx:
        for j in contains.get(i, ()):
            back = i in contains.get(j, ())
            if not back:
                strict.setdefault(i, set()).add(j)
    # longest descending chain by DP over the DAG
    import functools
    sys.setrecursionlimit(10000)
    @functools.lru_cache(maxsize=None)
    def depth(i):
        return 1 + max([depth(j) for j in strict.get(i, ())] or [0])
    best = max((depth(i) for i in idx), default=0)
    print(f"  containment probe on {len(small)} atoms: longest "
          f"strict chain = {best}", flush=True)
    # (c) strict pairs with equal level<=2 cell counts
    flat = 0
    for i in idx:
        for j in strict.get(i, ()):
            ci = tuple(len(s) for s in small[i][2])
            cj = tuple(len(s) for s in small[j][2])
            if ci == cj: flat += 1
    print(f"  strict pairs with EQUAL level<=2 counts: {flat}",
          flush=True)
