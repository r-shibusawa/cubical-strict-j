"""Direct search for a finite monoid on which W_D v W_E != W_{J_D v J_E}: by the reduction
lemma this happens iff the alternating tensor tower T_k = D (x) E (x) D (x) ... does NOT
stabilise (multiplication maps T_k -> T_{k-1} eventually bijective).  We scan contracted
monoids of random posets and free categories (the regime of non-commuting idempotent
ideals) and report any pair (D, E) whose tower is not stable by k = kmax."""
import random, sys, time
from threefold_transformation import two_sided_ideals, product
from threefold_contracted import poset_category, poset_from_edges, free_category, random_dag
from tensor_tower import tower

def scan(T, kmax=8, log=print):
    n = len(T); M = frozenset(range(n))
    allI = two_sided_ideals(T)
    if allI is None: return 0, 0
    ideals = [I for I in allI if I and product(T, I, I) == I and I != M]
    pairs = 0; unstable = 0
    for i, D in enumerate(ideals):
        for E in ideals[i + 1:]:
            if D <= E or E <= D: continue
            if len(D) * len(E) > 900: continue
            sizes, bij = tower(T, sorted(D), sorted(E), kmax=kmax)
            pairs += 1
            if not (bij[-2] and bij[-1]):
                unstable += 1; log(f"  UNSTABLE |M|={n} |D|={len(D)} |E|={len(E)} sizes={sizes} bij={bij}")
    return pairs, unstable

if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    random.seed(seed); seen = set(); tp = tu = 0; t0 = time.time()
    for trial in range(trials):
        nv = random.choice([3, 4, 4, 5, 5, 6]); ne = random.randint(1, min(8, nv * (nv - 1) // 2)); edges = random_dag(nv, ne)
        if random.random() < 0.6:
            T = poset_category(poset_from_edges(nv, edges), list(range(nv))); label = f"poset nv={nv} {edges}"
        else:
            T = free_category(list(range(nv)), [(s, t, f"a{i}") for i, (s, t) in enumerate(edges)]); label = f"free nv={nv} {edges}"
            if T is None: continue
        if len(T) > 30: continue
        key = tuple(map(tuple, T))
        if key in seen: continue
        seen.add(key)
        p, u = scan(T); tp += p; tu += u
        print(f"trial {trial} {label}: |M|={len(T)} pairs={p} unstable={u}", flush=True)
    print(f"DONE seed={seed} monoids={len(seen)} pairs={tp} unstable={tu} time={time.time()-t0:.0f}s")
