"""Statement S (right stabilisation): for idempotent two-sided ideals X, Y of a finite monoid
and any NON-UNIT p, the class [x, y p] in X (x) Y depends only on (x y, p).
S implies three-fold multiplicativity for every proper idempotent ideal Z:
[x,y,c] = [x, y c1, c2] for c = c1 c2 in Z, and [x, y c1] depends only on (xy, c1).
Verified here on random transformation submonoids and contracted monoids of acyclic categories."""
import itertools as it, random, sys, time
from tensor_multi import multitensor
from threefold_transformation import closure, two_sided_ideals, product
from threefold_contracted import poset_category, poset_from_edges, free_category, random_dag

def test_S(T, log=print):
    n = len(T); M = frozenset(range(n))
    allI = two_sided_ideals(T)
    if allI is None: return 0, 0
    ideals = [I for I in allI if I and product(T, I, I) == I and I != M]
    units = {g for g in range(n) if any(T[g][h] == 0 for h in range(n))}
    N = [p for p in range(n) if p not in units]
    tested = fails = 0
    for X in ideals:
        for Y in ideals:
            if len(X) * len(Y) > 3000: continue
            uf = multitensor(T, [X, Y]); tuples = list(it.product(sorted(X), sorted(Y)))
            byprod = {}
            for t in tuples: byprod.setdefault(T[t[0]][t[1]], []).append(t)
            for prod, ts in byprod.items():
                if len({uf.find(t) for t in ts}) == 1: continue  # no defect
                for p in N:
                    tested += 1
                    if len({uf.find((x, T[y][p])) for (x, y) in ts}) > 1:
                        fails += 1; log(f"  S FAILS |M|={n} |X|={len(X)} |Y|={len(Y)} p={p} prod={prod}")
    return tested, fails

if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    random.seed(seed); seen = set(); tot = fl = 0; defects = 0; t0 = time.time()
    for trial in range(trials):
        if random.random() < 0.5:
            k = random.choice([3, 4, 4, 5]); gens = [tuple(random.randrange(k) for _ in range(k)) for _ in range(random.choice([2, 2, 3]))]
            _, T = closure(gens, k); label = f"transf k={k}"
        else:
            nv = random.choice([2, 3, 3, 4, 4, 5]); ne = random.randint(1, min(6, nv * (nv - 1) // 2)); edges = random_dag(nv, ne)
            if random.random() < 0.5: T = poset_category(poset_from_edges(nv, edges), list(range(nv))); label = f"poset {edges}"
            else:
                T = free_category(list(range(nv)), [(s, t, f"a{i}") for i, (s, t) in enumerate(edges)]); label = f"free {edges}"
                if T is None: continue
        if len(T) > 45 or len(T) < 3: continue
        key = tuple(map(tuple, T))
        if key in seen: continue
        seen.add(key)
        a, b = test_S(T); tot += a; fl += b
        if a: defects += 1
        print(f"trial {trial} {label}: |M|={len(T)} defect-fibre tests={a} fails={b}", flush=True)
    print(f"DONE seed={seed} monoids={len(seen)} monoids-with-defects={defects} tests={tot} failures={fl} time={time.time()-t0:.0f}s")
