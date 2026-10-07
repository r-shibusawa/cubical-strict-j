"""Tower-stabilisation search, second family: random transformation submonoids of T_3..T_5
and direct products of monoids of order <= 4 (non-acyclic regime: groups of units,
regular D-classes).  Reports any incomparable pair (D, E) of proper idempotent ideals whose
alternating tensor tower is not stable by k = 8, and the first k from which mu_k is surjective."""
import random, sys, time, itertools as it
from threefold_transformation import closure, two_sided_ideals, product
from monoids_small import monoids
import tensor_tower

src = open('tensor_tower.py').read().split("if __name__")[0]
src = src.replace("sizes=[len(A_elems)]; bij=[]", "sizes=[len(A_elems)]; bij=[]; surj=[]")
src = src.replace("sizes.append(len(elems)); bij.append(len(set(mu.values()))==len(elems)==len(prev_elems))",
                  "sizes.append(len(elems)); bij.append(len(set(mu.values()))==len(elems)==len(prev_elems)); surj.append(len(set(mu.values()))==len(prev_elems))")
src = src.replace("    return sizes,bij", "    return sizes,bij,surj")
ns = {}; exec(compile(src, 'tt', 'exec'), ns); tower = ns['tower']

def direct_product(T1, T2):
    n1, n2 = len(T1), len(T2)
    idx = lambda a, b: a * n2 + b
    return [[idx(T1[a1][b1], T2[a2][b2]) for b1 in range(n1) for b2 in range(n2)] for a1 in range(n1) for a2 in range(n2)]

def scan(T, kmax=8, log=print):
    n = len(T); M = frozenset(range(n))
    allI = two_sided_ideals(T)
    if allI is None: return 0, 0, {}
    ideals = [I for I in allI if I and product(T, I, I) == I and I != M]
    pairs = unstable = 0; hist = {}
    for i, D in enumerate(ideals):
        for E in ideals[i + 1:]:
            if D <= E or E <= D or len(D) * len(E) > 900: continue
            sizes, bij, surj = tower(T, sorted(D), sorted(E), kmax=kmax)
            pairs += 1
            first = next((j + 2 for j in range(len(surj)) if all(surj[j:])), None)
            hist[first] = hist.get(first, 0) + 1
            if not (bij[-2] and bij[-1]) or any(sizes[j + 1] > sizes[j] for j in range(1, len(sizes) - 1)):
                unstable += 1; log(f"  UNSTABLE/INCREASE |M|={n} |D|={len(D)} |E|={len(E)} sizes={sizes} surj={surj}")
    return pairs, unstable, hist

if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    random.seed(seed); seen = set(); tp = tu = 0; H = {}; t0 = time.time()
    small = [T for n in range(2, 5) for T in monoids(n)]
    for trial in range(trials):
        if random.random() < 0.6:
            k = random.choice([3, 4, 4, 5]); gens = [tuple(random.randrange(k) for _ in range(k)) for _ in range(random.choice([2, 2, 3]))]
            _, T = closure(gens, k); label = f"transf k={k}"
        else:
            T = direct_product(random.choice(small), random.choice(small)); label = "product"
        if len(T) > 36 or len(T) < 4: continue
        key = tuple(map(tuple, T))
        if key in seen: continue
        seen.add(key)
        p, u, h = scan(T); tp += p; tu += u
        for a, b in h.items(): H[a] = H.get(a, 0) + b
        print(f"trial {trial} {label}: |M|={len(T)} pairs={p} unstable={u} first-surjective={h}", flush=True)
    print(f"DONE seed={seed} monoids={len(seen)} pairs={tp} unstable={tu} first-surjective-histogram={H} time={time.time()-t0:.0f}s")
