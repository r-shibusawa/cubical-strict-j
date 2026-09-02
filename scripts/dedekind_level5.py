"""O28 stage 7g: do new atoms of cube^3 keep appearing at
generator level 5?  (Truth-table composition; random monotone
functions on 2^5 sampled as up-closures of random antichains.)

Fingerprint = exact cell sets at levels 1 and 2.  Compare the
cumulative fingerprint sets from levels <= 4 (exhaustive at <= 2,
sampled 4000 at 3 and 4) against 2000 sampled level-5 generators.
"""
import itertools, random, time
random.seed(41)

def pts(m): return list(itertools.product((0,1), repeat=m))
PT = {m: pts(m) for m in range(0, 6)}
IDX = {m: {p: i for i, p in enumerate(PT[m])} for m in PT}
def comp(phi, a, ks, kt):
    return tuple(phi[IDX[ks][tuple(ai[j] for ai in a)]]
                 for j in range(len(PT[kt])))
def rest(cell, u, j, k):
    return tuple(comp(c, u, j, k) for c in cell)
def D(k):
    out = []
    P = PT[k]
    for bits in itertools.product((0,1), repeat=len(P)):
        ok = True
        for i, p in enumerate(P):
            if not ok: break
            for jj, q in enumerate(P):
                if all(a <= b for a, b in zip(p, q)) and \
                   bits[i] > bits[jj]: ok = False; break
        if ok: out.append(bits)
    return out
D1, D2 = D(1), D(2)
def cells(z, m, k, Dk):
    return frozenset(rest(z, u, m, k)
                     for u in itertools.product(Dk, repeat=m))
def fp(z, m):
    return (cells(z, m, 1, D1), cells(z, m, 2, D2))

def rand_mono(m, na=3):
    """up-closure of na random antichain points"""
    P = PT[m]
    seeds = random.sample(P, na)
    return tuple(1 if any(all(a <= b for a, b in zip(s, p))
                          for s in seeds) else 0 for p in P)

t0 = time.time()
seen = set()
D3 = D(3)
for m, gens in ((1, None), (2, None), (3, 3500), (4, 3500)):
    if m <= 2:
        Dm = D1 if m == 1 else D2
        G = list(itertools.product(Dm, repeat=3))
    else:
        G = [tuple(rand_mono(m) for _ in range(3))
             for _ in range(gens)]
    new = 0
    for z in G:
        f = fp(z, m)
        if f not in seen: seen.add(f); new += 1
    print(f"level {m}: +{new} (cum {len(seen)}) "
          f"{time.time()-t0:.0f}s", flush=True)
new5 = 0
for _ in range(2000):
    z = tuple(rand_mono(5) for _ in range(3))
    f = fp(z, 5)
    if f not in seen: seen.add(f); new5 += 1
print(f"level 5 (2000 sampled): +{new5} new fingerprints "
      f"(cum {len(seen)}) {time.time()-t0:.0f}s", flush=True)
