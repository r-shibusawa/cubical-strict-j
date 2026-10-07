"""Three-fold multiplicativity (the three-fold multiplicativity conjecture) on CONTRACTED MONOIDS of small acyclic
categories: M(S) = {1} u Mor(S) u {0}, with composition where defined and 0 otherwise.
These are the 'one-way arrow with zero' monoids of the residual case (monoid5#88 is M(a<b)),
whose two-sided ideals are typically non-commuting (DE != ED) with non-idempotent
intersections -- the regime not covered by either proof of paper 30.

Categories S: (i) all posets on <= 5 points (via random DAGs, transitive closure, dedup by
Cayley table), (ii) free categories on random acyclic quivers with <= 5 vertices and <= 6
arrows (finitely many paths), (iii) random quotients are not attempted.
For each idempotent proper ideal triple (X, Y, Z) we test X(x)Y(x)Z -> XY(x)Z bijective.
"""
import itertools as it, random, sys, time
from tensor_multi import mult_map_bijective
from threefold_transformation import two_sided_ideals, product

def contracted(objects, morphisms, compose):
    """morphisms: list of (src, tgt, name); compose(f, g) -> name of g o f or None.
    Returns Cayley table T with elements [1] + morphisms + [0], product T[a][b] = a * b := b o a
    (a first, then b) -- for a monoid the side convention is immaterial for the test."""
    names = [m[2] for m in morphisms]
    idx = {n: i + 1 for i, n in enumerate(names)}
    n = len(names) + 2; ZERO = n - 1
    info = {m[2]: m for m in morphisms}
    T = [[0] * n for _ in range(n)]
    for a in range(n):
        for b in range(n):
            if a == 0: T[a][b] = b
            elif b == 0: T[a][b] = a
            elif a == ZERO or b == ZERO: T[a][b] = ZERO
            else:
                f, g = names[a - 1], names[b - 1]
                if info[f][1] != info[g][0]: T[a][b] = ZERO
                else:
                    h = compose(f, g)
                    T[a][b] = idx[h] if h is not None else ZERO
    return T

def poset_category(le, pts):
    """le: set of pairs (a,b) with a<=b (reflexive, transitive). morphisms = pairs."""
    morphisms = [(a, b, (a, b)) for (a, b) in sorted(le)]
    def compose(f, g): return (f[0], g[1])
    return contracted(pts, morphisms, compose)

def free_category(verts, arrows):
    """arrows: list of (s, t, label); acyclic. morphisms = identities + nonempty paths."""
    paths = {}
    morphisms = []
    for v in verts: morphisms.append((v, v, ('id', v)))
    frontier = [((a[0], a[1]), (a[2],)) for a in arrows]
    allp = set()
    while frontier:
        nxt = []
        for (s, t), p in frontier:
            if p in allp: continue
            allp.add(p); morphisms.append((s, t, p))
            for a in arrows:
                if a[0] == t: nxt.append(((s, a[1]), p + (a[2],)))
        frontier = nxt
        if len(allp) > 60: return None
    def compose(f, g):
        if f[0] == 'id': return g
        if g[0] == 'id': return f
        return f + g
    return contracted(verts, morphisms, compose)

def random_dag(nv, ne):
    order = list(range(nv)); random.shuffle(order)
    edges = set()
    tries = 0
    while len(edges) < ne and tries < 50:
        tries += 1
        i, j = sorted(random.sample(range(nv), 2))
        edges.add((order[i], order[j]))
    return sorted(edges)

def poset_from_edges(nv, edges):
    le = {(v, v) for v in range(nv)} | set(edges)
    changed = True
    while changed:
        changed = False
        for (a, b) in list(le):
            for (c, d) in list(le):
                if b == c and (a, d) not in le: le.add((a, d)); changed = True
    return le

def run_test(T, label, log):
    from threefold_transformation import test_monoid
    tested, fails, nid = test_monoid(T, maxsize=40000, log=log)
    log(f"{label}: |M|={len(T)} idempotent proper ideals={nid} triples={tested} fails={fails}")
    return tested, fails

if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 150
    random.seed(seed)
    seen = set(); tot = 0; fl = 0; t0 = time.time()
    for trial in range(trials):
        nv = random.choice([2, 3, 3, 4, 4, 5]); ne = random.randint(1, min(6, nv * (nv - 1) // 2))
        edges = random_dag(nv, ne)
        if random.random() < 0.5:
            T = poset_category(poset_from_edges(nv, edges), list(range(nv))); label = f"poset nv={nv} edges={edges}"
        else:
            T = free_category(list(range(nv)), [(s, t, f"a{i}") for i, (s, t) in enumerate(edges)]); label = f"free nv={nv} edges={edges}"
            if T is None: continue
        key = tuple(map(tuple, T))
        if key in seen: continue
        seen.add(key)
        if len(T) > 40: continue
        a, b = run_test(T, label, print); tot += a; fl += b
    print(f"DONE seed={seed} monoids={len(seen)} triples={tot} failures={fl} time={time.time()-t0:.0f}s", flush=True)
