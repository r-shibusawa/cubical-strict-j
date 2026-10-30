"""Closure operators (abstract domains) on finite lattices and the sameness lattice of the poset.
For a finite lattice L (given by its order), an upper closure operator rho <-> Moore family F (meet-closed, contains top).
W_rho = {(x,y): x<=y, rho x = rho y}.  For a pair (rho, rho'):
  C  = compositional closure of W_rho u W_rho' (alternating chains),
  J  = two-out-of-three saturation of C (the join in Same(L)),
  Wj = W_{rho v rho'} where rho v rho' has fixpoints Fix(rho) n Fix(rho') (least common abstraction).
Reports: pairs with C != J (cancellation needed), pairs with J != Wj, and whether rho, rho' preserve binary meets."""
import itertools as it, sys

def lattice_from_cover(n, cover):
    le = [[i == j for j in range(n)] for i in range(n)]
    for a, b in cover: le[a][b] = True
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if le[i][k] and le[k][j]: le[i][j] = True
    def meet(a, b):
        lb = [z for z in range(n) if le[z][a] and le[z][b]]
        m = [z for z in lb if all(le[w][z] for w in lb)]
        assert len(m) == 1, "not a lattice"
        return m[0]
    top = [z for z in range(n) if all(le[w][z] for w in range(n))][0]
    return le, meet, top

def moore_families(n, le, meet, top):
    out = []
    for r in range(1, n + 1):
        for S in it.combinations(range(n), r):
            S = set(S)
            if top not in S: continue
            if all(meet(a, b) in S for a in S for b in S): out.append(frozenset(S))
    return out

def closure(F, n, le, meet):
    # rho(x) = meet of elements of F above x
    rho = []
    for x in range(n):
        above = [f for f in F if le[x][f]]
        m = above[0]
        for f in above[1:]: m = meet(m, f)
        rho.append(m)
    return tuple(rho)

def preserves_meets(rho, n, meet):
    return all(rho[meet(a, b)] == meet(rho[a], rho[b]) for a in range(n) for b in range(n))

def W(rho, n, le):
    return frozenset((x, y) for x in range(n) for y in range(n) if le[x][y] and rho[x] == rho[y])

def comp_closure(S, n, le):
    S = set(S) | {(x, x) for x in range(n)}
    changed = True
    while changed:
        changed = False
        for (a, b) in list(S):
            for (c, d) in list(S):
                if b == c and (a, d) not in S: S.add((a, d)); changed = True
    return frozenset(S)

def saturate(S, n, le):
    S = set(comp_closure(S, n, le))
    changed = True
    while changed:
        changed = False
        for x in range(n):
            for y in range(n):
                if not le[x][y] or (x, y) in S: continue
                # cancellation: (x,z),(y,z) in S with y<=z  or  (w,x),(w,y) in S with w<=x
                if any((x, z) in S and (y, z) in S for z in range(n) if le[y][z]) or \
                   any((w, x) in S and (w, y) in S for w in range(n) if le[w][x]):
                    S.add((x, y)); changed = True
        if changed: S = set(comp_closure(S, n, le))
    return frozenset(S)

def run(name, n, cover):
    le, meet, top = lattice_from_cover(n, cover)
    fams = moore_families(n, le, meet, top)
    rhos = {F: closure(F, n, le, meet) for F in fams}
    stats = dict(pairs=0, cancel=0, cancel_nuclei=0, jneq=0)
    examples = []
    for F in fams:
        for G in fams:
            if F == G: continue
            r, s = rhos[F], rhos[G]
            Wr, Ws = W(r, n, le), W(s, n, le)
            C = comp_closure(Wr | Ws, n, le); J = saturate(C, n, le)
            Fj = F & G; rj = closure(Fj, n, le, meet); Wj = W(rj, n, le)
            stats['pairs'] += 1
            nuc = preserves_meets(r, n, meet) and preserves_meets(s, n, meet)
            if C != J:
                stats['cancel'] += 1
                if nuc: stats['cancel_nuclei'] += 1
                if len(examples) < 2: examples.append((sorted(F), sorted(G), sorted(J - C)))
            if J != Wj: stats['jneq'] += 1
    print(f"{name}: {n} elements, {len(fams)} closure operators, {stats}")
    for e in examples: print("   cancellation needed: Fix rho =", e[0], " Fix rho' =", e[1], " J \\ C =", e[2])

# lattices: chains, 2x2, 2x3, 2^3, M3, N5, 2x2 with extra, pentagon+, etc.  Elements 0..n-1, cover relations.
run("chain 4", 4, [(0,1),(1,2),(2,3)])
run("2x2", 4, [(0,1),(0,2),(1,3),(2,3)])
run("M3", 5, [(0,1),(0,2),(0,3),(1,4),(2,4),(3,4)])
run("N5", 5, [(0,1),(1,3),(0,2),(2,3)][:0] + [(0,1),(0,2),(1,3),(3,4),(2,4)])
run("2x3", 6, [(0,1),(1,2),(0,3),(3,4),(4,5),(1,4),(2,5)])
run("2^3", 8, [(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(4,5),(4,6),(3,7),(5,7),(6,7)])
run("hexagon", 6, [(0,1),(1,2),(2,5),(0,3),(3,4),(4,5)])
run("2x2+top", 5, [(0,1),(0,2),(1,3),(2,3),(3,4)])
run("bottom+2x2", 5, [(0,1),(1,2),(1,3),(2,4),(3,4)])
