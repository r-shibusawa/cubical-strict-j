"""O28 stage 4b: (U-sub-H) -- chain-anchored subobjects of
PERMUTATION quotients of cubes are contractible.

The extension route handles cell stabilizers H_x (always
subgroups of the symmetric group on the reversal-free Dedekind
site) by lifting in the quotient cube^n/H.  Needed shape input:
for H <= Sigma_n and an H-stable chain-anchored S <= cube^n,
the image S/H into cube^n/H is a type-trivial cofibration --
via the H-equivariant wedge cone (symmetric formula) and the
orbit-MV induction.  Machine sanity: T-Betti of chain-anchored
subobjects of cube^2/swap and cube^3/(transpositions, Sigma_3):
expect (1,0,0).  Consistency check of Dedekind-specificity:
on reversal sites the cone is NOT equivariant -- here H is
always permutations only.
"""
import sys, itertools, random
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose
from dedekind_triangulate import coface as wall_coface, rank2

def rest(cell, u, j, k):
    return tuple(compose(c, u, j, k) for c in cell)
def leq_t(a, b): return all(x <= y for x, y in zip(a, b))
def comparable(a, b): return leq_t(a, b) or leq_t(b, a)
K = 3

def orbit_map(n, H):
    """H = list of permutations of range(n); returns cell -> rep"""
    def rep(c):
        return min(tuple(c[p[i]] for i in range(n)) for p in H)
    return rep

def betti_orbits(S, n, H):
    rep = orbit_map(n, H)
    lv = {k: sorted({rep(c) for c in S[k]}) for k in range(K + 1)}
    ind = {k: {c: i for i, c in enumerate(lv[k])} for k in lv}
    r = {}
    for q in range(1, K + 1):
        cols = []
        for cell in lv[q]:
            v = 0
            for i in range(q + 1):
                fc = rep(rest(cell, wall_coface(i, q), q, q - 1))
                if fc not in ind[q - 1]: return None
                v ^= 1 << ind[q - 1][fc]
            cols.append(v)
        r[q] = rank2(cols)
    b = [len(lv[0]) - r[1]]
    for q in range(1, K):
        b.append(len(lv[q]) - r[q] - r[q + 1])
    return b

def atom(z, j, n):
    S = {}
    for k in range(K + 1):
        _, Dk = F(k)
        S[k] = {rest(z, u, j, k)
                for u in itertools.product(Dk, repeat=j)}
    return S
def union(*Ss):
    return {k: set().union(*(S[k] for S in Ss)) for k in range(K+1)}
def chncells(n):
    S = {}
    for k in range(K + 1):
        _, Dk = F(k)
        S[k] = {c for c in itertools.product(Dk, repeat=n)
                if all(comparable(a, b)
                       for a, b in itertools.combinations(c, 2))}
    return S
def close_H(S, n, H):
    out = {}
    for k in range(K + 1):
        cells = set()
        for c in S[k]:
            for p in H:
                cells.add(tuple(c[p[i]] for i in range(n)))
        out[k] = cells
    return out

random.seed(31)
bad = 0; total = 0
groups = {
    2: [("swap", [ (0,1), (1,0) ])],
    3: [("transp01", [(0,1,2), (1,0,2)]),
        ("cyclic3", [(0,1,2), (1,2,0), (2,0,1)]),
        ("Sigma3", [p for p in itertools.permutations(range(3))])],
}
for n in (2, 3):
    _, Dn = F(n)
    Ch = chncells(n)
    cells_top = list(itertools.product(Dn, repeat=n))
    for gname, H in groups[n]:
        # whole quotient cube and chain part
        full = {k: set(itertools.product(F(k)[1], repeat=n))
                for k in range(K + 1)}
        b0 = betti_orbits(full, n, H)
        b1 = betti_orbits(Ch, n, H)
        st = f"cube^{n}/{gname}: full {b0}, chain-part {b1}"
        okf = (b0 == [1,0,0] and b1 == [1,0,0])
        total += 2; bad += (b0 != [1,0,0]) + (b1 != [1,0,0])
        # random H-stable chain-anchored subobjects
        for trial in range(8):
            gens = random.sample(cells_top, random.choice((1, 2)))
            S = close_H(union(Ch, *(atom(z, n, n) for z in gens)),
                        n, H)
            b = betti_orbits(S, n, H); total += 1
            if b != [1, 0, 0]:
                bad += 1
                print(f"FAIL {n}/{gname} trial {trial}: {b}",
                      flush=True)
        print(st, flush=True)
print(f"(U-sub-H): {total} tested, {bad} failures", flush=True)
