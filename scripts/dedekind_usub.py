"""O28 stage 4a: (U-sub) -- chain-anchored subobjects of the cube
are contractible.

Theorem candidate: every subobject S of cube^n with S containing
Ch_n is type-contractible; more generally every W with
Ch_amb(A) <= W <= A for an atom A.  Proof: well-founded MV
induction with base (B1) (ambient chain parts strictly
contractible via the constant-free cone) and atoms strictly
contractible.  Machine sanity: T-Betti of random chain-anchored
subobjects of cube^2 and cube^3 (and random Ch_amb(A)-anchored
subobjects of atoms) = (1,0,0).
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

def betti(S):
    lv = {k: sorted(S[k]) for k in range(K + 1)}
    ind = {k: {c: i for i, c in enumerate(lv[k])} for k in lv}
    r = {}
    for q in range(1, K + 1):
        cols = []
        for cell in lv[q]:
            v = 0
            for i in range(q + 1):
                fc = rest(cell, wall_coface(i, q), q, q - 1)
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

random.seed(21)
bad = 0; total = 0
for n in (2, 3):
    _, Dn = F(n)
    Ch = chncells(n)
    cells_top = list(itertools.product(Dn, repeat=n))
    for trial in range(15):
        gens = random.sample(cells_top, random.choice((1, 2, 3)))
        S = union(Ch, *(atom(z, n, n) for z in gens))
        b = betti(S); total += 1
        if b != [1, 0, 0]:
            bad += 1
            print(f"(U-sub) FAIL n={n} trial {trial}: {b}", flush=True)
print(f"(U-sub) chain-anchored subobjects: {total} tested, "
      f"{bad} failures", flush=True)

# atom-relative version: W = Ch_amb(A) u (random subatoms of A)
u3 = tuple(p[0] for p in F(3)[0]); v3 = tuple(p[1] for p in F(3)[0])
w3 = tuple(p[2] for p in F(3)[0])
def mt3(*xs):
    o = xs[0]
    for x in xs[1:]: o = tuple(a & b for a, b in zip(o, x))
    return o
def jn3(*xs):
    o = xs[0]
    for x in xs[1:]: o = tuple(a | b for a, b in zip(o, x))
    return o
T5 = (mt3(u3,v3,w3), mt3(u3,v3), mt3(u3, jn3(v3,w3)))
A = atom(T5, 3, 3)
Chamb = {k: {c for c in A[k]
             if all(comparable(a, b)
                    for a, b in itertools.combinations(c, 2))}
         for k in range(K + 1)}
bad2 = 0
cells2 = sorted(A[2]); random.seed(5)
for trial in range(12):
    gens = random.sample(cells2, random.choice((1, 2)))
    W = union(Chamb, *(atom(z, 2, 3) for z in gens))
    b = betti(W)
    if b != [1, 0, 0]:
        bad2 += 1
        print(f"(U-atom/T5) FAIL trial {trial}: {b}", flush=True)
print(f"(U-atom) over the five-chain atom: 12 tested, "
      f"{bad2} failures", flush=True)
