"""Variant: close D under d -> s only for s in the finite set S* of 'modal subformula values' (j1 g, j2 g, J g, top),
and define the nucleus on D by the fixed set F_i = meet-closure of {d -> s : d in D, s in S_i} (S_i = j_i-values ∪ {top}).
Check: nucleus property, and that c_i(g) = j_i(g) for g in G, and join agreement."""
import itertools as it, random, sys
from nuclei_join_axiom import HA, nuclei, join_nucleus
from nuclei_filtration import sublattice, is_nucleus_on

def close_imp(H, D, S):
    D = set(D); changed = True
    while changed:
        changed = False
        for d in list(D):
            for s in S:
                e = H.imp(d, s)
                if e not in D: D.add(e); changed = True
        D2 = sublattice(H, D)
        if D2 != D: D = D2; changed = True
    return D

def nucleus_from(H, D, S_i):
    F = {H.top} | {H.imp(d, s) for d in D for s in S_i}
    # meet closure
    changed = True
    while changed:
        changed = False
        for a in list(F):
            for b in list(F):
                m = H.meet(a, b)
                if m not in F: F.add(m); changed = True
    assert F <= D
    c = {}
    for d in D:
        ups = [s for s in F if H.le(d, s)]
        m = min(ups, key=lambda s: len(H.el[s])); assert all(H.le(m, s) for s in ups); c[d] = m
    return c, F

if __name__ == "__main__":
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 25
    ok = fail = agree = disagree = joinok = joinfail = 0; sizes = []
    for t in range(trials):
        n = random.choice([3, 4, 4, 5])
        le = [[i == j for j in range(n)] for i in range(n)]
        for _ in range(random.randint(0, n)):
            i, j = random.sample(range(n), 2); le[i][j] = True
        for k in range(n):
            for i in range(n):
                for j in range(n):
                    if le[i][k] and le[k][j]: le[i][j] = True
        if any(le[i][j] and le[j][i] and i != j for i in range(n) for j in range(n)): continue
        H = HA(n, le)
        if H.n > 14: continue
        N = nuclei(H)
        if len(N) > 40: N = random.sample(N, 40)
        for j1, j2 in it.product(N, repeat=2):
            J = join_nucleus(H, j1, j2)
            fix1 = {a for a in range(H.n) if j1[a] == a}; fix2 = {a for a in range(H.n) if j2[a] == a}
            for _ in range(3):
                G = set(random.sample(range(H.n), random.randint(1, min(4, H.n))))
                S1 = {j1[g] for g in G} | {H.top}; S2 = {j2[g] for g in G} | {H.top}; SJ = {J[g] for g in G}
                D = close_imp(H, sublattice(H, G | S1 | S2 | SJ), S1 | S2 | SJ)
                sizes.append(len(D))
                c1, F1 = nucleus_from(H, D, S1); c2, F2 = nucleus_from(H, D, S2)
                if is_nucleus_on(H, D, c1) and is_nucleus_on(H, D, c2): ok += 1
                else: fail += 1
                if all(c1[g] == j1[g] and c2[g] == j2[g] for g in G): agree += 1
                else: disagree += 1
                fixD = [s for s in D if c1[s] == s and c2[s] == s]
                good = True
                for g in G:
                    ups = [s for s in fixD if H.le(g, s)]
                    m = min(ups, key=lambda s: len(H.el[s]))
                    if m != J[g]: good = False
                if good: joinok += 1
                else: joinfail += 1
    print("nucleus ok/fail:", ok, fail, "| agreement on G ok/fail:", agree, disagree, "| join agreement ok/fail:", joinok, joinfail, "| max |D|:", max(sizes))
