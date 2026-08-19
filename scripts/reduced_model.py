"""Reduced vertex model for el(cube^n/D) (O18, section 79).

E_F(D) can be built from ANY D-set U with U^K nonempty exactly for
K in F.  Taking U = { v : Stab_D(v) is MAXIMAL among vertex stabilisers }
still has this property (every K in F lies in a maximal member, which is
a vertex stabiliser), and |U| < 2^n whenever some vertex orbit has a
non-maximal stabiliser.  The Cech orbit complex of U therefore computes
the same H_*(el(cube^n/D)) with far fewer simplices, which is what makes
degree 4 reachable in the residual cases of the (NR') table.
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build
from nr_sharp import VC, homology, induced_rank

def reduced_vertices(H, ACT, n):
    NV = 1 << n
    stab = {v: frozenset(a for a in H if ACT[a][v] == v) for v in range(NV)}
    keep = []
    for v in range(NV):
        S = stab[v]
        if any(S < frozenset(a for a in H if ACT[a][MUL_v] == MUL_v)
               for MUL_v in range(NV)) is False:
            pass
    # maximal stabilisers up to conjugacy
    maxes = []
    for v in range(NV):
        S = stab[v]
        if any(S < stab[w] for w in range(NV)): continue
        maxes.append(v)
    return sorted(maxes)

if __name__ == "__main__":
    for n in (2, 3):
        ELEMS, idx, ID, NE, MUL, INV, ACT = build(n)
        def cl(g):
            S = {ID}; dq = deque([ID])
            while dq:
                x = dq.popleft()
                for a in g:
                    y = MUL[x][a]
                    if y not in S: S.add(y); dq.append(y)
            return frozenset(S)
        tests = []
        if n == 2:
            tests = [("K", [idx[((1, 0), (0, 0))], idx[((0, 1), (1, 1))]])]
        else:
            tests = [("H8", [idx[((1, 0, 2), (0, 0, 0))],
                             idx[((0, 1, 2), (0, 1, 1))]]),
                     ("H24", [idx[((0, 1, 2), (1, 0, 0))],
                              idx[((0, 1, 2), (0, 1, 0))],
                              idx[((0, 1, 2), (0, 0, 1))],
                              idx[((1, 2, 0), (0, 0, 0))]]),
                     ("B_3", [idx[((1, 0, 2), (0, 0, 0))],
                              idx[((1, 2, 0), (0, 0, 0))],
                              idx[((0, 1, 2), (1, 0, 0))]])]
        for name, gens in tests:
            D = sorted(cl(gens))
            U = reduced_vertices(D, ACT, n)
            full = VC(list(range(1 << n)), [ACT[a] for a in D], 4, NV=1 << n)
            red = VC(U, [ACT[a] for a in D], 4, NV=1 << n)
            print(f"{name}: |V|={1<<n} -> |U|={len(U)};  full "
                  f"{homology(full, 4)}  reduced {homology(red, 4)}")
