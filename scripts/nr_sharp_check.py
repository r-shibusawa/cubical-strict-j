"""(NR') for every reflection-generated mixed class of B_n, n <= 4:
a twisted end class factors through a single stratum quotient
l/N_l = cube^m/Q_l, so the separation needs only that id_W does not
factor through it (O18, section 79).

Reported per maximal-stratum orbit:
  * "acyclic": Q_l fixes a vertex of l  =>  el(l/N_l) is F_2-acyclic
    (Theorem W1), so a retraction would make el(W) acyclic, contradicting
    W1 for the mixed D -- no computation needed;
  * otherwise the induced map H_*(el l/N_l) -> H_*(el W) is computed and
    (NR') is certified when it is not surjective.
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build
from nr_sharp import VC, homology, induced_rank

for n in (2, 3, 4):
    ELEMS, idx, ID, NE, MUL, INV, ACT = build(n)
    def close(gens):
        S = {ID}; dq = deque([ID])
        while dq:
            x = dq.popleft()
            for g in gens:
                y = MUL[x][g]
                if y not in S: S.add(y); dq.append(y)
        return frozenset(S)
    REFL = []
    for a in range(NE):
        p, s = ELEMS[a]
        seen = [False]*n; ok = a != ID
        for i in range(n):
            if seen[i]: continue
            sg = s[i]; j = p[i]; seen[i] = True
            while j != i:
                seen[j] = True; sg ^= s[j]; j = p[j]
            if sg & 1: ok = False
        REFL.append(ok)
    subs = {frozenset([ID]): []}
    frontier = list(subs.items())
    while frontier:
        new = []
        for H, gens in frontier:
            for g in range(NE):
                if g in H: continue
                H2 = close(gens + [g])
                if H2 not in subs:
                    subs[H2] = gens + [g]; new.append((H2, gens + [g]))
        frontier = new
    classes = {}
    for H in subs:
        key = min(tuple(sorted(MUL[MUL[g][a]][INV[g]] for a in H))
                  for g in range(NE))
        classes.setdefault(key, H)
    tgt = []
    for H in classes.values():
        R = [a for a in H if REFL[a]]
        if not R: continue
        if any(all(ACT[a][v] == v for a in R) for v in range(1 << n)): continue
        if close(R) != H: continue
        tgt.append(sorted(H))
    print(f"n={n}: reflection-generated mixed classes {len(tgt)}", flush=True)
    allok = 0
    for H in sorted(tgt, key=len):
        NV = 1 << n
        loci = {}
        for a in H:
            if REFL[a]:
                L = frozenset(v for v in range(NV) if ACT[a][v] == v)
                loci[L] = 1
        maximal = [sorted(L) for L in loci if not any(L < L2 for L2 in loci)]
        A = VC(list(range(NV)), [ACT[a] for a in H], 4, NV=NV)
        HA = homology(A, 4)
        seen = set(); verdicts = []
        for Ls in maximal:
            key = min(tuple(sorted(ACT[g][v] for v in Ls)) for g in H)
            if key in seen: continue
            seen.add(key)
            Nl = [a for a in H if {ACT[a][v] for v in Ls} == set(Ls)]
            if any(all(ACT[a][w] == w for a in Nl) for w in Ls):
                verdicts.append("acyclic-kill"); continue
            S = VC(Ls, [ACT[a] for a in Nl], 4, NV=NV)
            r = {k: induced_rank(S, A, k, lambda c, m: c) for k in (1, 2, 3)}
            bad = [k for k in (1, 2, 3) if r[k] < HA[k]]
            verdicts.append(f"deg{bad}" if bad else "INCONCLUSIVE")
        ok = all(v != "INCONCLUSIVE" for v in verdicts)
        allok += ok
        print(f"   |D|={len(H):3d} H(elW)={[HA[k] for k in (1,2,3)]} "
              f"strata-orbits={len(verdicts)}: {verdicts} -> "
              f"{'(NR-sharp) holds' if ok else '*** INCONCLUSIVE ***'}",
              flush=True)
    print(f"   (NR-sharp) certified for {allok}/{len(tgt)}", flush=True)
