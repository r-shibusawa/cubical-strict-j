"""Non-retraction (NR) for every reflection-generated mixed subgroup of
B_n, n <= 4 (O18, section 79).

(NR): el(W) is not a retract of el(S_W)  <=  q_* not surjective.
Calibration: B_3 reproduces the hand computation of section 44
(dim H^3(el W) = 2 while the strata part can only reach rank 1).
"""
import sys, itertools
from collections import deque, Counter
sys.path.insert(0, 'scripts')
from strata_retract import build, analyse

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
        tgt.append(H)
    print(f"n={n}: reflection-generated mixed classes: {len(tgt)}", flush=True)
    ok = 0
    for H in sorted(tgt, key=len):
        loci = {}
        for a in H:
            if REFL[a]:
                L = frozenset(v for v in range(1 << n) if ACT[a][v] == v)
                loci[L] = 1
        maximal = [sorted(L) for L in loci if not any(L < L2 for L2 in loci)]
        HA, HB, surj = analyse(H, ACT, n, maximal, top=4)
        bad = [k for k, (img, ha, hb) in surj.items() if img < ha]
        ok += bool(bad)
        print(f"   |D|={len(H):3d} strata={len(maximal)}  H(elW)="
              f"{[HA[k] for k in sorted(HA)]}  H(elS)="
              f"{[HB[k] for k in sorted(HB)]}  q_* rank="
              f"{[surj[k][0] for k in sorted(surj)]}  -> "
              f"{'NR holds (misses degree ' + str(bad) + ')' if bad else '*** q_* SURJECTIVE ***'}",
              flush=True)
    print(f"   (NR) confirmed for {ok}/{len(tgt)}", flush=True)
