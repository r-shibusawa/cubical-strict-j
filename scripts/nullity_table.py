"""The general-n nullity table (O18, section 79).

For every reflection-generated mixed class D <= B_n (n <= 4):

  (E) does an invariant END class with a NONSTRICT twist exist?
      (Boolean-exact: a delta-equivariant vertex map f : V_n -> V_l whose
      chosen values are not delta(D)-fixed.)  If NOT, the nullity theorem
      is ABSOLUTE for D and the separation needs nothing further.
  (NR) if such end classes exist, the nullity is RELATIVE and the
      separation needs "el(W) is not a retract of el(S_W)"; we certify it
      by q_* : H_*(el S_W) -> H_*(el W) failing to be surjective.
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build, analyse

def refl_table(ELEMS, ID, NE, n):
    R = []
    for a in range(NE):
        p, s = ELEMS[a]
        seen = [False]*n; ok = a != ID
        for i in range(n):
            if seen[i]: continue
            sg = s[i]; j = p[i]; seen[i] = True
            while j != i:
                seen[j] = True; sg ^= s[j]; j = p[j]
            if sg & 1: ok = False
        R.append(ok)
    return R

for n in (2, 3, 4):
    ELEMS, idx, ID, NE, MUL, INV, ACT = build(n)
    REFL = refl_table(ELEMS, ID, NE, n)
    def close(gens):
        S = {ID}; dq = deque([ID])
        while dq:
            x = dq.popleft()
            for g in gens:
                y = MUL[x][g]
                if y not in S: S.add(y); dq.append(y)
        return frozenset(S)
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
    print(f"n={n}: reflection-generated mixed classes: {len(tgt)}", flush=True)
    nab = nrel = nrok = 0
    for H in sorted(tgt, key=len):
        NV = 1 << n
        loci = {}
        for a in H:
            if REFL[a]:
                L = frozenset(v for v in range(NV) if ACT[a][v] == v)
                loci[L] = 1
        maximal = [sorted(L) for L in loci if not any(L < L2 for L2 in loci)]
        # ---- (E) twisted end classes ----
        gg = None
        for i, a in enumerate(H):
            for b in H[i:]:
                if len(close([a, b])) == len(H): gg = [a, b]; break
            if gg: break
        if gg is None:
            gg = []; span = {ID}
            for a in H:
                if a in span: continue
                gg.append(a); span = set(close(gg))
                if len(span) == len(H): break
        word = {ID: []}; dq = deque([ID])
        while dq:
            x = dq.popleft()
            for k, g in enumerate(gg):
                y = MUL[x][g]
                if y not in word: word[y] = word[x] + [k]; dq.append(y)
        orbreps = []; seenv = [False]*NV
        for v in range(NV):
            if seenv[v]: continue
            for a in H: seenv[ACT[a][v]] = True
            orbreps.append(v)
        stabs = [[a for a in H if ACT[a][v] == v] for v in orbreps]
        twisted = 0
        for Ls in maximal:
            Nl = [a for a in H if {ACT[a][v] for v in Ls} == set(Ls)]
            for imgs in itertools.product(Nl, repeat=len(gg)):
                d = {}
                for x in H:
                    y = ID
                    for k in word[x]: y = MUL[y][imgs[k]]
                    d[x] = y
                if not all(d[MUL[a][b]] == MUL[d[a]][d[b]]
                           for a in H for b in H): continue
                ch = []
                for v, St in zip(orbreps, stabs):
                    ws = [w for w in Ls if all(ACT[d[a]][w] == w for a in St)]
                    ch.append(ws)
                if any(not ws for ws in ch): continue
                if any(any(not all(ACT[d[x]][w] == w for x in H) for w in ws)
                       for ws in ch):
                    twisted += 1
        if twisted == 0:
            nab += 1
            print(f"   |D|={len(H):3d} strata={len(maximal):2d}: "
                  f"NO twisted end class -> ABSOLUTE nullity", flush=True)
            continue
        nrel += 1
        HA, HB, surj = analyse(H, ACT, n, maximal, top=4)
        bad = [k for k, (img, ha, hb) in surj.items() if img < ha]
        nrok += bool(bad)
        print(f"   |D|={len(H):3d} strata={len(maximal):2d}: twisted end "
              f"classes x{twisted} -> RELATIVE; H(elW)="
              f"{[HA[k] for k in sorted(HA)]} H(elS)="
              f"{[HB[k] for k in sorted(HB)]} q_* rank="
              f"{[surj[k][0] for k in sorted(surj)]} -> "
              f"{'(NR) certified, degree ' + str(bad) if bad else '(NR) INCONCLUSIVE in degrees <=3'}",
              flush=True)
    print(f"   summary: absolute {nab}, relative {nrel} of which (NR) "
          f"certified {nrok}", flush=True)
