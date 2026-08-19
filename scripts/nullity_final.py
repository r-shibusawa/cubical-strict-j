"""The general-n nullity status table (O18, section 79), final form.

For every reflection-generated mixed class D <= B_n (n <= 4):

  (E)  which maximal strata carry a NONSTRICT invariant end class?
       none  ->  ABSOLUTE nullity  ->  separation needs only W1.
  (NR') for each such stratum l:  id_W must not factor through
       l/N_l = cube^m/Q_l.  Certified either by
         "acyclic-kill": Q_l fixes a vertex of l, so el(l/N_l) is
            F_2-acyclic (Thm W1) and a retraction would make el(W)
            acyclic, contradicting W1 for the mixed D;  or by
         the induced map H_*(el l/N_l) -> H_*(el W) failing to be
         surjective in some degree <= 3.
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build
from nr_sharp import VC, homology, induced_rank

for n in (2, 3, 4):
    ELEMS, idx, ID, NE, MUL, INV, ACT = build(n)
    NV = 1 << n
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
        if any(all(ACT[a][v] == v for a in R) for v in range(NV)): continue
        if close(R) != H: continue
        tgt.append(sorted(H))
    print(f"n={n}: reflection-generated mixed classes {len(tgt)}", flush=True)
    nabs = nrel = ncert = 0
    for H in sorted(tgt, key=len):
        loci = {}
        for a in H:
            if REFL[a]:
                L = frozenset(v for v in range(NV) if ACT[a][v] == v)
                loci[L] = 1
        maximal = [sorted(L) for L in loci if not any(L < L2 for L2 in loci)]
        # generators + words
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
        # strata orbit reps carrying a twisted end class
        seen = set(); carriers = []
        for Ls in maximal:
            key = min(tuple(sorted(ACT[g][v] for v in Ls)) for g in H)
            if key in seen: continue
            seen.add(key)
            Nl = [a for a in H if {ACT[a][v] for v in Ls} == set(Ls)]
            tw = 0
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
                       for ws in ch): tw += 1
            if tw: carriers.append((Ls, Nl, tw))
        if not carriers:
            nabs += 1
            print(f"   |D|={len(H):3d}: ABSOLUTE nullity "
                  f"(no twisted end class)", flush=True)
            continue
        nrel += 1
        A = VC(list(range(NV)), [ACT[a] for a in H], 4, NV=NV)
        HA = homology(A, 4)
        verd = []
        for Ls, Nl, tw in carriers:
            if any(all(ACT[a][w] == w for a in Nl) for w in Ls):
                verd.append("acyclic-kill"); continue
            S = VC(Ls, [ACT[a] for a in Nl], 4, NV=NV)
            r = {k: induced_rank(S, A, k, lambda c, m: c) for k in (1, 2, 3)}
            bad = [k for k in (1, 2, 3) if r[k] < HA[k]]
            verd.append(f"deg{bad}" if bad else "INCONCLUSIVE")
        ok = all(v != "INCONCLUSIVE" for v in verd)
        ncert += ok
        print(f"   |D|={len(H):3d}: RELATIVE; H(elW)={[HA[k] for k in (1,2,3)]}"
              f" carriers={len(carriers)} {verd} -> "
              f"{'(NR-sharp) certified' if ok else '*** INCONCLUSIVE ***'}",
              flush=True)
    print(f"   summary: absolute {nabs}, relative {nrel} "
          f"((NR-sharp) certified {ncert})", flush=True)
