"""(NR') with the two general kills and the universal-cover reduction
(O18, section 80).

Setting: D reflection-generated mixed, l a maximal stratum carrying a
twisted end class, N_l its setwise stabiliser, P_l the pointwise one,
Q_l = N_l/P_l <= B_m acting on l = cube^m.  (NR') says id_W does not
factor through l/N_l -> W; applying el it suffices that el(W) is not a
retract of X := el(l/N_l) = el(cube^m/Q_l).

Three general instruments (el(W) is simply connected because D is
reflection-generated, and is not F_2-acyclic by Theorem W1):

 (K1) ACYCLIC-KILL: Q_l fixes a vertex of l  =>  X is F_2-acyclic
      (Thm W1 in dimension m)  =>  a retract of X is acyclic  =>
      el(W) acyclic, contradicting W1.

 (K2) FREE-KILL: Q_l acts freely on the cells of l (no reflections)
      =>  X = B Q_l.  A simply connected retract of B Q_l lifts to the
      contractible universal cover, so the retraction is null and
      el(W) would be contractible -- again contradicting W1.

 (K3) UNIVERSAL-COVER REDUCTION: in general pi_1(X) = Q_l/<R(Q_l)>, and
      a simply connected retract lifts to the universal cover
      X~ = el(cube^m / <R(Q_l)>).  So one may replace N_l by the
      preimage N' of <R(Q_l)> and test the (smaller) map
      H_*(el(l/N')) -> H_*(el W) for surjectivity.
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build
from nr_sharp import VC, homology, induced_rank

def analyse_group(H, ACT, MUL, INV, ID, REFL, n, verbose=True):
    NV = 1 << n
    Hs = sorted(H)
    def close(gens):
        S = {ID}; dq = deque([ID])
        while dq:
            x = dq.popleft()
            for g in gens:
                y = MUL[x][g]
                if y not in S: S.add(y); dq.append(y)
        return frozenset(S)
    loci = {}
    for a in Hs:
        if REFL[a]:
            L = frozenset(v for v in range(NV) if ACT[a][v] == v)
            loci[L] = 1
    maximal = [sorted(L) for L in loci if not any(L < L2 for L2 in loci)]
    # generators / words for the end-twist census
    gg = None
    for i, a in enumerate(Hs):
        for b in Hs[i:]:
            if len(close([a, b])) == len(H): gg = [a, b]; break
        if gg: break
    if gg is None:
        gg = []; span = {ID}
        for a in Hs:
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
        for a in Hs: seenv[ACT[a][v]] = True
        orbreps.append(v)
    stabs = [[a for a in Hs if ACT[a][v] == v] for v in orbreps]
    seen = set(); carriers = []
    for Ls in maximal:
        key = min(tuple(sorted(ACT[g][v] for v in Ls)) for g in Hs)
        if key in seen: continue
        seen.add(key)
        Nl = [a for a in Hs if {ACT[a][v] for v in Ls} == set(Ls)]
        tw = 0
        for imgs in itertools.product(Nl, repeat=len(gg)):
            d = {}
            for x in Hs:
                y = ID
                for k in word[x]: y = MUL[y][imgs[k]]
                d[x] = y
            if not all(d[MUL[a][b]] == MUL[d[a]][d[b]]
                       for a in Hs for b in Hs): continue
            ch = []
            for v, St in zip(orbreps, stabs):
                ws = [w for w in Ls if all(ACT[d[a]][w] == w for a in St)]
                ch.append(ws)
            if any(not ws for ws in ch): continue
            if any(any(not all(ACT[d[x]][w] == w for x in Hs) for w in ws)
                   for ws in ch): tw += 1
        if tw: carriers.append((Ls, Nl, tw))
    if not carriers: return "ABSOLUTE", []
    A = VC(list(range(NV)), [ACT[a] for a in Hs], 4, NV=NV)
    HA = homology(A, 4)
    verd = []
    for Ls, Nl, tw in carriers:
        Pl = [a for a in Nl if all(ACT[a][w] == w for w in Ls)]
        # (K1) Q_l fixes a vertex of l ?
        if any(all(ACT[a][w] == w for a in Nl) for w in Ls):
            verd.append(("K1 acyclic-kill", None)); continue
        # (K2) Q_l free on cells of l ?  <=> no a in N_l acts on l with a
        # fixed cell, i.e. every a in N_l \ P_l moves every cell of l:
        # on the Boolean site, a fixes a cell of l iff a fixes a vertex of l
        if not any(a not in Pl and any(ACT[a][w] == w for w in Ls)
                   for a in Nl):
            verd.append(("K2 free-kill", None)); continue
        # (K3) replace N_l by the preimage of <R(Q_l)>
        Rq = [a for a in Nl if a not in Pl and any(ACT[a][w] == w for w in Ls)]
        Nprime = sorted(close(Rq + Pl)) if Rq else sorted(Pl)
        for label, grp in (("N_l", Nl), ("N' (univ. cover)", Nprime)):
            S = VC(Ls, [ACT[a] for a in grp], 4, NV=NV)
            r = {k: induced_rank(S, A, k, lambda c, m: c) for k in (1, 2, 3)}
            bad = [k for k in (1, 2, 3) if r[k] < HA[k]]
            if bad:
                verd.append((f"deg{bad} via {label}", None)); break
        else:
            HS = homology(VC(Ls, [ACT[a] for a in Nprime], 4, NV=NV), 4)
            verd.append(("INCONCLUSIVE",
                         (len(Ls), len(Nl), len(Nprime),
                          [HA[k] for k in (1, 2, 3)],
                          [HS[k] for k in (1, 2, 3)])))
    return "RELATIVE", verd

if __name__ == "__main__":
    for n in (4,):
        ELEMS, idx, ID, NE, MUL, INV, ACT = build(n)
        NV = 1 << n
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
            if any(all(ACT[a][v] == v for a in R) for v in range(NV)): continue
            if close(R) != H: continue
            tgt.append(H)
        print(f"n={n}: reflection-generated mixed classes {len(tgt)}",
              flush=True)
        nab = ncert = ninc = 0
        for H in sorted(tgt, key=len):
            kind, verd = analyse_group(H, ACT, MUL, INV, ID, REFL, n)
            if kind == "ABSOLUTE":
                nab += 1
                print(f"   |D|={len(H):3d}: ABSOLUTE", flush=True)
                continue
            tags = [v[0] for v in verd]
            ok = all(t != "INCONCLUSIVE" for t in tags)
            ncert += ok; ninc += (not ok)
            print(f"   |D|={len(H):3d}: RELATIVE {tags} -> "
                  f"{'(NR-sharp) certified' if ok else '*** INCONCLUSIVE ***'}",
                  flush=True)
            for t, info in verd:
                if info:
                    print(f"        residual: |l|={info[0]} |N_l|={info[1]} "
                          f"|N'|={info[2]} H(elW)={info[3]} "
                          f"H(el l/N')={info[4]}", flush=True)
        print(f"   summary: absolute {nab}, certified {ncert}, "
              f"inconclusive {ninc}", flush=True)
