"""The four residual classes of the (NR') table (O18, section 80).

They are the cases where the maximal stratum quotient l/N_l is itself a
SEPARATING object (for n=4 it is the Klein object W_K = cube^2/K), so
el cannot separate el(W) from el(l/N_l).  But then the right move is the
opposite one: if l/N_l is a strict RETRACT of W, the separation of
l/N_l TRANSFERS to W by the retract-transfer theorem of paper 14, and the
collage argument for D is not needed at all.

A strict retraction r : W -> l/N_l is, on the Boolean site, a map of
vertex sets f : V -> V_l with
    f(sigma_h v) = sigma_h(f(v))   (h in D, acting on l through Q_l)
    f(v) = v                        (v in V_l),
i.e. a D-equivariant retraction of vertex sets; it exists iff every
D-orbit on V has a representative v with Stab_D(v) fixing some w in V_l,
compatibly with the identity on V_l.
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build

n = 4
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

def close(g):
    S = {ID}; dq = deque([ID])
    while dq:
        x = dq.popleft()
        for a in g:
            y = MUL[x][a]
            if y not in S: S.add(y); dq.append(y)
    return frozenset(S)

RES = [
    ("R1 = <twisted diagonal, block swap>",
     [idx[((0, 1, 3, 2), (1, 1, 0, 0))], idx[((1, 0, 2, 3), (0, 0, 1, 1))],
      idx[((2, 3, 0, 1), (0, 0, 0, 0))]]),
    ("R2 = <sw01> x K_23 (product)",
     [idx[((1, 0, 2, 3), (0, 0, 0, 0))], idx[((0, 1, 3, 2), (0, 0, 0, 0))],
      idx[((0, 1, 2, 3), (0, 0, 1, 1))]]),
    ("R3 (|D|=24, transitive)",
     [idx[((0, 1, 3, 2), (1, 1, 0, 0))], idx[((1, 2, 0, 3), (0, 0, 0, 0))],
      idx[((0, 2, 1, 3), (1, 1, 1, 1))]]),
    ("R4 = K wr Z/2 (|D|=32)",
     [idx[((1, 0, 2, 3), (0, 0, 0, 0))], idx[((0, 1, 2, 3), (1, 1, 0, 0))],
      idx[((2, 3, 0, 1), (0, 0, 0, 0))]]),
]
for name, gens in RES:
    D = sorted(close(gens))
    loci = {}
    for a in D:
        if REFL[a]:
            L = frozenset(v for v in range(NV) if ACT[a][v] == v)
            loci[L] = 1
    maximal = [sorted(L) for L in loci if not any(L < L2 for L2 in loci)]
    print(f"{name}: |D|={len(D)}, maximal strata sizes "
          f"{sorted(len(L) for L in maximal)}")
    seen = set()
    for Ls in maximal:
        key = min(tuple(sorted(ACT[g][v] for v in Ls)) for g in D)
        if key in seen: continue
        seen.add(key)
        Nl = [a for a in D if {ACT[a][v] for v in Ls} == set(Ls)]
        Pl = [a for a in Nl if all(ACT[a][w] == w for w in Ls)]
        if len(Nl) != len(D): 
            print(f"    stratum |l|={len(Ls)}: N_l proper ({len(Nl)}), "
                  f"no D-equivariant retraction possible")
            continue
        # orbit-wise search for a D-equivariant retraction V -> V_l
        orbs = []; seenv = [False]*NV
        for v in range(NV):
            if seenv[v]: continue
            orb = {ACT[a][v] for a in D}
            for w in orb: seenv[w] = True
            orbs.append(sorted(orb))
        ok = True; witness = {}
        for orb in orbs:
            v = orb[0]
            St = [a for a in D if ACT[a][v] == v]
            if v in Ls:
                cands = [v]
            else:
                cands = [w for w in Ls if all(ACT[a][w] == w for a in St)]
            if not cands: ok = False; break
            witness[v] = cands[0]
        print(f"    stratum |l|={len(Ls)} |N_l|={len(Nl)} |P_l|={len(Pl)} "
              f"|Q_l|={len(Nl)//len(Pl)}: D-equivariant vertex retraction "
              f"{'EXISTS' if ok else 'does NOT exist'}")


# --- twisted retractions: r : W -> l/N_l need not be induced by a
# D-equivariant map into l; it is a TWISTED end class f (delta-equivariant
# V -> V_l), and r . j = id iff f restricted to V_l agrees with some
# element of N_l acting on l.
print()
print("twisted retractions (r . j = id up to the deck action of N_l):")
for name, gens in RES:
    D = sorted(close(gens))
    loci = {}
    for a in D:
        if REFL[a]:
            L = frozenset(v for v in range(NV) if ACT[a][v] == v)
            loci[L] = 1
    maximal = [sorted(L) for L in loci if not any(L < L2 for L2 in loci)]
    gg = None
    for i, a in enumerate(D):
        for b in D[i:]:
            if len(close([a, b])) == len(D): gg = [a, b]; break
        if gg: break
    if gg is None:
        gg = []; span = {ID}
        for a in D:
            if a in span: continue
            gg.append(a); span = set(close(gg))
            if len(span) == len(D): break
    word = {ID: []}; dq = deque([ID])
    while dq:
        x = dq.popleft()
        for k, g in enumerate(gg):
            y = MUL[x][g]
            if y not in word: word[y] = word[x] + [k]; dq.append(y)
    orbs = []; seenv = [False]*NV
    for v in range(NV):
        if seenv[v]: continue
        orb = {ACT[a][v] for a in D}
        for w in orb: seenv[w] = True
        orbs.append(sorted(orb))
    seen = set(); found_any = []
    for Ls in maximal:
        key = min(tuple(sorted(ACT[g][v] for v in Ls)) for g in D)
        if key in seen: continue
        seen.add(key)
        Nl = [a for a in D if {ACT[a][v] for v in Ls} == set(Ls)]
        hit = False
        for imgs in itertools.product(Nl, repeat=len(gg)):
            d = {}
            for x in D:
                y = ID
                for k in word[x]: y = MUL[y][imgs[k]]
                d[x] = y
            if not all(d[MUL[a][b]] == MUL[d[a]][d[b]]
                       for a in D for b in D): continue
            # build all delta-equivariant f orbit-wise, requiring that on
            # V_l it agrees with some k in N_l
            for k in Nl:
                ok = True; f = {}
                for orb in orbs:
                    v = orb[0]
                    St = [a for a in D if ACT[a][v] == v]
                    if v in Ls:
                        w = ACT[k][v]
                        if not all(ACT[d[a]][w] == w for a in St):
                            ok = False; break
                    else:
                        cands = [w for w in Ls
                                 if all(ACT[d[a]][w] == w for a in St)]
                        if not cands: ok = False; break
                        w = cands[0]
                    f[v] = w
                if ok: hit = True; break
            if hit: break
        found_any.append((len(Ls), len(Nl), hit))
    print(f"  {name}: " + ", ".join(
        f"|l|={a} |N_l|={b} -> {'RETRACT' if c else 'none'}"
        for a, b, c in found_any))
