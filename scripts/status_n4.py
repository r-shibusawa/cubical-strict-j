"""Corrected resolution status at n = 4 (O18, section 84).

For each reflection-generated mixed class D <= B_4 report which of the
three UNCONDITIONAL routes settles it:

 (a) ABSOLUTE nullity: no twisted end class  ->  Phi_D is the witness
     (relative nullity degenerates to the absolute one).
 (b) (NR') at every carrier: el(W) is not a retract of el(l/N_l)
     (acyclic-kill / free-kill / non-surjective induced map)  ->  Branch 2
     is impossible, so Phi_D is the witness.
 (c) EQUIVARIANT TRANSFER: some maximal stratum l is a D-equivariant
     retract of cube^n (delta = id: f(v) = v on V_l, f(sigma_h v) =
     sigma_h f(v)) with Q_l separating.  Then the mux upgrades r to a
     D-equivariant deformation retraction, W ~ l/D in BOTH structures,
     and the witness for Q_l transfers (section 81.1).  This route is
     independent of the nullity analysis.

Anything else is OPEN.
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build
from nr_sharp import VC, homology, induced_rank

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
print(f"n=4: reflection-generated mixed classes {len(tgt)}", flush=True)

def sep_closed_form(Ls, Nl):
    """closed form (section 75) for Q_l acting on l"""
    Pl = [a for a in Nl if all(ACT[a][w] == w for w in Ls)]
    Rq = [a for a in Nl if a not in Pl and any(ACT[a][w] == w for w in Ls)]
    if not Rq: return False
    return not any(all(ACT[a][w] == w for a in Rq) for w in Ls)

cnt = {'a': 0, 'b': 0, 'c': 0, 'open': 0}
for H in sorted(tgt, key=len):
    loci = {}
    for a in H:
        if REFL[a]:
            L = frozenset(v for v in range(NV) if ACT[a][v] == v)
            loci[L] = 1
    maximal = [sorted(L) for L in loci if not any(L < L2 for L2 in loci)]
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
    orbs = []; seenv = [False]*NV
    for v in range(NV):
        if seenv[v]: continue
        orb = {ACT[a][v] for a in H}
        for w in orb: seenv[w] = True
        orbs.append(sorted(orb))
    # (c) equivariant retraction onto a D-invariant stratum
    route_c = False
    for Ls in maximal:
        Nl = [a for a in H if {ACT[a][v] for v in Ls} == set(Ls)]
        if len(Nl) != len(H): continue          # need l D-invariant
        Lset = set(Ls)
        okc = True
        for orb in orbs:
            v = orb[0]
            if v in Lset: continue
            St = [a for a in H if ACT[a][v] == v]
            if not any(all(ACT[a][w] == w for a in St) for w in Ls):
                okc = False; break
        if okc and sep_closed_form(Ls, Nl): route_c = True; break
    # carriers (twisted end classes)
    seen = set(); carriers = []
    for Ls in maximal:
        key = min(tuple(sorted(ACT[g][v] for v in Ls)) for g in H)
        if key in seen: continue
        seen.add(key)
        Nl = [a for a in H if {ACT[a][v] for v in Ls} == set(Ls)]
        tw = False
        for imgs in itertools.product(Nl, repeat=len(gg)):
            d = {}
            for x in H:
                y = ID
                for k in word[x]: y = MUL[y][imgs[k]]
                d[x] = y
            if not all(d[MUL[a][b]] == MUL[d[a]][d[b]]
                       for a in H for b in H): continue
            ch = []
            for orb in orbs:
                v = orb[0]; St = [a for a in H if ACT[a][v] == v]
                ws = [w for w in Ls if all(ACT[d[a]][w] == w for a in St)]
                ch.append(ws)
            if any(not ws for ws in ch): continue
            if any(any(not all(ACT[d[x]][w] == w for x in H) for w in ws)
                   for ws in ch): tw = True; break
        if tw: carriers.append((Ls, Nl))
    if not carriers:
        cnt['a'] += 1
        print(f"   |D|={len(H):3d}: (a) ABSOLUTE", flush=True); continue
    A = VC(list(range(NV)), [ACT[a] for a in H], 4, NV=NV)
    HA = homology(A, 4)
    allkilled = True
    for Ls, Nl in carriers:
        Pl = [a for a in Nl if all(ACT[a][w] == w for w in Ls)]
        if any(all(ACT[a][w] == w for a in Nl) for w in Ls): continue   # K1
        if not any(a not in Pl and any(ACT[a][w] == w for w in Ls)
                   for a in Nl): continue                               # K2
        S = VC(Ls, [ACT[a] for a in Nl], 4, NV=NV)
        r = {k: induced_rank(S, A, k, lambda c, m: c) for k in (1, 2, 3)}
        if not any(r[k] < HA[k] for k in (1, 2, 3)): allkilled = False; break
    if allkilled:
        cnt['b'] += 1
        print(f"   |D|={len(H):3d}: (b) all carriers killed by (NR')",
              flush=True)
    elif route_c:
        cnt['c'] += 1
        print(f"   |D|={len(H):3d}: (c) equivariant transfer", flush=True)
    else:
        cnt['open'] += 1
        print(f"   |D|={len(H):3d}: *** OPEN *** (carriers "
              f"{[len(L) for L, _ in carriers]})", flush=True)
print(f"   status: {cnt}", flush=True)
