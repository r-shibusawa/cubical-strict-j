"""(R-ret) as a pure group-theoretic criterion (O18, section 84).

Normalising k = 1, a retraction class rho_0 : W -> l/N_l with
rho_0 . j = id is a delta_0-equivariant vertex map f_0 : V -> V_l with
f_0|_{V_l} = id.  Equivariance on V_l forces delta_0(h) to agree with h on
V_l whenever both v and sigma_h v lie in V_l; in particular
delta_0|_{N_l} = id mod P_l.  Hence, writing Q_l = N_l/P_l:

  (i)  there is a homomorphism  pi : D -> Q_l  whose restriction to N_l is
       the canonical projection N_l ->> Q_l  (a retraction of groups), and
       pi(h) must agree with h on V_l cap sigma_h^{-1}(V_l) for every h;
  (ii) for every vertex v of the cube, pi(Stab_D(v)) fixes a vertex of l.

Then f_0 is defined orbit-wise: f_0(v) := v for v in V_l, and for the
other orbits pick a pi(Stab_D(v))-fixed vertex of l.

This script checks the criterion directly and compares it with the
retraction search of branch2_check.py.
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

ok_classes = 0; ncar = 0; nok = 0
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
    seen = set(); rows = []
    for Ls in maximal:
        key = min(tuple(sorted(ACT[g][v] for v in Ls)) for g in H)
        if key in seen: continue
        seen.add(key)
        Nl = [a for a in H if {ACT[a][v] for v in Ls} == set(Ls)]
        Lset = set(Ls)
        found = False
        for imgs in itertools.product(Nl, repeat=len(gg)):
            d = {}
            for x in H:
                y = ID
                for k in word[x]: y = MUL[y][imgs[k]]
                d[x] = y
            if not all(d[MUL[a][b]] == MUL[d[a]][d[b]]
                       for a in H for b in H): continue
            # (i) delta_0(h) agrees with h on V_l cap h^{-1}(V_l)
            if not all(ACT[d[h]][v] == ACT[h][v]
                       for h in H for v in Ls if ACT[h][v] in Lset):
                continue
            # (ii) every vertex stabiliser maps into a fixed-type subgroup
            good = True
            for orb in orbs:
                v = orb[0]
                if v in Lset: continue
                St = [a for a in H if ACT[a][v] == v]
                if not any(all(ACT[d[a]][w] == w for a in St) for w in Ls):
                    good = False; break
            if good: found = True; break
        rows.append((len(Ls), len(Nl), found))
        ncar += 1; nok += found
    allok = all(f for _, _, f in rows)
    ok_classes += allok
    print(f"   |D|={len(H):3d}: strata-orbits " + ", ".join(
        f"(|l|={a},|N|={b},(R-ret)={'yes' if f else 'NO'})" for a, b, f in rows)
        + f" -> {'OK' if allok else '*** FAILS ***'}", flush=True)
print(f"   classes with (R-ret) at every maximal stratum: "
      f"{ok_classes}/{len(tgt)};  strata: {nok}/{ncar}", flush=True)
