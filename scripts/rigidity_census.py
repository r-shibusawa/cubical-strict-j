"""Sieve-landing dichotomy census, closed form (O20).

KEY IDENTITY: for a twisted-equivariant F (F o sigma_h =
sigma_{c^{-1}hc} o F), a deck set D_F(h) is non-singleton iff
sigma_{d1^{-1}d2} o F = F for d1 != d2, i.e. iff F is a
STABILIZED cell.  So deck freedom = stabilized = lands in the
sieve: one condition, and the dichotomy theorem reads

  either SOME twisted map is stabilized  (=> the identity
  factors through the sieve by a one-step cylinder: reduction),
  or NO twisted map is stabilized (=> all decks are singletons,
  the strict homotopy component of the identity is exactly the
  twisted classes, and it contains no constant, no sieve-landing
  map, and no strictly invariant map: Phi-bar_N separates).

Existence of a stabilized twisted map is decidable orbitwise in
closed form: choices at different vertex orbits are independent,
so a stabilized c-twisted map stabilized by s exists iff for
every orbit rep v the set

  A_{c,s}(v) = { w : w fixed by c^{-1}Stab(v)c and by every
                 N-conjugate of s }

is nonempty.  We also report the twisted-map count as a product
over orbits."""
import sys
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build

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
    fr = list(subs.items())
    while fr:
        new = []
        for H, gens in fr:
            for g in range(NE):
                if g in H: continue
                H2 = close(gens + [g])
                if H2 not in subs:
                    subs[H2] = gens + [g]; new.append((H2, gens + [g]))
        fr = new
    classes = {}
    for H in subs:
        key = min(tuple(sorted(MUL[MUL[g][a]][INV[g]] for a in H))
                  for g in range(NE))
        classes.setdefault(key, H)
    tgt = []
    for H in classes.values():
        R = [a for a in H if REFL[a]]
        if not R or close(R) != H: continue
        if any(all(ACT[a][v] == v for a in R)
               for v in range(1 << n)): continue
        tgt.append(sorted(H))
    print(f"\nn={n}: {len(tgt)} reflection-generated mixed classes",
          flush=True)
    V = 1 << n
    reductions = 0
    for N in sorted(tgt, key=len):
        orb_of = {}; reps = []
        for v in range(V):
            if v in orb_of: continue
            reps.append(v)
            for h in N: orb_of[ACT[h][v]] = v
        stab = {v: [h for h in N if ACT[h][v] == v] for v in reps}
        # conjugacy closure of each s in N (s ranges over N\1)
        red_wit = None
        tot = 0
        for c in N:
            ci = INV[c]
            allowed = []
            for v in reps:
                conj = [MUL[MUL[ci][h]][c] for h in stab[v]]
                allowed.append([w for w in range(V)
                                if all(ACT[g][w] == w for g in conj)])
            prod = 1
            for A in allowed: prod *= len(A)
            tot += prod
            if red_wit is None:
                for s in N:
                    if s == ID: continue
                    sconj = {MUL[MUL[INV[g]][s]][g] for g in N}
                    if all(any(all(ACT[t][w] == w for t in sconj)
                               for w in A) for A in allowed):
                        red_wit = (c, s); break
        if red_wit:
            reductions += 1
            print(f"  |N|={len(N):3d}: twisted={tot:8d} -> REDUCTION "
                  f"(stabilized twisted map exists)", flush=True)
        else:
            print(f"  |N|={len(N):3d}: twisted={tot:8d} -> RIGID: "
                  f"Phi-bar separates", flush=True)
    print(f"  reduction classes: {reductions}/{len(tgt)}", flush=True)
