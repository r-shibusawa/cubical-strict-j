"""W1 for all reflection-generated mixed subgroups of B_4 (O18, section 77).

Using el(cube^n/D) = B(O_F(D)) (orbit_category.py, calibrated against the
three published el-computations), W1 -- "el(cube^n/D) is not contractible
for D mixed" -- becomes a finite group-theoretic computation.

pi_1 = D/<reflections> = 1 for reflection-generated D, so the witness must
be H_2 or higher; and el is always Q-acyclic, so it must be torsion.
"""
import sys, itertools
from collections import deque, Counter
sys.path.insert(0, 'scripts')
from orbit_category import build, orbit_category, nerve_homology

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
    tgt = {}
    for H in subs:
        R = [a for a in H if REFL[a]]
        if not R: continue
        if any(all(ACT[a][v] == v for a in R) for v in range(1 << n)): continue
        if close(R) != H: continue
        key = min(tuple(sorted(MUL[MUL[g][a]][INV[g]] for a in H))
                  for g in range(NE))
        tgt.setdefault(key, H)
    print(f"n={n}: reflection-generated mixed classes: {len(tgt)} "
          f"(orders {sorted(Counter(len(H) for H in tgt.values()).items())})")
    res = Counter()
    for H in sorted(tgt.values(), key=len):
        reps, mors, comp, ident = orbit_category(H, MUL, INV, ID, ACT, n)
        nm = sum(len(L) for L in mors.values()) - len(reps)
        top = 4 if nm <= 40 else (3 if nm <= 120 else 2)
        try:
            Hh, dims = nerve_homology(reps, mors, comp, ident, top=top)
        except MemoryError:
            print(f"   |D|={len(H):3d}: nerve too large (morphisms={nm})")
            res['skipped'] += 1
            continue
        deg = [d for d in sorted(Hh) if d >= 1 and Hh[d]]
        verdict = ("W1 OK  (H_%d != 0)" % deg[0]) if deg else \
                  ("H_1..H_%d all zero" % (top - 1))
        res[bool(deg)] += 1
        print(f"   |D|={len(H):3d} objs={len(reps)} mors={nm} "
              f"H_*(<={top-1}) = "
              f"{[Hh[d] for d in range(1, top)]}  -> {verdict}")
    print(f"   summary: {dict(res)}")
    print()
