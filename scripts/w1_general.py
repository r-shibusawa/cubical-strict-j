"""W1 for every reflection-generated mixed subgroup of B_n, n <= 4
(O18, section 77), via el(cube^n/D) ~ V^{*oo}/D.

W1 = "el(cube^n/D) is not contractible when D is mixed".  For
reflection-generated D one has pi_1 = D/<reflections> = 1, and el is
always Q-acyclic, so the witness has to be F_2-torsion in degree >= 2.
"""
import sys, itertools
from collections import deque, Counter
sys.path.insert(0, 'scripts')
from el_homology import build, el_homology

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
    mixed = []
    for H in classes.values():
        R = [a for a in H if REFL[a]]
        if not R: continue
        if any(all(ACT[a][v] == v for a in H) for v in range(1 << n)): continue
        mixed.append((H, close(R) == H))
    print(f"n={n}: mixed classes {len(mixed)} "
          f"(reflection-generated {sum(1 for _, g in mixed if g)})")
    top = 5 if n <= 3 else 4
    bad = []
    for H, gen in sorted(mixed, key=lambda x: len(x[0])):
        Hh = el_homology(H, ACT, n, top=top)
        pos = [d for d in range(1, top) if Hh[d]]
        tag = "reflection-generated" if gen else "not refl-gen"
        print(f"   |D|={len(H):3d} [{tag:20s}] H_1..H_{top-1} = "
              f"{[Hh[d] for d in range(1, top)]}"
              f"{'  <-- ALL ZERO' if not pos else ''}")
        if not pos: bad.append((H, gen))
    print(f"   W1 confirmed in degrees <= {top-1}: "
          f"{len(mixed) - len(bad)}/{len(mixed)}")
    print()
