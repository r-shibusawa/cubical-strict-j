"""Sweep 2 (O22): the EZ danger zone and composite gluings.

(a) all pairs of distinct level-2 cells of cube^2 (630): these
    include identifying the GENERIC square with connection-
    degenerate squares -- the Eilenberg-Zilber pathology that
    blocks the relative-elegance method at two connections;
(b) all pairs of single identifications from sweep 1 (double
    identifications, ~861 combos): figure-eights, tori-bits,
    composite collapses.
Same invariants: T-Betti (deg 0..2) vs strict [id]~const.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, cube_cells, Quotient
from dedekind_triangulate import tri_homology
from dedekind_sweep import strict_census, cellname

K = 3
jobs = []
l2 = cube_cells(2, 2)
for A, B in itertools.combinations(l2, 2):
    jobs.append([(2, A, B)])
singles = []
verts = cube_cells(2, 0)
for A, B in itertools.combinations(verts, 2):
    singles.append((0, A, B))
l1 = cube_cells(2, 1)
for A, B in itertools.combinations(l1, 2):
    singles.append((1, A, B))
for s1_, s2_ in itertools.combinations(singles, 2):
    jobs.append([s1_, s2_])
print(f"sweep2 over {len(jobs)} quotients "
      f"({len(list(itertools.combinations(l2,2)))} level-2 pairs + "
      f"doubles)", flush=True)
cands = 0; bugs = 0; checked = 0
for idents in jobs:
    W = Quotient(2, idents, K)
    betti = tri_homology(W, 2, K)
    contr = strict_census(W)
    checked += 1
    acyc = (betti[0] == 1 and all(b == 0 for b in betti[1:]))
    if acyc and not contr:
        cands += 1
        print(f"  CANDIDATE: {[(j, cellname(A), cellname(B)) for (j,A,B) in idents]} "
              f"T={betti}", flush=True)
    if contr and not acyc:
        bugs += 1
        print(f"  BUG?: {[(j, cellname(A), cellname(B)) for (j,A,B) in idents]} "
              f"T={betti}", flush=True)
    if checked % 200 == 0:
        print(f"  ... {checked}/{len(jobs)} (cands {cands}, bugs {bugs})",
              flush=True)
print(f"done: {checked}, candidates {cands}, bugs {bugs}", flush=True)
