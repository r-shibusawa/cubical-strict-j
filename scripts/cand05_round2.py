"""Targeted round-2 check (O22): enumerate ALL 3-box assemblies
over the FULL round-1 universe (W-classes + every fresh square of
every 2-box filler) that contain the identity cell as a face, and
test whether any filler passes the homotopy descent with
slice_0 = id.  Key structural laws being tested:
  (VERTEX LAW)  old-cell homotopies from id die at k=0;
  (PROVENANCE LAW) a fresh filler's (diag x id)-restriction is
    interior-fresh while its (top x id)-restriction face-factors,
    so condition (c) can never hold for a generic fresh filler.
Expected: zero valid id-moving homotopies.  Any hit would break
the isolation conjecture (and be checked in detail).
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, cube_cells, all_maps, restrict, Quotient
from dedekind_stage1 import Stage1, const_f, var_f
from collections import deque

K = 3
c00 = const_f(1,0); x1 = var_f(1,0); c11 = const_f(1,1)
idents = [(1, (c00, x1), (x1, c00)), (1, (x1, x1), (x1, c11))]
W = Quotient(2, idents, K)
S = Stage1(W)
idnode = ('w', W.cls(2, (var_f(2,0), var_f(2,1))))

# full round-1 universe of level-2 cells (all fresh squares)
pool = S.level(2)
print(f"full level-2 universe: {len(pool)}", flush=True)

def rcell(cell, u, k): return S.restrict_cell(cell, u, 2, k)
def edge_sub(axis, eps, axis2, eps2):
    rem = [a for a in range(3) if a != axis]
    j = rem.index(axis2)
    return tuple(const_f(1, eps2) if t == j else var_f(1, 0)
                 for t in range(2))

FACES = [(a, e) for a in range(3) for e in (0, 1)]
hits = 0; assemblies = 0
# id sits at slot (a_t, 0) for the homotopy axis a_t: enumerate
# a_t and missing face m != (a_t, 0)
for a_t in range(3):
    id_slot = (a_t, 0)
    for miss in FACES:
        if miss == id_slot: continue
        present = [f for f in FACES if f != miss]
        order = [f for f in present if f != id_slot]
        order.sort(key=lambda f: 0 if f[0] != a_t else 1)
        def bt(i, asg):
            global hits, assemblies
            if assemblies >= 3000000: return
            if i == len(order):
                assemblies += 1
                if assemblies % 100000 == 0:
                    print(f"  ... {assemblies} assemblies "
                          f"(axis={a_t} miss={miss}, hits={hits})",
                          flush=True)
                # descent check with t-axis a_t (same as stage2)
                valid = True
                for k in range(0, 3):
                    groups = {}
                    for u in all_maps(2, k):
                        groups.setdefault(W.cls(k, u), []).append(u)
                    for g in groups.values():
                        if len(g) < 2: continue
                        vals = []
                        for u in g:
                            ptsk1 = F(k+1)[0]; ptsk = F(k)[0]
                            idxk = {q: t for t, q in enumerate(ptsk)}
                            lift = [tuple(comp[idxk[q[:-1]]]
                                          for q in ptsk1)
                                    for comp in u]
                            tvar = tuple(q[-1] for q in ptsk1)
                            trip = []
                            vi = 0
                            for ax in range(3):
                                if ax == a_t: trip.append(tvar)
                                else: trip.append(lift[vi]); vi += 1
                            val = None
                            for (fa, fe) in present:
                                if trip[fa] == const_f(k+1, fe):
                                    rem = [x for x in range(3)
                                           if x != fa]
                                    val = rcell(asg[(fa, fe)],
                                        (trip[rem[0]], trip[rem[1]]),
                                        k+1)
                                    break
                            if val is None:
                                valid = False; break
                            vals.append(val)
                        if not valid: break
                        if any(v != vals[0] for v in vals):
                            valid = False; break
                    if not valid: break
                if valid:
                    s1 = asg[(a_t, 1)]
                    if s1 != idnode:
                        hits += 1
                        print(f"  HIT: axis={a_t} miss={miss} "
                              f"slice1={s1}", flush=True)
                return
            f = order[i]
            for cand in pool:
                asg[f] = cand
                ok = True
                for g in present[:len(present)]:
                    if g not in asg or g == f: continue
                    (aa, ee), (bb, ff2) = f, g
                    if aa == bb: continue
                    r1 = rcell(cand, edge_sub(aa, ee, bb, ff2), 1)
                    r2 = rcell(asg[g], edge_sub(bb, ff2, aa, ee), 1)
                    if r1 != r2: ok = False; break
                if ok: bt(i + 1, asg)
            del asg[f]
        bt(0, {id_slot: idnode})
print(f"id-adjacent assemblies: {assemblies}, "
      f"valid id-moving homotopies: {hits}", flush=True)
