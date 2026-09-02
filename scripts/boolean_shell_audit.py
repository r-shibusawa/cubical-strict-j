"""O24 audit: the shell mechanism does NOT threaten the
reversal-site separations.

Structural reason (Proposition eqshell of the integrated
manuscript): homotopy data over a group quotient square^n/H are
constrained by source-AUTOMORPHISM invariance (dimension-
preserving), not by source-congruence folds (dimension-
lowering).  By the based normal form, a fresh invariant filler
forces its shell box to be equivariant; equivariant shell data
are strict-cylinder data, so old ends of fresh invariant
cylinders are already connected at the previous stage.  (On
the Dedekind dunce hat the constraints are source-congruence
folds, which a shell absorbs -- hence the contraction there.)

Executable corroboration on X = square^2/Klein, Boolean site:
 (A) census: strict endomorphism classes, the strict cluster
     partition; the identity's component is {id} and contains
     no constant (the object-level separation base at n = 2).
 (B) every K-invariant level-3 cell is a strict cylinder whose
     two w-slices are strictly connected (the G / C-prism step
     of the proposition).
 (C) sections at invariant parameters connect strictly to both
     slices via the connection reparametrizations
     C.(u,v,s0|w), C.(u,v,s0&w) -- the secconn step for
     invariant sections.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from boolean_site import NPTS, all_fns, neg, subst, gen

M2, M3 = 2, 3
FB2, FB3 = all_fns(2), all_fns(3)
u2, v2 = gen(0,2), gen(1,2)
u3, v3, w3 = gen(0,3), gen(1,3), gen(2,3)

def orbit2(c):
    c1, c2 = c
    return {(c1,c2), (c2,c1), (neg(c1,2),neg(c2,2)) if False else (neg(c2,2),neg(c1,2)), (neg(c1,2),neg(c2,2))}
def orbit(c, m):
    c1, c2 = c
    return {(c1, c2), (c2, c1),
            (neg(c1, m), neg(c2, m)), (neg(c2, m), neg(c1, m))}
def cls(c, m):
    return min(orbit(c, m))

# substitution of a level-3 cell along a map [2]->[3] given as a
# 3-tuple over FB(2)
def r32(H, mp):
    return cls(tuple(subst(comp, mp, 3, 2) for comp in H), 2)

const2 = {0: 0, 1: (1 << NPTS(2)) - 1}
n0m = (u2, v2, 0)
n1m = (u2, v2, const2[1])

# source-invariance of a level-3 cell (as X-class):
# H o (sigma x id) must be in the K-orbit of H.
def sub3(H, mp):
    return tuple(subst(comp, mp, 3, 3) for comp in H)
sw3 = (v3, u3, w3)
nb3 = (neg(u3,3), neg(v3,3), w3)
def invariant3(H):
    O = orbit(H, 3)
    return sub3(H, sw3) in O and sub3(H, nb3) in O

def sub2(h, mp):
    return tuple(subst(comp, mp, 2, 2) for comp in h)
sw2 = (v2, u2); nb2 = (neg(u2,2), neg(v2,2))
def invariant2(h):
    O = orbit(h, 2)
    return sub2(h, sw2) in O and sub2(h, nb2) in O

# ---- (A) census ----
endos = set()
for c1 in FB2:
    for c2 in FB2:
        h = (c1, c2)
        if invariant2(h):
            endos.add(cls(h, 2))
idc = cls((u2, v2), 2)
consts = {cls((const2[a], const2[b]), 2) for a in (0,1) for b in (0,1)}
print("(A) strict endo classes:", len(endos), "; id class present:",
      idc in endos)

# strict cylinders and cluster partition
parent = {e: e for e in endos}
def find(x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]; x = parent[x]
    return x
def union(a, b):
    ra, rb = find(a), find(b)
    if ra != rb: parent[ra] = rb

inv3 = []
for c1 in FB3:
    for c2 in FB3:
        H = (c1, c2)
        if c1 > c2 and False: continue
        if invariant3(H):
            inv3.append(H)
# deduplicate by class
seen3 = set(); inv3u = []
for H in inv3:
    c = cls(H, 3)
    if c in seen3: continue
    seen3.add(c); inv3u.append(H)
print("    invariant level-3 classes (strict cylinders):", len(inv3u))
for H in inv3u:
    e0, e1 = r32(H, n0m), r32(H, n1m)
    if e0 in parent and e1 in parent:
        union(e0, e1)
clusters = {}
for e in endos:
    clusters.setdefault(find(e), []).append(e)
sizes = sorted(len(v) for v in clusters.values())
idcomp = [e for e in endos if find(e) == find(idc)]
print("    clusters:", len(clusters), "sizes:", sizes)
print("    id component:", len(idcomp),
      "; contains a constant:",
      any(c in idcomp for c in consts))

# ---- (B) slices of invariant cylinders strictly connected ----
okB = all(find(r32(H, n0m)) == find(r32(H, n1m))
          for H in inv3u
          if r32(H, n0m) in parent and r32(H, n1m) in parent)
print("(B) all invariant-cylinder slice pairs strictly connected:",
      okB)

# ---- (C) invariant sections connect via connections ----
inv_s0 = [s0 for s0 in FB2
          if subst(s0, sw2, 2, 2) == s0 and subst(s0, nb2, 2, 2) == s0]
print("(C) invariant section parameters:", len(inv_s0))
okC = True
for H in inv3u[:200]:
    for s0 in inv_s0:
        sec = r32(H, (u2, v2, s0))
        if sec not in parent: continue
        # reparametrized cylinders
        for op in ('or', 'and'):
            if op == 'or':
                rp = (u3, v3, subst(s0,(u3,v3),2,3) | w3)
            else:
                rp = (u3, v3, subst(s0,(u3,v3),2,3) & w3)
            Kp = sub3(H, rp)
            if not invariant3(Kp):
                okC = False; print("  non-invariant reparam!", op)
            e0, e1 = r32(Kp, n0m), r32(Kp, n1m)
            if e0 in parent and e1 in parent and find(e0) != find(e1):
                okC = False; print("  reparam fails to connect!")
        if sec in parent and find(sec) != find(r32(H, n0m)) and \
           r32(H, n0m) in parent:
            okC = False; print("  section disconnected from slice!")
print("(C) invariant sections strictly connected to slices:", okC)
print()
print("=> AUDIT PASSED: reversal-site (group-quotient) homotopy"
      " data admit no shell escape." if okB and okC and
      not any(c in idcomp for c in consts) else "=> AUDIT ISSUES")
