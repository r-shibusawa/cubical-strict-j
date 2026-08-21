"""Crown-poset probes on the Dedekind site (O22).

(a) The Cavallo-Sattler diamond map u(x,y,z) = (x|y, y|z, z|x):
    verify it admits no section (no s with u o s = id), and
    compute the congruence structure of its image.
(b) The crown subobject: C_3 embedded in [1]^3 by
    c(i)_j = 1 iff floor(i/2) <= j <= ceil(i/2)  (CS Def A.11);
    W = the subpresheaf of the representable cube^3 of cells with
    vertex-image in c(C_3).  Triangulation Betti should be the
    circle [1,1,0] -- the monotone circle inside the 3-cube.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, cube_cells
from dedekind_triangulate import coface
from dedekind_sweep import strict_census

# (a) diamond map: u = (x v y, y v z, z v x) as 3-tuple over F(3)
pts3, f3 = F(3)
def mk(fn): return tuple(1 if fn(p) else 0 for p in pts3)
u = (mk(lambda p: p[0] | p[1]), mk(lambda p: p[1] | p[2]),
     mk(lambda p: p[2] | p[0]))
idc = (mk(lambda p: p[0]), mk(lambda p: p[1]), mk(lambda p: p[2]))
sections = 0
for s in itertools.product(f3, repeat=3):
    # u o s: substitute s into u: compose(u_i, s, 3, 3)
    us = tuple(compose(ui, s, 3, 3) for ui in u)
    if us == idc: sections += 1
print(f"(a) diamond map sections found: {sections} (expected 0)",
      flush=True)
# image congruence: kernel pairs at level 1
_, f1 = F(1)
lvl1 = list(itertools.product(f1, repeat=3))
img = {}
for a in lvl1:
    ua = tuple(compose(ui, a, 3, 1) for ui in u)
    img.setdefault(ua, []).append(a)
merged = sum(1 for v in img.values() if len(v) > 1)
print(f"(a) level-1 cells of cube^3: {len(lvl1)}, image classes: "
      f"{len(img)}, merged classes: {merged}", flush=True)

# (b) crown subobject: crown C_3 = 6 elements 0..5 in [1]^3:
# c(i)_j = 1 iff floor(i/2) <= j <= ceil(i/2), indices mod-ish:
# CS: teeth 1,3,5 over gaps 0,2,4; explicit for n=3:
def crown_vertex(i):
    lo = i // 2; hi = (i + 1) // 2
    return tuple(1 if lo <= j <= hi else 0 for j in range(3))
# hmm for i=5: lo=2,hi=3 -> j=2 only? standard crown: use mod:
# teeth: {e_j + e_{j+1 mod 3}}? Use: odd i=2j+1: vertex with 1s at
# j and j+1 mod 3; even i=2j: vertex e_j.
def crown_vertex2(i):
    j = i // 2
    if i % 2 == 0:
        return tuple(1 if k == j else 0 for k in range(3))
    return tuple(1 if k in (j, (j+1) % 3) else 0 for k in range(3))
CR = sorted({crown_vertex2(i) for i in range(6)})
print(f"(b) crown vertex set ({len(CR)}):", CR, flush=True)
# poset order on CR inherited from [1]^3; W([k]) = triples over
# F(k) whose joint vertex image lies in CR
def W_level(k):
    ptsk, fk = F(k)
    out = []
    for c in itertools.product(fk, repeat=3):
        imgs = {tuple(ci[t] for ci in c) for t in range(len(ptsk))}
        if imgs <= set(CR): out.append(c)
    return out
import sys as _s
from dedekind_sweep import strict_census  # not used for subobject
# triangulation Betti of the subpresheaf (levels 0..3)
def rank2(cols):
    piv = {}; r = 0
    for v in cols:
        while v:
            l = v.bit_length() - 1
            if l in piv: v ^= piv[l]
            else: piv[l] = v; r += 1; break
    return r
levels = {k: W_level(k) for k in range(4)}
ind = {k: {c: i for i, c in enumerate(levels[k])} for k in levels}
print(f"(b) W levels: {[len(levels[k]) for k in range(4)]}", flush=True)
from dedekind_site import restrict
def dmat(q):
    cols = []
    for cell in levels[q]:
        v = 0
        for i in range(q + 1):
            uu = coface(i, q)
            fc = restrict(cell, uu, 3, q, q - 1)
            v ^= 1 << ind[q - 1][fc]
        cols.append(v)
    return cols
r = {q: rank2(dmat(q)) for q in range(1, 4)}
b = [len(levels[0]) - r[1],
     len(levels[1]) - r[1] - r[2],
     len(levels[2]) - r[2] - r[3]]
print(f"(b) T(crown subobject) F2-Betti deg0..2 = {b} "
      f"(circle = [1,1,0])", flush=True)
