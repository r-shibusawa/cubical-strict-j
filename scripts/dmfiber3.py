#!/usr/bin/env python3
"""n=2 sphere-surjectivity check + n=3 fiber census via numpy.

Coordinate layout for DM(3): 6 literal coords (x1,x1',x2,x2',x3,x3'),
point index p = sum b_j << j, element = u64 bitmask of accepted points.
"""
import numpy as np
from itertools import product
from collections import Counter

# ---------- generic helpers (small n, set-based) ----------
def monotone(k):
    if k == 0:
        return [frozenset(), frozenset([()])]
    prev = monotone(k - 1)
    return [frozenset([p + (0,) for p in g]) | frozenset([p + (1,) for p in h])
            for g in prev for h in prev if g <= h]

def face_set(f, i, b):
    want = (0, 1) if b == 0 else (1, 0)
    return frozenset(p[:2*i] + p[2*i+2:] for p in f
                     if p[2*i] == want[0] and p[2*i+1] == want[1])

# ---------- (i) sphere surjectivity at n=2 ----------
DM1 = monotone(2)
DM2 = monotone(4)
# compatible sphere: (f10,f11,f20,f21) in DM1^4 such that for the two
# pairs (i,j)=(1,2): restricting f_{1,e} at x2:=e' equals restricting
# f_{2,e'} at x1:=e  (both are vertices, elements of DM(0) = {0,1}).
def vtx(f, e):  # restrict the single remaining pair to e
    return face_set(f, 0, e)
compat = 0
realized = set()
for f in DM2:
    realized.add(tuple(face_set(f, i, b) for i in (0, 1) for b in (0, 1)))
cnt = 0
for f10, f11, f20, f21 in product(DM1, repeat=4):
    ok = all(vtx((f10, f11)[e1], e2) == vtx((f20, f21)[e2], e1)
             for e1 in (0, 1) for e2 in (0, 1))
    if ok:
        cnt += 1
print(f"n=2: compatible spheres = {cnt}, realized boundaries = {len(realized)}",
      "SURJECTIVE" if cnt == len(realized) else "NOT surjective")

# ---------- (ii) n=3 census ----------
# build M(6) as u64 masks by the pair construction over coord 5.
def masks(k):
    """all monotone functions on k coords as sorted numpy array of uint64
    bitmasks over 2^k points."""
    if k == 0:
        return np.array([0, 1], dtype=np.uint64)
    prev = masks(k - 1)
    npts = 1 << (k - 1)
    g = prev[:, None]
    h = prev[None, :]
    ok = (g & ~h) == 0
    gi, hi = np.nonzero(ok)
    return (prev[gi].astype(np.uint64)
            | (prev[hi].astype(np.uint64) << np.uint64(npts)))

M5 = masks(5)
print("M(5) count:", len(M5))
M6 = masks(6)
print("M(6) count:", len(M6))

# faces: for pair i in {0,1,2} and e in {0,1}, select the 16 points with
# (b_{2i}, b_{2i+1}) = (0,1) if e==0 else (1,0), compact to 4 remaining
# coords in increasing coord order.
def face_maps(i, e):
    want = (0, 1) if e == 0 else (1, 0)
    sel = []
    for p in range(64):
        bits = [(p >> j) & 1 for j in range(6)]
        if (bits[2*i], bits[2*i+1]) == want:
            rem = [bits[j] for j in range(6) if j not in (2*i, 2*i+1)]
            idx = sum(b << j for j, b in enumerate(rem))
            sel.append((p, idx))
    return sel

faces = np.zeros((len(M6), 6), dtype=np.uint16)
col = 0
for i in range(3):
    for e in (0, 1):
        sel = face_maps(i, e)
        acc = np.zeros(len(M6), dtype=np.uint16)
        for p, idx in sel:
            acc |= (((M6 >> np.uint64(p)) & np.uint64(1)).astype(np.uint16)
                    << np.uint16(idx))
        faces[:, col] = acc
        col += 1

uniq, counts = np.unique(faces, axis=0, return_counts=True)
print(f"n=3: |DM(3)| = {len(M6)}")
print(f"  distinct boundaries B(3) = {len(uniq)}")
dist = Counter(counts.tolist())
print(f"  fiber size distribution = {dict(sorted(dist.items()))}")
print(f"  max fiber size = {counts.max()}")
