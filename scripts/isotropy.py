#!/usr/bin/env python3
"""Verification record for the isotropy paper (docs/paperM/isotropy.tex).

Three independent checks:

1. Twisted reachability censuses over the subgroups of Aut([2]) = G_2
   (dihedral of order 8) acting on De Morgan squares: for each subgroup,
   the graph of H-symmetric squares connected by H-symmetric cubes.
   Expected (paper, Prop. census + controls):
     <sw>, <g>      : generic square connects to a constant  (both contract)
     <n>, <n1>      : generic square does NOT connect        (K(H,1), free)
     Klein<sw,n>    : 72 nodes, generic component {3}, constants' {66}
     G2 (full)      : 18 nodes, generic isolated from the constant
2. Sieve structure for the collage decomposition: no morphism from a
   free-stratum object into a stabilized one, none between the two
   stabilized strata (small levels, exhaustive on samples).
3. The Z/3 fixed-stratum retraction of the cube: all identities of the
   equivariant interpolation on all 256 literal points.

Pure python + numpy; runtime a few minutes (DM(3) has 7,828,354 elements).
"""
import numpy as np
from itertools import product
import collections

# ---------------- free De Morgan algebras on the literal cube ----------------

def monotone(k):
    if k == 0:
        return [frozenset(), frozenset([()])]
    prev = monotone(k - 1)
    return [frozenset([p + (0,) for p in g]) | frozenset([p + (1,) for p in h])
            for g in prev for h in prev if g <= h]

DM2 = monotone(4)                     # 168 elements, coords (s0,s1,t0,t1)
pts4 = list(product((0, 1), repeat=4))

def unb4(b): return sum(x << j for j, x in enumerate(b))
def to16(f): return sum(1 << unb4(list(p)) for p in f)
mask2 = {to16(f): f for f in DM2}

def neg2(f):
    return frozenset(p for p in pts4
                     if (1 - p[1], 1 - p[0], 1 - p[3], 1 - p[2]) not in f)

def pre2(f, perm):
    return frozenset(p for p in pts4 if perm(p) in f)

SUB2 = {'sw': lambda p: (p[2], p[3], p[0], p[1]),
        'nb': lambda p: (p[1], p[0], p[3], p[2]),
        'n1': lambda p: (p[1], p[0], p[2], p[3]),
        'g':  lambda p: (p[3], p[2], p[1], p[0])}

def post(h, pq):
    (a, b), (sw, e1, e2) = pq, h
    x, y = (b, a) if sw else (a, b)
    if e1: x = neg2(x)
    if e2: y = neg2(y)
    return (x, y)

def orbit(H, pq): return {post(h, pq) for h in H}
def key(f): return tuple(sorted(tuple(x) for x in f))
def norm(H, pq): return min(orbit(H, pq), key=lambda x: (key(x[0]), key(x[1])))

s_el = frozenset(p for p in pts4 if p[0] == 1)
t_el = frozenset(p for p in pts4 if p[2] == 1)
zero2, one2 = frozenset(), frozenset(pts4)

def masks(k):
    if k == 0:
        return np.array([0, 1], dtype=np.uint64)
    prev = masks(k - 1); npts = 1 << (k - 1)
    ok = (prev[:, None] & ~prev[None, :]) == 0
    gi, hi = np.nonzero(ok)
    return prev[gi].astype(np.uint64) | (prev[hi].astype(np.uint64) << np.uint64(npts))

M6 = masks(6); N = len(M6); one = np.uint64(1)
assert N == 7828354

def bits(p): return [(p >> j) & 1 for j in range(6)]
def unb(b): return sum(x << j for j, x in enumerate(b))

def apply_pointmap(M, pm):
    out = np.zeros(len(M), dtype=np.uint64)
    for p in range(64):
        out |= ((M >> np.uint64(pm[p])) & one) << np.uint64(p)
    return out

PM = {'sw': [unb([bits(p)[2], bits(p)[3], bits(p)[0], bits(p)[1], bits(p)[4], bits(p)[5]]) for p in range(64)],
      'nb': [unb([bits(p)[1], bits(p)[0], bits(p)[3], bits(p)[2], bits(p)[4], bits(p)[5]]) for p in range(64)],
      'n1': [unb([bits(p)[1], bits(p)[0], bits(p)[2], bits(p)[3], bits(p)[4], bits(p)[5]]) for p in range(64)],
      'g':  [unb([bits(p)[3], bits(p)[2], bits(p)[1], bits(p)[0], bits(p)[4], bits(p)[5]]) for p in range(64)]}
negp = [unb([1 - bits(p)[1], 1 - bits(p)[0], 1 - bits(p)[3], 1 - bits(p)[2],
             1 - bits(p)[5], 1 - bits(p)[4]]) for p in range(64)]

def negM(M):
    out = np.zeros(len(M), dtype=np.uint64)
    for p in range(64):
        out |= ((one ^ ((M >> np.uint64(negp[p])) & one))) << np.uint64(p)
    return out

def face_pair(M):
    f0 = np.zeros(len(M), dtype=np.uint32); f1 = np.zeros(len(M), dtype=np.uint32)
    for p in range(64):
        b = bits(p); i4 = unb4(b[:4])
        v = ((M >> np.uint64(p)) & one).astype(np.uint32)
        if (b[4], b[5]) == (0, 1): f0 |= v << np.uint32(i4)
        elif (b[4], b[5]) == (1, 0): f1 |= v << np.uint32(i4)
    return f0, f1

print("precomputing transforms over DM(3)...")
T = {g: apply_pointmap(M6, PM[g]) for g in PM}
NEG_M6 = negM(M6)
F0, F1 = face_pair(M6)
order = np.argsort(M6); M6s = M6[order]
def idx_of(A): return order[np.searchsorted(M6s, A)]
IDX = {g: idx_of(T[g]) for g in T}
IDX_NEG = idx_of(NEG_M6)
allidx = np.arange(N)

# ---------------- 1. twisted reachability censuses ----------------

def census(Hname, H, gens, expect_connect):
    nodeset = set()
    for p in DM2:
        for q in DM2:
            ok = True
            for gname in gens:
                pp, qq = pre2(p, SUB2[gname]), pre2(q, SUB2[gname])
                if (pp, qq) not in orbit(H, (p, q)):
                    ok = False; break
            if ok:
                nodeset.add(norm(H, (p, q)))
    generic = norm(H, (s_el, t_el))
    constants = {norm(H, (a, b)) for a in (zero2, one2) for b in (zero2, one2)} & nodeset
    codes = set()
    for nd in nodeset:
        for pq in orbit(H, nd):
            codes.add((to16(pq[0]) << 16) | to16(pq[1]))
    codes_np = np.array(sorted(codes), dtype=np.uint64)
    edges = set()

    def add_edges(iu, iv):
        c0 = (F0[iu].astype(np.uint64) << np.uint64(16)) | F0[iv].astype(np.uint64)
        c1 = (F1[iu].astype(np.uint64) << np.uint64(16)) | F1[iv].astype(np.uint64)
        good = np.isin(c0, codes_np) & np.isin(c1, codes_np)
        for a, b in zip(c0[good], c1[good]):
            n0 = norm(H, (mask2[int(a) >> 16], mask2[int(a) & 0xffff]))
            n1 = norm(H, (mask2[int(b) >> 16], mask2[int(b) & 0xffff]))
            if n0 != n1:
                edges.add((n0, n1))

    for kassign in product(H, repeat=len(gens)):
        det = None
        for g, kk in zip(gens, kassign):
            if kk[0] == 1:
                det = (g, kk); break
        if det is not None:
            g, kk = det
            iu = allidx; iv = IDX[g][iu]
            if kk[1]: iv = IDX_NEG[iv]
            keep = (IDX[g][iv] == (IDX_NEG[iu] if kk[2] else iu))
            iu, iv = iu[keep], iv[keep]
            for g2, k2 in zip(gens, kassign):
                if (g2, k2) == (g, kk):
                    continue
                l1 = IDX[g2][iu]
                r1 = (IDX_NEG[iv] if k2[1] else iv) if k2[0] else (IDX_NEG[iu] if k2[1] else iu)
                l2 = IDX[g2][iv]
                r2 = (IDX_NEG[iu] if k2[2] else iu) if k2[0] else (IDX_NEG[iv] if k2[2] else iv)
                keep = (l1 == r1) & (l2 == r2)
                iu, iv = iu[keep], iv[keep]
            if len(iu):
                add_edges(iu, iv)
        else:
            fu = np.ones(N, dtype=bool); fv = np.ones(N, dtype=bool)
            for g, kk in zip(gens, kassign):
                fu &= (IDX[g] == (IDX_NEG if kk[1] else allidx))
                fv &= (IDX[g] == (IDX_NEG if kk[2] else allidx))
            iu = allidx[fu]; iv = allidx[fv]
            if len(iu) == 0 or len(iv) == 0:
                continue
            pu = set(zip(F0[iu].tolist(), F1[iu].tolist()))
            pv = set(zip(F0[iv].tolist(), F1[iv].tolist()))
            for a0, a1 in pu:
                for b0, b1 in pv:
                    if ((a0 << 16) | b0) in codes and ((a1 << 16) | b1) in codes:
                        n0 = norm(H, (mask2[a0], mask2[b0]))
                        n1 = norm(H, (mask2[a1], mask2[b1]))
                        if n0 != n1:
                            edges.add((n0, n1))
    adj = collections.defaultdict(set)
    for (a, b) in edges:
        adj[a].add(b); adj[b].add(a)
    seen = {generic}; stack = [generic]
    while stack:
        x = stack.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y); stack.append(y)
    conn = any(c in seen for c in constants)
    status = "OK" if conn == expect_connect else "MISMATCH"
    print(f"[{Hname}] nodes={len(nodeset)} edges={len(edges)} "
          f"generic~const={conn} comp={len(seen)}  {status}")
    assert conn == expect_connect
    return len(nodeset), len(edges), len(seen)

ID = (0, 0, 0); SW = (1, 0, 0); NB = (0, 1, 1); G = (1, 1, 1); N1 = (0, 1, 0)
KLEIN = [ID, SW, NB, G]
G2 = [(sw, e1, e2) for sw in (0, 1) for e1 in (0, 1) for e2 in (0, 1)]

census("<sw>   (contracts)", [ID, SW], ['sw'], True)
census("<g>    (contracts)", [ID, G], ['g'], True)
census("<n>    (free, BZ2)", [ID, NB], ['nb'], False)
census("<n1>   (free, BZ2)", [ID, N1], ['n1'], False)
n, e, c = census("Klein<sw,n>", KLEIN, ['sw', 'nb'], False)
assert (n, c) == (72, 3)
n, e, c = census("G2 (full)", G2, ['sw', 'n1'], False)
assert (n, c) == (18, 3)

# ---------------- 2. sieve structure (collage decomposition) ----------------

DM1 = monotone(2); pts2 = list(product((0, 1), repeat=2))
def neg1(f): return frozenset(p for p in pts2 if (1 - p[1], 1 - p[0]) not in f)

def compose(g, us, m):
    ptsm = list(product((0, 1), repeat=2 * m))
    out = set()
    for p in ptsm:
        vals = []
        for u in us:
            v = 1 if p in u else 0
            q = tuple(1 - p[i ^ 1] for i in range(len(p)))
            nv = 0 if q in u else 1
            vals.append((v, nv))
        if tuple(b for pair in vals for b in pair) in g:
            out.add(p)
    return frozenset(out)

def Korbit1(f):
    a, b = f
    return {(a, b), (b, a), (neg1(a), neg1(b)), (neg1(b), neg1(a))}

free1 = [(a, b) for a in DM1 for b in DM1 if b != a and b != neg1(a)]
import random
random.seed(0)
diag2 = [(d, d) for d in DM2]; anti2 = [(d, neg2(d)) for d in DM2]
viol = checked = 0
for f in random.sample(free1, 8):
    Kf = Korbit1(f)
    for g in random.sample(diag2, 40) + random.sample(anti2, 40):
        for u1 in DM1:
            for u2 in DM1:
                comp = (compose(g[0], [u1, u2], 1), compose(g[1], [u1, u2], 1))
                checked += 1
                if comp in Kf:
                    viol += 1
print(f"sieve: free->stabilized composites checked={checked} violations={viol}")
assert viol == 0
viol2 = 0
for f in [(d, d) for d in DM1]:
    Kf = Korbit1(f)
    for g in [(d, neg1(d)) for d in DM1]:
        for u in DM1:
            if (compose(g[0], [u], 1), compose(g[1], [u], 1)) in Kf:
                viol2 += 1
print(f"sieve: diag<->antidiag violations={viol2}")
assert viol2 == 0

# ---------------- 3. the Z/3 fixed-stratum retraction ----------------

PTS = list(product((0, 1), repeat=8))   # literal cube on x,y,z,t
X = lambda p: p[0]; Y = lambda p: p[2]; Z = lambda p: p[4]; Tv = lambda p: p[6]
def AND(*fs): return lambda p: min(f(p) for f in fs)
def OR(*fs): return lambda p: max(f(p) for f in fs)
def NEG(f):
    def g(p):
        q = tuple(1 - p[i ^ 1] for i in range(8))
        return 1 - f(q)
    return g
def SUB(f, sigma): return lambda p: f(sigma(p))
def sigA(p):  # x := ¬z, y := ¬x, z := y, t := t
    return (p[5], p[4], p[1], p[0], p[2], p[3], p[6], p[7])
def sigA2(p): return sigA(sigA(p))
def eq(f, g): return all(f(p) == g(p) for p in PTS)

m = AND(X, NEG(Y), NEG(Z))
G1 = OR(AND(X, NEG(Tv)), AND(m, Tv), AND(X, m))
G3 = NEG(SUB(G1, sigA))
G2c = NEG(SUB(G1, sigA2))
def face_t(f, e):
    tp = (0, 1) if e == 0 else (1, 0)
    return lambda p: f(p[:6] + tp)
def mono(f):
    return all(not (p[i] == 0 and f(p) > f(p[:i] + (1,) + p[i + 1:]))
               for p in PTS for i in range(8))
checks = [
    ("sigma^3 = id", all(sigA(sigA(sigA(p))) == p for p in PTS)),
    ("m invariant", eq(SUB(m, sigA), m)),
    ("G1∘σ = ¬G3", eq(SUB(G1, sigA), NEG(G3))),
    ("G2∘σ = ¬G1", eq(SUB(G2c, sigA), NEG(G1))),
    ("G3∘σ = G2", eq(SUB(G3, sigA), G2c)),
    ("t=0 faces", eq(face_t(G1, 0), X) and eq(face_t(G2c, 0), Y) and eq(face_t(G3, 0), Z)),
    ("t=1 faces", eq(face_t(G1, 1), m) and eq(face_t(G2c, 1), NEG(m)) and eq(face_t(G3, 1), NEG(m))),
    ("monotone", mono(G1) and mono(G2c) and mono(G3) and mono(m)),
]
for name, ok in checks:
    print(f"retraction: {name}: {'OK' if ok else 'FAIL'}")
    assert ok

print("\nall verifications passed")
