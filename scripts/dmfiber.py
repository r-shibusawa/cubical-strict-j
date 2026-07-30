#!/usr/bin/env python3
"""Boundary fibers in free De Morgan algebras DM(n).

Element of DM(n) = monotone Boolean function on 2n literal coordinates
(x1, x1', x2, x2', ...), i.e. the free bounded distributive lattice on
the 2n literals.  Face x_i := 0 sets (x_i, x_i') = (0,1); face
x_i := 1 sets (1,0).  Boundary of f = tuple of its 2n faces (elements
of DM(n-1)).  We enumerate DM(n) for n = 1, 2 (and DM(3) via the
pair construction), compute the boundary fibers, and report:
  - number of distinct boundaries B(n)
  - fiber size distribution
  - max fiber size
  - verification: every fiber equals the full interval [min, max]
  - verification: chi(k) = (a & ~k) | (k & b) | (a & b) has constant
    faces (the cylinder/interpolation property) on sample fibers
"""
import sys
from itertools import product
from collections import Counter

def monotone_functions(nvars):
    """All monotone f: {0,1}^nvars -> {0,1} as frozensets of accepted points
    (points = tuples).  Recursive pair construction: f = (g at x_last=0,
    h at x_last=1) with g <= h."""
    if nvars == 0:
        return [frozenset()], [frozenset([()])]  # bottom, top as the two fns
    # represent as set of accepted points
    def rec(k):
        if k == 0:
            return [frozenset(), frozenset([()])]
        prev = rec(k - 1)
        out = []
        for g in prev:
            for h in prev:
                if g <= h:
                    f = frozenset([p + (0,) for p in g]) | frozenset([p + (1,) for p in h])
                    out.append(f)
        return out
    return rec(nvars)

def face(f, nvars, i, b):
    """Restrict pair i (coords 2i, 2i+1) to (0,1) if b==0 else (1,0).
    Returns a monotone function on 2(n-1) coords (as frozenset of points)."""
    want = (0, 1) if b == 0 else (1, 0)
    out = set()
    for p in f:
        if p[2*i] == want[0] and p[2*i+1] == want[1]:
            out.add(p[:2*i] + p[2*i+2:])
    return frozenset(out)

def boundary(f, n):
    return tuple(face(f, n, i, b) for i in range(n) for b in (0, 1))

def le(f, g):
    return f <= g

def run(n):
    els = monotone_functions(2 * n)
    print(f"n={n}: |DM({n})| = {len(els)}")
    fibers = {}
    for f in els:
        fibers.setdefault(boundary(f, n), []).append(f)
    sizes = Counter(len(v) for v in fibers.values())
    print(f"  distinct boundaries B({n}) = {len(fibers)}")
    print(f"  fiber size distribution (size: count) = {dict(sorted(sizes.items()))}")
    print(f"  max fiber size = {max(sizes)}")
    # interval check: fiber == [min, max]
    ok_interval = True
    for bnd, fib in fibers.items():
        fmin = frozenset.intersection(*fib)
        fmax = frozenset.union(*fib)
        # count elements of DM(n) in [fmin, fmax]
        cnt = sum(1 for g in els if fmin <= g <= fmax)
        if cnt != len(fib):
            ok_interval = False
            print(f"  INTERVAL FAIL at boundary with fiber size {len(fib)}: interval has {cnt}")
    print(f"  every fiber is the full interval [min,max]: {ok_interval}")
    # chi interpolation check on the largest fiber: chi(a,b) with fresh k
    # chi as element of DM over coords + one literal pair (k, k'):
    # (a & ~k)|(k & b)|(a & b) where ~k is the literal k'.
    # Check: face k:=0 gives a, face k:=1 gives b, and every face x_i:=e
    # of chi is the (constant-in-k image of the) common face of a,b.
    big = max(fibers.values(), key=len)
    a, b = big[0], big[-1]
    chi = set()
    for p in product((0,1), repeat=2*n):
        for k, kp in product((0,1), repeat=2):
            va = p in a
            vb = p in b
            v = (va and kp == 1) or (k == 1 and vb) or (va and vb)
            if v:
                chi.add(p + (k, kp))
    chi = frozenset(chi)
    # monotone sanity
    def is_monotone(f, m):
        pts = list(f)
        for p in pts:
            for j in range(m):
                if p[j] == 0:
                    q = p[:j] + (1,) + p[j+1:]
                    if q not in f:
                        # q must be accepted if it dominates an accepted point
                        return False
        return True
    mono = is_monotone(chi, 2*n + 2)
    f0 = face(chi, n + 1, n, 0)  # k := 0  (pair index n is the k-pair)
    f1 = face(chi, n + 1, n, 1)
    print(f"  chi monotone: {mono}; chi|k=0 == a: {f0 == a}; chi|k=1 == b: {f1 == b}")
    # facewise constancy: for each original face, chi's face should be
    # the face of a (== face of b) extended constantly in (k,k').
    ok_const = True
    for i in range(n):
        for e in (0, 1):
            fa = face(a, n, i, e)
            fc = face(chi, n + 1, i, e)  # function on remaining coords + (k,k')
            const_ext = frozenset(p + (k, kp) for p in fa
                                  for k, kp in product((0,1), repeat=2))
            if fc != const_ext:
                ok_const = False
    print(f"  chi faces constant on boundary: {ok_const}")
    return len(fibers), sizes

for n in (1, 2):
    run(n)
    print()
