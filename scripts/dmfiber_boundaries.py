#!/usr/bin/env python3
"""Two independent checks for the boundary classification
(Theorem `boundaries` of the paper):

1. B(n) as the number of antichains of the face-point subposet of the
   literal cube (n = 1, 2, 3).
2. The Sperner-extremal fiber construction at n = 4: the middle layer
   of the diagonal cube (an antichain of size C(4,2) = 6) yields a
   fiber isomorphic to 2^6, all 64 members sharing their boundary.

Expected output:
  n=1: face points=2, antichains=4
  n=2: face points=12, antichains=82
  n=3: face points=56, antichains=4829136
  n=4 construction: antichain 6; m/M up-closed True True;
    bnd(m)==bnd(M) True; all 64 subsets same boundary True
"""
from itertools import product, combinations

def facept(p, n):
    return any((p[2*i], p[2*i+1]) in ((0, 1), (1, 0)) for i in range(n))

def diag(p, n):
    return all((p[2*i], p[2*i+1]) in ((0, 0), (1, 1)) for i in range(n))

def le(p, q):
    return all(a <= b for a, b in zip(p, q))

def count_antichains(P):
    P = sorted(P, key=sum)
    N = len(P)
    comp = [0] * N
    for i in range(N):
        for j in range(N):
            if i != j and (le(P[i], P[j]) or le(P[j], P[i])):
                comp[i] |= 1 << j
    cnt = 0
    def dfs(i, banned):
        nonlocal cnt
        if i == N:
            cnt += 1
            return
        dfs(i + 1, banned)
        if not (banned >> i) & 1:
            dfs(i + 1, banned | comp[i])
    dfs(0, 0)
    return cnt

for n in (1, 2, 3):
    pts = [p for p in product((0, 1), repeat=2*n) if facept(p, n)]
    print(f"n={n}: face points={len(pts)}, antichains={count_antichains(pts)}")

# ---- n = 4 Sperner construction ----
n = 4
pts = list(product((0, 1), repeat=2*n))
D = [p for p in pts if diag(p, n) and sum(p) // 2 == n // 2]
assert all(not (le(p, q) or le(q, p)) for p, q in combinations(D, 2))
above = {c for d in D for c in pts if facept(c, n) and le(d, c) and c != d}
m = {q for c in above for q in pts if le(c, q)}
M = m | set(D)
def upclosed(S):
    return all(q in S for p in S for q in pts if le(p, q))
def face(S, i, e):
    want = (0, 1) if e == 0 else (1, 0)
    return frozenset(p[:2*i] + p[2*i+2:] for p in S
                     if (p[2*i], p[2*i+1]) == want)
same = all(face(m, i, e) == face(M, i, e) for i in range(n) for e in (0, 1))
ok = all(upclosed(m | set(sub))
         and all(face(m | set(sub), i, e) == face(m, i, e)
                 for i in range(n) for e in (0, 1))
         for r in range(len(D) + 1) for sub in combinations(D, r))
print(f"n=4 construction: antichain {len(D)}; m/M up-closed "
      f"{upclosed(m)} {upclosed(M)}; bnd(m)==bnd(M) {same}; "
      f"all 64 subsets same boundary {ok}")
