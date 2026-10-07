"""Contracted monoids of 'cyclic' finite categories: objects 0..n-1 arranged in a cycle with
arrows x_i : i -> i+1 (mod n) (and optionally extra arrows), all words of length >= L with the
same endpoints identified.  Arrows = (src, tgt, len) with len in 0..L (len L = 'long').
These have non-idempotent D ∩ E for D = ideal of object 0, E = ideal of object 1, and cycles,
i.e. the regime not covered by paper 30.  Used to test tower stabilisation / surjectivity."""
import sys
from tower_search2 import scan

def cycle_monoid(n, L):
    arrows = []
    for s in range(n):
        for t in range(n):
            # lengths l >= 0 with l ≡ t - s (mod n), l < L, plus 'L' (long) if any word of length >= L exists
            for l in range(0, L):
                if (l - (t - s)) % n == 0: arrows.append((s, t, l))
            arrows.append((s, t, L))
    idx = {a: i + 1 for i, a in enumerate(arrows)}
    N = len(arrows) + 2; ZERO = N - 1
    T = [[0] * N for _ in range(N)]
    for a in range(N):
        for b in range(N):
            if a == 0: T[a][b] = b
            elif b == 0: T[a][b] = a
            elif a == ZERO or b == ZERO: T[a][b] = ZERO
            else:
                (s1, t1, l1), (s2, t2, l2) = arrows[a - 1], arrows[b - 1]
                if t1 != s2: T[a][b] = ZERO           # 'a then b'
                else:
                    l = l1 + l2
                    T[a][b] = idx[(s1, t2, l if l < L else L)]
    return T

if __name__ == "__main__":
    for n, L in [(2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (2, 6), (3, 6), (4, 5)]:
        T = cycle_monoid(n, L)
        p, u, h = scan(T, kmax=10, log=print)
        print(f"n={n} L={L}: |M|={len(T)} pairs={p} unstable={u} first-surjective={h}", flush=True)
