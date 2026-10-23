"""Alternating torsion filtrations for representations of the two-vertex quivers A_2 and the 2-cycle.

A representation M of the quiver with vertices 1, 2 and arrows a : 1 -> 2, b : 2 -> 1 is a pair of GF(2)-vector
spaces (V1, V2) with linear maps a, b.  (A_2 is the case b = 0; the 2-cycle is the general case.)  Let
    T  = { M : V2 = 0 }   (radical t(M)  = (Ker a, 0)),
    T' = { M : V1 = 0 }   (radical t'(M) = (0, Ker b)),
two hereditary torsion theories on the module category of the path algebra (which is Noetherian).  The canonical
alternating filtration of M is
    X_1 = t'(M),  X_2 = preimage of t(M/X_1),  X_3 = preimage of t'(M/X_2), ...
and M lies in E_k iff X_{2k} = M.  Since a subrepresentation is a pair (U1, U2) with a(U1) <= U2 and b(U2) <= U1,
a t-step replaces U1 by a^{-1}(U2) and a t'-step replaces U2 by b^{-1}(U1); no quotients need to be formed.

The script shows:
  * for A_2 (b = 0) every representation lies in E_1 (the t'-step gives (0, V2), the t-step then gives M);
  * for the 2-cycle the string module M_N (basis e_1, ..., e_N alternating between the vertices, each arrow sending
    e_i to e_{i+1} and e_N to 0) needs a filtration of length N (or N+1), unbounded in N, so the join torsion class
    (everything, for finite-dimensional modules) is not E_k for any k;
  * the length of the filtration of a direct sum is the maximum of the lengths;
  * a random search over small representations records the maximal length found in each dimension among the
    representations in the join class (those not exhausted by the filtration are outside T v T').
"""
import itertools as it
import random

def span_contains(basis, v):
    """membership of bitmask v in the GF(2)-span of basis (list of bitmasks), by elimination"""
    rows = list(basis)
    for bit in range(64):
        piv = next((i for i in range(len(rows)) if rows[i] >> bit & 1), None)
        if piv is None:
            continue
        p = rows.pop(piv)
        rows = [r ^ p if r >> bit & 1 else r for r in rows]
        if v >> bit & 1:
            v ^= p
    return v == 0

def apply(cols, v):
    img = 0
    for i, c in enumerate(cols):
        if v >> i & 1:
            img ^= c
    return img

def preimage(cols, d, U):
    """all v in GF(2)^d with apply(cols, v) in span(U) -- returned as a list of all vectors (brute force, d small)"""
    return [v for v in range(1 << d) if span_contains(U, apply(cols, v))]

def length(d1, d2, a, b, first="t'"):
    """length of the canonical alternating filtration (number of steps until the whole module is reached),
    starting with a t'-step (default) or a t-step.  U1, U2 are kept as lists of all their vectors."""
    U1, U2 = [0], [0]
    full = (1 << d1, 1 << d2)
    step = first
    n = 0
    while (len(U1), len(U2)) != full:
        n += 1
        if step == "t'":
            U2 = preimage(b, d2, U1)      # t'(M/X) = (0, Ker b-bar): new U2 = b^{-1}(U1)
            step = "t"
        else:
            U1 = preimage(a, d1, U2)      # t(M/X) = (Ker a-bar, 0): new U1 = a^{-1}(U2)
            step = "t'"
        if n > 2 * (d1 + d2) + 2:
            raise RuntimeError("filtration does not exhaust: M is not in the join torsion class")
    return n

def string_module(N, start=1):
    """basis e_1..e_N; e_i at vertex 'start' for i odd, the other vertex for i even; arrows e_i -> e_{i+1}, e_N -> 0"""
    v1 = [i for i in range(N) if (i % 2 == 0) == (start == 1)]
    v2 = [i for i in range(N) if i not in v1]
    idx1 = {e: k for k, e in enumerate(v1)}
    idx2 = {e: k for k, e in enumerate(v2)}
    a = [0] * len(v1); b = [0] * len(v2)
    for i in range(N - 1):
        if i in idx1:
            a[idx1[i]] = 1 << idx2[i + 1]
        else:
            b[idx2[i]] = 1 << idx1[i + 1]
    return len(v1), len(v2), a, b

def dsum(M, M2):
    d1, d2, a, b = M; e1, e2, c, d = M2
    return d1 + e1, d2 + e2, a + [x << d2 for x in c], b + [x << d1 for x in d]

if __name__ == "__main__":
    print("A_2 (b = 0), all representations with d1, d2 <= 3: maximal length of the t'-first filtration")
    mx = 0
    for d1 in range(4):
        for d2 in range(4):
            for a in it.product(range(1 << d2), repeat=d1):
                mx = max(mx, length(d1, d2, list(a), [0] * d2))
    print("  max length =", mx, "(so every representation is in E_1)")
    mx = 0
    for d1 in range(4):
        for d2 in range(4):
            for a in it.product(range(1 << d2), repeat=d1):
                mx = max(mx, length(d1, d2, list(a), [0] * d2, first="t"))
    print("  max length with a t-step first =", mx)

    print("2-cycle, string modules M_N starting at vertex 1 / vertex 2: filtration length (t' first)")
    for N in range(1, 13):
        M1 = string_module(N, 1); M2 = string_module(N, 2)
        print(f"  N={N:2d}: start 1 -> {length(*M1)}, start 2 -> {length(*M2)}")
    print("direct sums M_3 + M_7, M_5 + M_10:")
    print("  ", length(*dsum(string_module(3, 1), string_module(7, 1))), length(*dsum(string_module(5, 2), string_module(10, 1))))

    random.seed(1)
    print("2-cycle, random representations: maximal filtration length found per (d1, d2)")
    for d1, d2 in [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5)]:
        best = 0; outside = 0; trials = 300 if d1 >= 4 else 2000
        for _ in range(trials):
            a = [random.randrange(1 << d2) for _ in range(d1)]
            b = [random.randrange(1 << d1) for _ in range(d2)]
            try:
                best = max(best, length(d1, d2, a, b))
            except RuntimeError:
                outside += 1
        print(f"  ({d1},{d2}): max length {best} among {trials - outside} representations in the join class ({outside} outside)")
