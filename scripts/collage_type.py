"""(T-C) presheaf-level collage: the equivariant median interpolation.

Verifies, in the up-set representation of free De Morgan algebras
(monotone functions on the literal cube, negation via the
order-reversing pair-swap-complement involution):

  (1) self-duality of the median interpolant
        F(d,a,t) = (d & ~t) | (a & t) | (d & a):
        NOT F(d,a,t) == F(NOT d, NOT a, t)     [identity in DM(d,a,t)]
  (2) the face conditions F(d,a,0) = d, F(d,a,1) = a,
  (3) hence K-equivariance of
        Phi = (F(d,a,t), F(d,~a,t)) : cube^3 -> cube^2
      for the Klein group K = <sw, nb> acting on cube^2 by
      sw(x,y)=(y,x), nb(x,y)=(~x,~y), and on the join model by
      sw: a |-> ~a, nb: (d,a) |-> (~d,~a),
  (4) decides whether Phi admits a STRICT section: elements
        d, a, t in DM(x,y)  with  F(d,a,t) = x and F(d,~a,t) = y
      (exhaustive search over all |DM(2)|^3 = 168^3 triples).

Everything is an exact finite computation.
"""

import itertools, sys

# ---------- literal cube L_n and DM(n) as bit-mask up-sets ----------

def build(n):
    """Points of L_n = {0,1}^{2n}; return (npoints, leq pairs, involution)."""
    N = 1 << (2 * n)
    def coords(p):
        return [(p >> i) & 1 for i in range(2 * n)]
    leq = []
    for p in range(N):
        cp = coords(p)
        for q in range(N):
            cq = coords(q)
            if all(a <= b for a, b in zip(cp, cq)):
                leq.append((p, q))
    # involution rho: swap each pair (x_i, ~x_i) AND complement
    rho = []
    for p in range(N):
        c = coords(p)
        d = []
        for i in range(n):
            vx, vnx = c[2 * i], c[2 * i + 1]
            d += [1 - vnx, 1 - vx]
        q = sum(b << i for i, b in enumerate(d))
        rho.append(q)
    return N, leq, rho

def monotone_masks(N, leq):
    out = []
    for m in range(1 << N):
        ok = True
        for p, q in leq:
            if (m >> p) & 1 and not (m >> q) & 1:
                ok = False
                break
        if ok:
            out.append(m)
    return out

def NOT(m, N, rho):
    r = 0
    for p in range(N):
        if not (m >> rho[p]) & 1:
            r |= 1 << p
    return r

def gen(i, n, N):
    """Generator x_i as a mask: bit p set iff coordinate 2i of p is 1."""
    m = 0
    for p in range(N):
        if (p >> (2 * i)) & 1:
            m |= 1 << p
    return m

# ---------- (1)-(3): identities in DM(d,a,t)  (L_3, 64 points) ----------

N3, leq3, rho3 = build(3)
D, A, T = gen(0, 3, N3), gen(1, 3, N3), gen(2, 3, N3)
FULL3 = (1 << N3) - 1

def not3(m): return NOT(m, N3, rho3)

def F(d, a, t):
    return (d & not3(t)) | (a & t) | (d & a)

# sanity: involution and De Morgan on generators
assert not3(not3(D)) == D
assert not3(D & A) == (not3(D) | not3(A))
assert not3(0) == FULL3

# (1) self-duality
sd = not3(F(D, A, T)) == F(not3(D), not3(A), T)
# also the a-negated instance used for the second coordinate
sd2 = not3(F(D, not3(A), T)) == F(not3(D), A, T)
print("self-duality  NOT F(d,a,t) == F(~d,~a,t):", sd)
print("self-duality (a-negated instance):        ", sd2)

# (2) faces: substitute t = 0, 1 (constants)
f0 = F(D, A, 0) == D
f1 = F(D, A, FULL3) == A
print("face t=0: F(d,a,0) == d:", f0)
print("face t=1: F(d,a,1) == a:", f1)

# (3) equivariance of Phi = (F(d,a,t), F(d,~a,t))
phi1, phi2 = F(D, A, T), F(D, not3(A), T)
sw_ok = (phi2, phi1) == (F(D, not3(A), T), F(D, not3(not3(A)), T))
nb_ok = (not3(phi1), not3(phi2)) == (F(not3(D), not3(A), T),
                                     F(not3(D), A, T))
print("sw-equivariance of Phi:", sw_ok)
print("nb-equivariance of Phi:", nb_ok)

if not (sd and sd2 and f0 and f1 and sw_ok and nb_ok):
    sys.exit("FAILURE: an identity does not hold")

# ---------- (4): strict section search over DM(x,y)^3 ----------

N2, leq2, rho2 = build(2)
X, Y = gen(0, 2, N2), gen(1, 2, N2)
dm2 = monotone_masks(N2, leq2)
print("|DM(2)| =", len(dm2))
assert len(dm2) == 168  # Dedekind M(4)

not2 = {m: NOT(m, N2, rho2) for m in dm2}

sections = []
for t in dm2:
    nt = not2[t]
    for d in dm2:
        base = d & nt
        if base & ~X & ((1 << N2) - 1):
            continue  # F1 ⊇ d&~t must be ≤ x
        da = d  # for F1: (a&t)|(d&a) with base
        for a in dm2:
            F1 = base | (a & t) | (d & a)
            if F1 != X:
                continue
            na = not2[a]
            F2 = base | (na & t) | (d & na)
            if F2 == Y:
                sections.append((d, a, t))

print("strict sections found:", len(sections))
if sections:
    for s in sections[:5]:
        print("  (d,a,t) masks:", s)
print("ALL CHECKS COMPLETE")
