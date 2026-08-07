"""(T-C) part 2: layer analysis of Phi-bar : J/K -> W.

(A) Freeness basis: no element of DM(2) is self-negated (so K acts
    freely on cylinder cells of J, and the W4 route to type = BK for
    the cylinder quotient is available).
(B) The collapse locus: Phi does NOT preserve the collage layers —
    some cylinder (free-layer) cells of J land on stabilized
    (diagonal/antidiagonal) cells of W.  Census at levels 1 and 2:
    classify the image of every cylinder cell (d,a,t), t non-endpoint.
(C) Median closure of fibers — TESTED AND REFUTED: F does NOT
    commute with the coordinatewise ternary median (counterexamples
    below; already meet fails: maj(x)&maj(y) != maj(x&y)).  The
    fibers of Phi are therefore not median-closed by this mechanism,
    and the fiber-contraction strategy needs a different idea.
"""

import sys
from collage_type_lib import build, monotone_masks, NOT, gen

# ---------- DM(2) infrastructure ----------
N2, leq2, rho2 = build(2)
X, Y = gen(0, 2, N2), gen(1, 2, N2)
dm2 = monotone_masks(N2, leq2)
not2 = {m: NOT(m, N2, rho2) for m in dm2}
FULL2 = (1 << N2) - 1

# ---------- DM(1) ----------
N1, leq1, rho1 = build(1)
dm1 = monotone_masks(N1, leq1)
not1 = {m: NOT(m, N1, rho1) for m in dm1}
FULL1 = (1 << N1) - 1
assert len(dm1) == 6

# ---------- (A) no self-negated elements ----------
selfneg2 = [m for m in dm2 if not2[m] == m]
selfneg1 = [m for m in dm1 if not1[m] == m]
print("(A) self-negated in DM(1):", len(selfneg1), " in DM(2):", len(selfneg2))
assert not selfneg1 and not selfneg2

# ---------- (B) collapse-locus census ----------
def census(dm, notf, full):
    """Classify Phi-images of cylinder cells (d,a,t), t not endpoint."""
    diag = anti = free = 0
    diag_examples = []
    for t in dm:
        if t == 0 or t == full:
            continue
        nt = notf[t]
        for d in dm:
            b = d & nt
            for a in dm:
                na = notf[a]
                F1 = b | (a & t) | (d & a)
                F2 = b | (na & t) | (d & na)
                if F1 == F2:
                    diag += 1
                    if len(diag_examples) < 3:
                        diag_examples.append((d, a, t, F1))
                elif F1 == notf[F2]:
                    anti += 1
                else:
                    free += 1
    return diag, anti, free, diag_examples

d1, a1, f1, ex1 = census(dm1, not1, FULL1)
print(f"(B) level 1 cylinder cells: diag-image {d1}, anti-image {a1}, free-image {f1}")
print("    diagonal-image examples (d,a,t,image):", ex1)

d2c, a2c, f2c, ex2 = census(dm2, not2, FULL2)
tot2 = d2c + a2c + f2c
print(f"(B) level 2 cylinder cells: total {tot2}, diag-image {d2c}, anti-image {a2c}, free-image {f2c}")

# ---------- (C) does F commute with the ternary median?  (NO) ----------
# We only need the identity  F(med(d),med(a),med(t)) == med(F(d1,a1,t1),...)
# on generic generators; build with 9 variables is too big (2^18 points),
# so verify on DM(6) with a *substitution trick*: check the identity as a
# lattice-polynomial fact instead on all triples from DM(1)^3 per slot at
# level 1 (exhaustive finite check), and on 2000 random DM(2) triples.
def F_of(d, a, t, notf):
    return (d & notf[t]) | (a & t) | (d & a)

def med(u, v, w):
    return (u & v) | (v & w) | (w & u)

def check_med(dm, notf, triples):
    for (d1_, a1_, t1_), (d2_, a2_, t2_), (d3_, a3_, t3_) in triples:
        lhs = F_of(med(d1_, d2_, d3_), med(a1_, a2_, a3_), med(t1_, t2_, t3_), notf)
        rhs = med(F_of(d1_, a1_, t1_, notf), F_of(d2_, a2_, t2_, notf),
                  F_of(d3_, a3_, t3_, notf))
        if lhs != rhs:
            return (d1_, a1_, t1_, d2_, a2_, t2_, d3_, a3_, t3_)
    return None

# exhaustive at level 1: all triples of (d,a,t) in DM(1)^3 — 216^3 too big;
# instead all triples of cells from a full enumeration of DM(1)^3 pairs
import itertools, random
cells1 = [(d, a, t) for d in dm1 for a in dm1 for t in dm1]
random.seed(0)
sample = [tuple(random.choice(cells1) for _ in range(3)) for _ in range(20000)]
bad = check_med(dm1, not1, sample)
print("(C) med-commutation, 20000 random level-1 triples:", "FAIL" + str(bad) if bad else "pass")

cells2s = [(random.choice(dm2), random.choice(dm2), random.choice(dm2)) for _ in range(2000)]
sample2 = [tuple(random.choice(cells2s) for _ in range(3)) for _ in range(2000)]
bad2 = check_med(dm2, not2, sample2)
print("(C) med-commutation, 2000 random level-2 triples:", "FAIL" + str(bad2) if bad2 else "pass")

print("DONE")
