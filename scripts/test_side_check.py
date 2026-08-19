"""Test side of the non-equivariant retract transfer (O18, section 81).

Two separate questions.

(A) EQUIVARIANT case (R1, R2).  If l is a D-equivariant retract of
cube^n (D-maps j, r with r j = id), then the self-dual mux
      H_t(x)_i := F(x_i, (j r x)_i, t) = (x_i & ~t) | ((jrx)_i & t)
                                        | (x_i & (jrx)_i)
is again D-equivariant (F commutes with permutations coordinatewise and
~F(a,b,t) = F(~a,~b,t)), with H_0 = id and H_1 = j r.  So l is a
D-equivariant DEFORMATION retract, the homotopy descends to the
quotient, and j : W' = l/D -> W is a homotopy equivalence in EVERY
structure -- test and type alike.  Hence a witness for Q transfers to W
by 2-out-of-3, with no pullback and no test-side computation.
This script verifies the mux identities and the equivariance mechanically.

(B) NON-EQUIVARIANT case (R3, R4).  Only a quotient-level retraction
r : W -> W' with r j = id exists (a twisted end class).  Then j_* is a
split mono on H_*(el -), and j is a test equivalence iff j_* is onto in
every degree (both sides are simply connected when Q is
reflection-generated).  We test this in as many degrees as the reduced
vertex model allows.
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build
from nr_sharp import VC, homology, induced_rank

# ---------- (A) the mux identities ----------
def F(a, b, t): return (a & (1 - t)) | (b & t) | (a & b)
ok = all(F(a, b, 0) == a and F(a, b, 1) == b and
         (1 - F(a, b, t)) == F(1 - a, 1 - b, t)
         for a in (0, 1) for b in (0, 1) for t in (0, 1))
print(f"(A) mux: F(.,.,0)=a, F(.,.,1)=b, ~F(a,b,t)=F(~a,~b,t) -> {ok}")
print("    => a D-equivariant retraction r of cube^n onto l upgrades to a")
print("       D-equivariant deformation retraction, so l/D -> W is a")
print("       homotopy equivalence in test AND type; transfer is formal.")

# ---------- (B) higher-degree test for the twisted cases ----------
n = 4
ELEMS, idx, ID, NE, MUL, INV, ACT = build(n)
NV = 1 << n
REFL = []
for a in range(NE):
    p, s = ELEMS[a]
    seen = [False]*n; ok2 = a != ID
    for i in range(n):
        if seen[i]: continue
        sg = s[i]; j = p[i]; seen[i] = True
        while j != i:
            seen[j] = True; sg ^= s[j]; j = p[j]
        if sg & 1: ok2 = False
    REFL.append(ok2)
def close(g):
    S = {ID}; dq = deque([ID])
    while dq:
        x = dq.popleft()
        for a in g:
            y = MUL[x][a]
            if y not in S: S.add(y); dq.append(y)
    return frozenset(S)
RES = [
    ("R1", [idx[((0, 1, 3, 2), (1, 1, 0, 0))], idx[((1, 0, 2, 3), (0, 0, 1, 1))],
            idx[((2, 3, 0, 1), (0, 0, 0, 0))]]),
    ("R3", [idx[((0, 1, 3, 2), (1, 1, 0, 0))], idx[((1, 2, 0, 3), (0, 0, 0, 0))],
            idx[((0, 2, 1, 3), (1, 1, 1, 1))]]),
    ("R4", [idx[((1, 0, 2, 3), (0, 0, 0, 0))], idx[((0, 1, 2, 3), (1, 1, 0, 0))],
            idx[((2, 3, 0, 1), (0, 0, 0, 0))]]),
]
print()
print("(B) is j : l/N_l -> W a test equivalence?  (reduced vertex model)")
for name, gens in RES:
    D = sorted(close(gens))
    stab = {v: frozenset(a for a in D if ACT[a][v] == v) for v in range(NV)}
    U = [v for v in range(NV) if not any(stab[v] < stab[w] for w in range(NV))]
    loci = {}
    for a in D:
        if REFL[a]:
            L = frozenset(v for v in range(NV) if ACT[a][v] == v)
            loci[L] = 1
    maximal = [sorted(L) for L in loci if not any(L < L2 for L2 in loci)]
    print(f"  {name}: |D|={len(D)} |V|={NV} |U|={len(U)}")
    top = 5 if len(U) <= 8 else 4
    A = VC(list(range(NV)), [ACT[a] for a in D], 4, NV=NV)
    HA = homology(A, 4)
    Ared = VC(U, [ACT[a] for a in D], top, NV=NV)
    HAr = homology(Ared, top)
    print(f"      H_*(el W): full {[HA[k] for k in (1,2,3)]}, reduced "
          f"{[HAr[k] for k in range(1, top)]}")
    seen = set()
    for Ls in maximal:
        key = min(tuple(sorted(ACT[g][v] for v in Ls)) for g in D)
        if key in seen: continue
        seen.add(key)
        Nl = [a for a in D if {ACT[a][v] for v in Ls} == set(Ls)]
        if not set(Ls) <= set(U):
            print(f"      stratum |l|={len(Ls)}: not inside U, skipped")
            continue
        S = VC(Ls, [ACT[a] for a in Nl], top, NV=NV)
        HS = homology(S, top)
        r = {k: induced_rank(S, Ared, k, lambda c, m: c)
             for k in range(1, top)}
        iso = all(r[k] == HAr[k] == HS[k] for k in range(1, top))
        print(f"      stratum |l|={len(Ls)} |N_l|={len(Nl)}: "
              f"H_*(el l/N)={[HS[k] for k in range(1, top)]} "
              f"j_* ranks={[r[k] for k in range(1, top)]} -> "
              f"{'ISO in all computed degrees' if iso else 'NOT surjective somewhere'}")
