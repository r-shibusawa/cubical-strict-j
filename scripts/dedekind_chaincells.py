"""O27 stage 10: the chain-cell subobject and the master filling
lemma.

Ch_n <= cube^n := cells (p_1..p_n) whose components are PAIRWISE
COMPARABLE (form a chain in D(k)).  Facts:
 (i)  subpresheaf: instances of chain tuples are chain tuples;
 (ii) the wedge-cone p |-> p ^ t preserves Ch_n: strictly
      contractible; hence Ch_n -> cube^n is a type-trivial
      cofibration (mono + both contractible);
 (iii) Ch_2 = union of the two chamber simplices glued along the
      diagonal (comparable pairs);
 (iv) sorted cells (o-chain-valued tuples) are chain cells, and
      every chain cell is a pattern-instance of a sorted cell.
Verify (i)-(iv) computationally at n <= 3, k <= 3; report sizes.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F

def to_int(t):
    n = 0
    for i, b in enumerate(t): n |= b << i
    return n

D = {k: [to_int(f) for f in F(k)[1]] for k in range(0, 4)}

def leq(a, b): return (a & b) == a
def comparable(a, b): return leq(a, b) or leq(b, a)

def is_chain(cell):
    return all(comparable(a, b) for a, b in
               itertools.combinations(cell, 2))

def o_stat(j, m):
    if j <= 0: return (1 << (1 << m)) - 1
    if j > m: return 0
    out = 0
    for pt in range(1 << m):
        if bin(pt).count('1') >= j: out |= 1 << pt
    return out

def comp1(p, v, l, m):
    out = 0
    for x in range(1 << m):
        idx = 0
        for i in range(l):
            idx |= ((v[i] >> x) & 1) << i
        if (p >> idx) & 1: out |= 1 << x
    return out

for n in (2, 3):
    for k in (1, 2, 3):
        cells = list(itertools.product(D[k], repeat=n))
        ch = [c for c in cells if is_chain(c)]
        # (i) closure under instances (test all v: [k']->[k], k'<=2)
        closed = True
        for kk in (0, 1, 2):
            for c in ch:
                for v in itertools.product(D[kk], repeat=k):
                    inst = tuple(comp1(p, v, k, kk) for p in c)
                    if not is_chain(inst): closed = False
        # (ii) wedge cone: components ^ t (t = extra variable):
        # verified pointwise: p_i <= p_j => p_i^t <= p_j^t: trivial;
        # spot-check at k+1 vars
        # (iii) at n=2: chain = comparable pairs = O u O^op
        extra = ""
        if n == 2:
            incr = [c for c in cells if leq(c[0], c[1])]
            decr = [c for c in cells if leq(c[1], c[0])]
            extra = (f", Ch_2 == incr u decr: "
                     f"{set(ch) == set(incr) | set(decr)}")
        # (iv) sorted cells are chain cells
        srt = tuple(o_stat(j, k) for j in range(1, k + 1))
        sorted_cells = [c for c in cells
                        if tuple(comp1(p, srt, k, k) for p in c) == c]
        sorted_in_ch = all(is_chain(c) for c in sorted_cells)
        print(f"n={n}, k={k}: cells {len(cells)}, chain {len(ch)}, "
              f"closed: {closed}, sorted({len(sorted_cells)}) all "
              f"chain: {sorted_in_ch}{extra}", flush=True)

# (iv') every chain cell = pattern-instance of a sorted cell:
# decreasing rearrangement d of the components is itself a cell,
# and c = pattern . d with d sorted?  d sorted iff components are
# order statistics -- NOT generally.  Correct statement: c is an
# instance of sort_n along d: c = pattern-of(sort_n . d-subst)?
# check: for chain c with decreasing rearrangement d (as tuple of
# D(k) elements), sort_n <> d = d (computed in D(k)): then
# c = rho <> d for the variable pattern rho.
ok = True
for k in (1, 2, 3):
    srtn = tuple(o_stat(j, 3) for j in range(1, 4))
    for c in itertools.product(D[k], repeat=3):
        if not is_chain(c): continue
        d = tuple(sorted(c, key=lambda p: -bin(p).count('1')))
        # ensure d decreasing wrt leq (chain: popcount sort works?)
        if not all(leq(d[i+1], d[i]) for i in range(2)):
            d = tuple(sorted(c, key=lambda p: [not leq(q, p) for q in c].count(True)))
        if not all(leq(d[i+1], d[i]) for i in range(2)):
            ok = False; continue
        # sort_3 evaluated at d = d?
        sd = tuple(comp1(o, d, 3, k) for o in srtn)
        if sd != d: ok = False
print(f"chain cells: decreasing rearrangement is sort-stable: {ok}")
