"""O27: the five-chain atom is a square.

Claim: T = <z>, z = (u^v^w, u^v, u^(v|w)), satisfies
  T(k) = {(p^q, p, p|q) : p,q in D(k)}   and the map
  cube^2 -> T, (p,q) |-> (p^q, p, p|q) is an ISOMORPHISM
(injectivity = cancellation in distributive lattices).
Verify at levels 0..4:  (a) the two cell sets coincide,
(b) the map is injective, (c) counts |T(k)| = |D(k)|^2.

General principle behind it (canonical coordinates + sections):
for an atom <z>, z in D(n)^j, the ker-respecting coordinates are
the monotone g: {0,1}^n -> {0,1} constant on the fibers of the
vertex map zhat and monotone w.r.t. the transitive closure of
realized comparability of fibers.  If the fiber poset admits a
monotone transversal s, then e := s o (fiber map) is a monotone
idempotent with z o e = z and fiber collapse, and <z> is iso to
<e> = a retract of cube^n, hence W-regular for every localizer.
Second sweep: check the TRANSVERSAL property for the fiber
partitions of ALL monotone vertex maps on {0,1}^3 (all cell
kernels at n = 3), i.e. all "monotone partitions".
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F
from collections import defaultdict

def to_int(t):
    n = 0
    for i, b in enumerate(t): n |= b << i
    return n

def ints(k):
    pts, D = F(k)
    return pts, [to_int(f) for f in D]

# ---- part 1: T = <z> equals the square ----
for k in range(0, 5):
    pts, D = ints(k)
    T = set()
    for s in itertools.product(D, repeat=3):
        T.add((s[0] & s[1] & s[2], s[0] & s[1], s[0] & (s[1] | s[2])))
    sq = set()
    inj = {}
    ok_inj = True
    for p in D:
        for q in D:
            c = (p & q, p, p | q)
            if c in inj and inj[c] != (p, q): ok_inj = False
            inj[c] = (p, q)
            sq.add(c)
    print(f"level {k}: |T| = {len(T)}, |D|^2 = {len(D)**2}, "
          f"T == square-image: {T == sq}, injective: {ok_inj}")
print()

# ---- part 2: transversal sweep over all cell kernels at n = 3 ----
# fiber partitions of monotone maps {0,1}^3 -> {0,1}^j  =
# partitions P of the 8 points such that the transitive closure of
# "exists a<=b crossing" is antisymmetric on blocks AND the
# canonical monotone block-functions separate the blocks (which
# for a genuine cell kernel is automatic; we enumerate partitions
# that ARE kernels: P is a cell kernel iff the canonical map with
# all admissible g's has fiber partition exactly P).
pts = list(range(8))
def leq(x, y): return (x & y) == x

def closure_order(blocks):
    # realized comparability between blocks; return matrix or None
    nb = len(blocks)
    le = [[False]*nb for _ in range(nb)]
    for i in range(nb): le[i][i] = True
    for i, Bi in enumerate(blocks):
        for j, Bj in enumerate(blocks):
            if i != j and any(leq(a, b) for a in Bi for b in Bj):
                le[i][j] = True
    # transitive closure
    for m in range(nb):
        for i in range(nb):
            if le[i][m]:
                for j in range(nb):
                    if le[m][j]: le[i][j] = True
    for i in range(nb):
        for j in range(nb):
            if i != j and le[i][j] and le[j][i]:
                return None  # not antisymmetric: not a kernel
    return le

def is_kernel(blocks, le):
    # canonical g's = indicators of up-sets of the block poset;
    # they separate blocks iff block poset is a poset (yes) --
    # distinct blocks differ in some up-set indicator, and each
    # indicator is monotone as a point function iff for x <= y
    # (points), block(x) <= block(y) in the closure -- which holds
    # by construction.  So P is a kernel iff antisymmetric.  BUT
    # must also check: pointwise monotone: x <= y implies
    # le[bl(x)][bl(y)] (true: realized comparability).
    return True

def transversal(blocks, le):
    nb = len(blocks)
    # choose s(i) in blocks[i], monotone w.r.t. le
    order = sorted(range(nb), key=lambda i: sum(le[j][i] for j in range(nb)))
    chosen = {}
    def bt(pos):
        if pos == nb: return True
        i = order[pos]
        for y in blocks[i]:
            good = True
            for j, yj in chosen.items():
                if le[j][i] and not leq(yj, y): good = False; break
                if le[i][j] and not leq(y, yj): good = False; break
            if good:
                chosen[i] = y
                if bt(pos + 1): return True
                del chosen[i]
        return False
    return bt(0)

def partitions(seq):
    if not seq:
        yield []
        return
    x, rest = seq[0], seq[1:]
    for part in partitions(rest):
        for i in range(len(part)):
            yield part[:i] + [part[i] + [x]] + part[i+1:]
        yield part + [[x]]

total = kernels = failed = 0
bad = []
for part in partitions(pts):
    total += 1
    blocks = [tuple(b) for b in part]
    le = closure_order(blocks)
    if le is None: continue
    kernels += 1
    if not transversal(blocks, le):
        failed += 1
        if len(bad) < 5: bad.append(blocks)
print(f"partitions of 8 points: {total}, cell kernels (antisym): {kernels}, "
      f"WITHOUT monotone transversal: {failed}")
for b in bad: print("  counterexample:", b)
