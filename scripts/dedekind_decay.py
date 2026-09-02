"""O28 stage 2: the decay probe.

Enrich the chain complex of Ch(W), W the monotone dunce hat, by
the sorted-position filler cells of the ENGINE boxes
  b_x = (Ch_2 into cube^2) box delta^0,  datum
  b_x(u) = x . (u1^u3, u2^u3)
for every level-2 class x of W.  New simplices: (x, c) for sorted
positions c of cube^3 not in the prescribed part P (= comparable
(c1,c2), or c3 = 0), levels 2 and 3; faces via T(delta^i):
prescribed positions evaluate through b_x (giving Ch(W)-cells),
free positions give new symbols.  Question: do the 14 old
H2-classes of Ch(W) become boundaries?  (A chain map to the true
stage-1 complex exists, so death here implies death there.)
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, restrict, Quotient
from collections import defaultdict

K = 3
W = Quotient(2, [(1, ((0,0), (0,1)), ((0,1), (0,0))),
                 (1, ((0,1), (0,1)), ((0,1), (1,1)))], K)

def o_stat_t(j, m):
    pts, _ = F(m)
    if j <= 0: return tuple(1 for _ in pts)
    if j > m: return tuple(0 for _ in pts)
    return tuple(1 if sum(p) >= j else 0 for p in pts)

def sort_sub(q): return tuple(o_stat_t(j, q) for j in range(1, q+1))
def act(cls_, u, j, k): return W.cls(k, restrict(cls_, u, 2, j, k))

def leq_t(a, b): return all(x <= y for x, y in zip(a, b))
def comparable(a, b): return leq_t(a, b) or leq_t(b, a)

# sorted W classes (= Ch(W) cells) at levels 0..3
sortedW = {}
for q in range(K + 1):
    srt = sort_sub(q)
    sortedW[q] = [c for c in W.level(q) if act(c, srt, q, q) == c]
# NOTE: Ch(W) cells = chain instances; section 166 verified these
# = the counit values; at our truncation use sorted classes and
# their instances: recompute Ch(W) as in dedekind_chW.py
def chain_subs(q, k):
    _, Dk = F(k)
    if q == 0: return [()]
    out = []
    for c in itertools.product(Dk, repeat=q):
        if all(comparable(a, b) for a, b in itertools.combinations(c, 2)):
            out.append(c)
    return out
ChW = {}
for k in range(K + 1):
    cells = set()
    for q in range(K + 1):
        for s in sortedW[q]:
            u0 = tuple() if q == 0 else None
            for u in chain_subs(q, k):
                cells.add(act(s, u, q, k) if q > 0 else
                          W.cls(k, restrict(s, tuple(), 2, 0, k)))
    ChW[k] = sorted(cells)
print("Ch(W) levels:", [len(ChW[k]) for k in range(K+1)], flush=True)

# sorted positions of cube^3 at level q: triples over the o-chain
def o_chain_elts(q):
    return [o_stat_t(j, q) for j in range(0, q + 2)]  # 1, o1..oq, 0
def sorted_positions(q):
    ch = o_chain_elts(q)
    return list(itertools.product(ch, repeat=3))
def inP(c):
    zero = c[2] == tuple(0 for _ in c[2])
    return comparable(c[0], c[1]) or zero

def coface_T(i, q):
    f = tuple(x if x < i else x + 1 for x in range(q))
    idx = []
    for ii in range(1, q + 1):
        ks = [kk for kk in range(q) if f[kk] >= ii]
        idx.append(min(ks) if ks else q)
    return tuple(o_stat_t(kk, q - 1) for kk in idx)

def pos_face(c, i, q):
    """position c (triple over F(q)) restricted along T(delta^i)"""
    Tf = coface_T(i, q)
    return tuple(compose(comp, Tf, q, q - 1) for comp in c)

def b_val(x, c, q):
    """prescribed value: x . (c1^c3, c2^c3) as W-class at level q"""
    u = (tuple(a & b for a, b in zip(c[0], c[2])),
         tuple(a & b for a, b in zip(c[1], c[2])))
    return act(x, u, 2, q)

X2 = W.level(2)   # all 26 level-2 classes
new2 = []; new3 = []
for x in X2:
    for c in sorted_positions(2):
        if not inP(c): new2.append((x, c))
    for c in sorted_positions(3):
        if not inP(c): new3.append((x, c))
print(f"new sorted cells: level2 {len(new2)}, level3 {len(new3)}",
      flush=True)

# bases
b1 = {('o', c): i for i, c in enumerate(ChW[1])}
b2 = {}
for c in ChW[2]: b2[('o', c)] = len(b2)
for s in new2: b2[('n', s)] = len(b2)
b3 = {}
for c in ChW[3]: b3[('o', c)] = len(b3)
for s in new3: b3[('n', s)] = len(b3)

def face2(sym, i):
    """face of a level-2 basis element -> level-1 old cell"""
    kind, v = sym
    if kind == 'o':
        return ('o', act(v, coface_T(i, 2), 2, 1))
    x, c = v
    fc = pos_face(c, i, 2)
    # level-1 positions are always in P
    return ('o', b_val(x, fc, 1))

def face3(sym, i):
    kind, v = sym
    if kind == 'o':
        return ('o', act(v, coface_T(i, 3), 3, 2))
    x, c = v
    fc = pos_face(c, i, 3)
    if inP(fc):
        return ('o', b_val(x, fc, 2))
    return ('n', (x, fc))

def rank2f(cols):
    rank = 0; pivots = []
    for c in cols:
        cur = c
        for p in pivots: cur = min(cur, cur ^ p)
        if cur: pivots.append(cur); rank += 1
    return rank, pivots

# old complex ranks (for reference): from section 166: H2 = 14
# enriched: d2 columns
d2cols = []
for sym in b2:
    v = 0
    for i in range(3):
        v ^= 1 << b1[face2(sym, i)]
    d2cols.append(v)
r2, _ = rank2f(d2cols)
d3cols = []
for sym in b3:
    v = 0
    for i in range(4):
        v ^= 1 << b2[face3(sym, i)]
    d3cols.append(v)
r3, piv3 = rank2f(d3cols)
h2 = len(b2) - r2 - r3
print(f"enriched: |C2| = {len(b2)}, |C3| = {len(b3)}, "
      f"rank d2 = {r2}, rank d3 = {r3}, H2 = {h2}", flush=True)

# do the OLD 14 classes die?  compute old cycle space Z2old inside
# enriched C2 (old cells only): old d2 restricted
oldd2 = {sym: col for sym, col in zip(b2, d2cols)
         if sym[0] == 'o'}
# old cycles: kernel of d2 on old subspace; old d3 image; then check
# dim of (Z2old + im d3)/im d3 vs old H2
# kernel basis of old d2 via row-reduction over F2:
oldsyms = [s for s in b2 if s[0] == 'o']
oidx = {s: i for i, s in enumerate(oldsyms)}
import copy
# build matrix columns with tracking to get kernel
pivots = {}; kernel = []
for s in oldsyms:
    col = 0
    for i in range(3):
        col ^= 1 << b1[face2(s, i)]
    comb = 1 << oidx[s]
    cur, curc = col, comb
    changed = True
    while cur:
        low = cur & -cur
        if low in pivots:
            pc, pcc = pivots[low]
            cur ^= pc; curc ^= pcc
        else:
            pivots[low] = (cur, curc); cur = 0; curc = 0
    if curc:
        kernel.append(curc)
print(f"old Z2 dim = {len(kernel)}", flush=True)
# express old kernel vectors in enriched C2 coordinates and reduce
# against im(d3): count how many survive
surv_pivots = list(piv3)
survivors = 0
for kv in kernel:
    # kv is over old-index space; map to enriched index space
    v = 0
    for i, s in enumerate(oldsyms):
        if (kv >> i) & 1: v |= 1 << b2[s]
    cur = v
    for p in surv_pivots: cur = min(cur, cur ^ p)
    if cur:
        surv_pivots.append(cur); survivors += 1
print(f"old cycle classes NOT killed by enriched boundaries: "
      f"{survivors}  (old H2 was 14)", flush=True)
