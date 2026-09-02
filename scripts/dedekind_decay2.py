"""O28 stage 2b: decay probe with STANDARD open boxes.

Structural finding: sorted positions are chain positions, so a box
whose prescribed part contains the chain part of its codomain
creates no new sorted cells (the engine box creates none).  New
sorted cells come from the standard boxes
  (m into cube^2) box delta^0,  m = boundary minus one face,
whose free part contains chain positions.  Enumerate box data
over W (bottom 2-cell + three compatible side cylinders), adjoin
the sorted-position filler cells, and test whether the 14 old
H2-classes of Ch(W) become boundaries.
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

sortedW = {q: [c for c in W.level(q)
               if act(c, sort_sub(q), q, q) == c] for q in range(K+1)}
def chain_subs(q, k):
    _, Dk = F(k)
    if q == 0: return [()]
    return [c for c in itertools.product(Dk, repeat=q)
            if all(comparable(a,b) for a,b in itertools.combinations(c,2))]
ChW = {}
for k in range(K + 1):
    cells = set()
    for q in range(K + 1):
        for s in sortedW[q]:
            for u in chain_subs(q, k):
                cells.add(act(s, u, q, k) if q > 0 else
                          W.cls(k, restrict(s, tuple(), 2, 0, k)))
    ChW[k] = sorted(cells)

# box shapes: m_f = boundary of cube^2 minus face f, f in
# {(x1=0),(x1=1),(x2=0),(x2=1)}; prescribed part of the box over
# cube^3 (coords c = (c1,c2,c3)):
#   P_f = { (c1,c2) in m_f } u { c3 = 0 }
# membership of a level-q position (c1,c2) in m_f: the pair
# factors through the boundary-minus-f: i.e. (c1,c2) is an
# instance of one of the three kept faces: c1=0 / c1=1 / c2=0 /
# c2=1 minus f: position in face (x1=e): c1 = const e; etc.
ZERO = {q: tuple(0 for _ in F(q)[0]) for q in range(K+2)}
ONE  = {q: tuple(1 for _ in F(q)[0]) for q in range(K+2)}
def in_face(c12, face, q):
    c1, c2 = c12
    if face == 'x1=0': return c1 == ZERO[q]
    if face == 'x1=1': return c1 == ONE[q]
    if face == 'x2=0': return c2 == ZERO[q]
    if face == 'x2=1': return c2 == ONE[q]
FACES = ['x1=0', 'x1=1', 'x2=0', 'x2=1']

def in_m(c12, f, q):
    return any(in_face(c12, g, q) for g in FACES if g != f)

def inP(c, f, q):
    return in_m((c[0], c[1]), f, q) or c[2] == ZERO[q]

# box data: bottom w0 in W(2); side cylinders h_g in W(2) for the
# three faces g != f, compatibility:
#  h_g . (t,0) = w0 . (face g)   [cylinder starts at bottom edge]
#  corner edges match: for adjacent faces g, g' sharing a vertex v:
#  h_g . (vertex-side, t) = h_g' . (vertex-side, t)
# encode: face g of cube^2 as a 1-cell map [1]->[2]:
tvar = tuple(p[0] for p in F(1)[0])
FMAP = {'x1=0': (ZERO[1], tvar), 'x1=1': (ONE[1], tvar),
        'x2=0': (tvar, ZERO[1]), 'x2=1': (tvar, ONE[1])}
def face_cell(x, g):   # w0 restricted to face g: level-1 class
    return act(x, FMAP[g], 2, 1)
# side cylinder h_g: a level-2 class, coordinates (edge-param s, t):
# bottom edge h.(s,0) must equal face_cell(w0, g); the vertical
# edges h.(0,t), h.(1,t) are the corner paths.
def cyl_bottom(h): return act(h, (tvar, ZERO[1]), 2, 1)
def cyl_v0(h): return act(h, (ZERO[1], tvar), 2, 1)
def cyl_v1(h): return act(h, (ONE[1], tvar), 2, 1)

# corners of face g: which ends correspond to which cube vertex:
# face x1=e: param s = x2: ends s=0 -> vertex (e,0), s=1 -> (e,1)
# face x2=e: param s = x1: ends s=0 -> (0,e), s=1 -> (1,e)
def face_ends(g):
    if g == 'x1=0': return (('0','0'), ('0','1'))
    if g == 'x1=1': return (('1','0'), ('1','1'))
    if g == 'x2=0': return (('0','0'), ('1','0'))
    if g == 'x2=1': return (('0','1'), ('1','1'))

import time
t0 = time.time()
W2 = W.level(2)
boxes = []
CAP = 400
for f in FACES:
    kept = [g for g in FACES if g != f]
    for w0 in W2:
        # enumerate side triples with compatibility
        cand = {g: [h for h in W2
                    if cyl_bottom(h) == face_cell(w0, g)]
                for g in kept}
        for hs in itertools.product(*(cand[g] for g in kept)):
            H = dict(zip(kept, hs))
            # corner matching: vertical edges at shared vertices
            ok = True
            corner = {}
            for g in kept:
                e0, e1 = face_ends(g)
                for endv, vert in ((cyl_v0(H[g]), e0),
                                  (cyl_v1(H[g]), e1)):
                    if vert in corner and corner[vert] != endv:
                        ok = False; break
                    corner[vert] = endv
                if not ok: break
            if ok:
                boxes.append((f, w0, H))
            if len(boxes) >= CAP: break
        if len(boxes) >= CAP: break
    if len(boxes) >= CAP: break
print(f"boxes enumerated: {len(boxes)} (cap {CAP}), "
      f"{time.time()-t0:.1f}s", flush=True)

def o_chain(q): return [o_stat_t(j, q) for j in range(0, q + 2)]
def sorted_positions(q):
    return list(itertools.product(o_chain(q), repeat=3))
def coface_T(i, q):
    f = tuple(x if x < i else x + 1 for x in range(q))
    idx = []
    for ii in range(1, q + 1):
        ks = [kk for kk in range(q) if f[kk] >= ii]
        idx.append(min(ks) if ks else q)
    return tuple(o_stat_t(kk, q - 1) for kk in idx)
def pos_face(c, i, q):
    Tf = coface_T(i, q)
    return tuple(compose(comp, Tf, q, q - 1) for comp in c)

def b_val(box, c, q):
    """prescribed value of box datum at position c (level q)"""
    f, w0, H = box
    c1, c2, c3 = c
    if c3 == ZERO[q]:
        return act(w0, (c1, c2), 2, q)
    # in m_f x cyl: find a kept face containing (c1,c2)
    for g in [gg for gg in FACES if gg != f]:
        if in_face((c1, c2), g, q):
            # position within the cylinder h_g: (s, t) = ?
            if g in ('x1=0', 'x1=1'): s = c2
            else: s = c1
            return act(H[g], (s, c3), 2, q)
    return None

# assemble enriched complex
b1i = {('o', c): i for i, c in enumerate(ChW[1])}
b2i = {}
for c in ChW[2]: b2i[('o', c)] = len(b2i)
newsyms2 = set(); newsyms3 = set()
for bi, box in enumerate(boxes):
    f = box[0]
    for c in sorted_positions(2):
        if not inP(c, f, 2): newsyms2.add((bi, c))
    for c in sorted_positions(3):
        if not inP(c, f, 3): newsyms3.add((bi, c))
for s in sorted(newsyms2): b2i[('n', s)] = len(b2i)
b3i = {}
for c in ChW[3]: b3i[('o', c)] = len(b3i)
for s in sorted(newsyms3): b3i[('n', s)] = len(b3i)
print(f"enriched sizes: C2 = {len(b2i)}, C3 = {len(b3i)}", flush=True)

def face_of(sym, i, q):
    kind, v = sym
    if kind == 'o':
        return ('o', act(v, coface_T(i, q), q, q - 1))
    bi, c = v
    box = boxes[bi]
    fc = pos_face(c, i, q)
    if inP(fc, box[0], q - 1):
        return ('o', b_val(box, fc, q - 1))
    return ('n', (bi, fc))

def rank2f(cols):
    rank = 0; pivots = []
    for c in cols:
        cur = c
        for p in pivots: cur = min(cur, cur ^ p)
        if cur: pivots.append(cur); rank += 1
    return rank, pivots

d3cols = []
for sym in b3i:
    v = 0
    for i in range(4):
        fs = face_of(sym, i, 3)
        v ^= 1 << b2i[fs]
    d3cols.append(v)
r3, piv3 = rank2f(d3cols)
print(f"rank d3 (enriched) = {r3}", flush=True)

# old cycles (Z2 of old complex) survivors mod enriched d3
oldsyms = [s for s in b2i if s[0] == 'o']
oidx = {s: i for i, s in enumerate(oldsyms)}
pivots = {}; kernel = []
for s in oldsyms:
    col = 0
    for i in range(3):
        col ^= 1 << b1i[face_of(s, i, 2)]
    comb = 1 << oidx[s]
    cur, curc = col, comb
    while cur:
        low = cur & -cur
        if low in pivots:
            pc, pcc = pivots[low]
            cur ^= pc; curc ^= pcc
        else:
            pivots[low] = (cur, curc); curc = 0; break
    if curc: kernel.append(curc)
surv = list(piv3); survivors = 0
for kv in kernel:
    v = 0
    for i, s in enumerate(oldsyms):
        if (kv >> i) & 1: v |= 1 << b2i[s]
    cur = v
    for p in surv: cur = min(cur, cur ^ p)
    if cur: surv.append(cur); survivors += 1
print(f"old cycle classes surviving: {survivors} (was 14; "
      f"old Z2 dim {len(kernel)})", flush=True)
