"""O27 stage 15: the attachment subobject A_n = Ch_n u P_n.

A_n <= cube^n: union of the chain cells and the cells factoring
through a lower cube ([k], k < n).  For the chain approximation
lemma the induction needs A_n -> cube^n to be a type-trivial
cofibration, i.e. A_n contractible.
Checks at n = 3:
 (i)  cell counts of Ch_3, P_3, A_3 at levels <= 3;
 (ii) is A_3 closed under the wedge cone?  (if yes: strictly
      contractible and we are done at n=3);
 (iii) if not: which cells escape, and is the escape absorbed
      (cone image still in A_3)?
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose

def to_int(t):
    n = 0
    for i, b in enumerate(t): n |= b << i
    return n

D = {k: [to_int(f) for f in F(k)[1]] for k in range(0, 4)}
def leq(a, b): return (a & b) == a
def chainv(c): return all(leq(a,b) or leq(b,a)
                          for a,b in itertools.combinations(c,2))

def comp1(p, v, l, m):
    out = 0
    for x in range(1 << m):
        idx = 0
        for i in range(l):
            idx |= ((v[i] >> x) & 1) << i
        if (p >> idx) & 1: out |= 1 << x
    return out

n = 3
for k in range(1, 4):
    cells = list(itertools.product(D[k], repeat=n))
    ch = set(c for c in cells if chainv(c))
    # P_3 at level k: cells factoring as v <> w, v: [j]->[3], j<3,
    # w: [k]->[j]
    P = set()
    for j in range(0, n):
        for v in itertools.product(D[j], repeat=n):
            for w in itertools.product(D[k], repeat=j):
                P.add(tuple(comp1(c, w, j, k) for c in v))
    A = ch | P
    print(f"n=3, level {k}: cells {len(cells)}, Ch {len(ch)}, "
          f"P {len(P)}, A {len(A)}, complement {len(cells)-len(A)}",
          flush=True)
    # cone closure of A at this level: c |-> c ^ t needs level k+1
    # representation; test pointwise closure instead: for c in A,
    # is c^t's structure in A at level k+1?  Approximate: check
    # for k <= 2 by direct computation at level k+1.
    if k <= 2:
        # embed: c in A(level k) -> c' = (c_i ^ t) at level k+1
        pts1, _ = F(k + 1)
        def lift_and(c):
            # variables x1..xk, t: component c_i(x) & t
            out = []
            for comp in c:
                v = 0
                for i, p in enumerate(pts1):
                    x = p[:k]; tbit = p[k]
                    idx = 0
                    for ii in range(k):
                        idx |= x[ii] << ii
                    if ((comp >> idx) & 1) and tbit: v |= 1 << i
                out.append(v)
            return tuple(out)
        cellsk1 = None
        chk1 = None
        Pk1 = set()
        for j in range(0, n):
            for v in itertools.product(D[j], repeat=n):
                for w in itertools.product(D[k+1], repeat=j):
                    Pk1.add(tuple(comp1(c, w, j, k+1) for c in v))
        escapes = 0
        for c in A:
            lc = lift_and(c)
            if not (chainv(lc) or lc in Pk1):
                escapes += 1
        print(f"  cone-lift escapes A at level {k+1}: {escapes}",
              flush=True)

# ---- stage 2: identify escapees; test or-cone; homology ----
print("--- stage 2 ---", flush=True)
k = 2
cells2 = list(itertools.product(D[2], repeat=3))
ch2 = set(c for c in cells2 if chainv(c))
P2 = set(cells2)   # all level-2 cells factor through [2]
A2 = ch2 | P2      # = all
pts3, _ = F(3)
def lift_op(c, op):
    """c at level 2 -> (c_i op t) at level 3 (t = 3rd var)"""
    out = []
    for comp in c:
        v = 0
        for i, p in enumerate(pts3):
            x = p[:2]; tbit = p[2]
            idx = x[0] | (x[1] << 1)
            b = (comp >> idx) & 1
            val = (b & tbit) if op == 'and' else (b | tbit)
            if val: v |= 1 << i
        out.append(v)
    return tuple(out)

# recompute P3 at level 3
P3 = set()
for j in range(0, 3):
    for v in itertools.product(D[j], repeat=3):
        for w in itertools.product(D[3], repeat=j):
            P3.add(tuple(comp1(c, w, j, 3) for c in v))
A3_3 = set(c for c in itertools.product(D[3], repeat=3)
           if chainv(c)) | P3

esc_and = [c for c in A2 if lift_op(c, 'and') not in A3_3]
esc_or = [c for c in A2 if lift_op(c, 'or') not in A3_3]
print(f"level-2 cells escaping wedge-cone: {len(esc_and)}, "
      f"escaping join-cone: {len(esc_or)}")
u2 = to_int(tuple(p[0] for p in F(2)[0]))
v2 = to_int(tuple(p[1] for p in F(2)[0]))
names = {0:'0', u2:'a', v2:'b', u2&v2:'a&b', u2|v2:'a|b',
         (1<<4)-1:'1'}
for c in esc_and:
    print("  and-escape:", tuple(names.get(x, x) for x in c))
for c in esc_or[:8]:
    print("  or-escape:", tuple(names.get(x, x) for x in c))

# ---- homology of A3 (chains to level 3) ----
import itertools as it
levels = {}
for kk in range(0, 4):
    cells = list(it.product(D[kk], repeat=3))
    Pk = set()
    for j in range(0, 3):
        for v in it.product(D[j], repeat=3):
            for w in it.product(D[kk], repeat=j):
                Pk.add(tuple(comp1(c, w, j, kk) for c in v))
    Ak = set(c for c in cells if chainv(c)) | Pk
    levels[kk] = sorted(Ak)
print("A3 levels:", [len(levels[kk]) for kk in range(4)], flush=True)

def coface_tuple(i, q):
    """delta^i: [q-1]->[q]-ish for the simplicial chain cx used in
    tri_homology: the coface as a (q)-tuple over F(q-1)?? use the
    same convention as dedekind_triangulate: simplices at level q =
    cells at level q, faces via the q+1 ordinal cofaces T(delta^i)"""
    # faces of a level-q simplex = restrictions along T(delta_i):
    # [q-1] -> [q]
    def ordinal_face(i, q):
        # delta^i skips i: {0..q-1}->{0..q}
        return tuple(x if x < i else x + 1 for x in range(q))
    f = ordinal_face(i, q)
    idx = []
    for ii in range(1, q + 1):
        ks = [kk for kk in range(q) if f[kk] >= ii]
        idx.append(min(ks) if ks else q)
    def o_stat_int(j, m):
        if j <= 0: return (1 << (1 << m)) - 1
        if j > m: return 0
        out = 0
        for pt in range(1 << m):
            if bin(pt).count('1') >= j: out |= 1 << pt
        return out
    return tuple(o_stat_int(kk, q - 1) for kk in idx)

def rank2(cols):
    rank = 0; pivots = []
    for c in cols:
        cur = c
        for p in pivots:
            cur = min(cur, cur ^ p)
        if cur: pivots.append(cur); rank += 1
    return rank

ind = {q: {c: i for i, c in enumerate(levels[q])} for q in range(4)}
bettis = []
ranks = {}
for q in range(1, 4):
    cols = []
    for cell in levels[q]:
        vvec = 0
        for i in range(q + 1):
            Tf = coface_tuple(i, q)
            fc = tuple(comp1(comp, Tf, q, q - 1) for comp in cell)
            vvec ^= 1 << ind[q - 1][fc]
        cols.append(vvec)
    ranks[q] = rank2(cols)
b0 = len(levels[0]) - ranks[1]
b1 = len(levels[1]) - ranks[1] - ranks[2]
b2 = len(levels[2]) - ranks[2] - ranks[3]
print(f"A3 F2-Betti (deg 0..2): {b0}, {b1}, {b2}", flush=True)
