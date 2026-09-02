"""O28 stage 2i: explicit prism transport of the H2 classes.

Theory: Theta = (shell graph homotopy K: id ~ phi) followed by
(strict homotopy psi: phi ~ const), phi = the sort endo of W.
Simplicial prism operators transported through Theta must bound
every 2-cycle of Sing(W) inside Sing(R1 W) (R1 = W + the one
shell filler L).  decay5 reported the shell wad contributes no
boundaries -- contradicting this.  Here we build the prism
chains explicitly and check the boundary identities cell by
cell, to locate the discrepancy.

Complex: SORTED cells only (simplices of Sing).  Level-3 new
generators: free sorted positions (o-chain 4-tuples) of the
shell codomain cube^4.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, restrict, Quotient

K = 3
def proj(k, i):
    pts, _ = F(k)
    return tuple(p[i] for p in pts)
def const(k, e):
    pts, _ = F(k)
    return tuple(e for _ in pts)
def pmeet(*xs):
    out = xs[0]
    for x in xs[1:]: out = tuple(a & b for a, b in zip(out, x))
    return out
def pjoin(*xs):
    out = xs[0]
    for x in xs[1:]: out = tuple(a | b for a, b in zip(out, x))
    return out

A1c, B1c = (const(1,0), proj(1,0)), (proj(1,0), const(1,0))
A2c, B2c = (proj(1,0), proj(1,0)), (proj(1,0), const(1,1))
W = Quotient(2, [(1, A1c, B1c), (1, A2c, B2c)], K)

def o_stat_t(j, m):
    pts, _ = F(m)
    if j <= 0: return tuple(1 for _ in pts)
    if j > m: return tuple(0 for _ in pts)
    return tuple(1 if sum(p) >= j else 0 for p in pts)
def sort_sub(q): return tuple(o_stat_t(j, q) for j in range(1, q+1))
def act(cls_, u, j, k): return W.cls(k, restrict(cls_, u, 2, j, k))
sortedW = {q: [c for c in W.level(q)
               if act(c, sort_sub(q), q, q) == c] for q in range(K+1)}
print("sorted cells per level:",
      [len(sortedW[q]) for q in range(K+1)], flush=True)

def o_chain(q): return [o_stat_t(j, q) for j in range(0, q + 2)]
def coface_T(i, q):
    f = tuple(x if x < i else x + 1 for x in range(q))
    idx = []
    for ii in range(1, q + 1):
        ks = [kk for kk in range(q) if f[kk] >= ii]
        idx.append(min(ks) if ks else q)
    return tuple(o_stat_t(kk, q - 1) for kk in idx)

# ---- Sing(W) complex (sorted cells, T-faces) ----
S1i = {c: i for i, c in enumerate(sortedW[1])}
S2i = {c: i for i, c in enumerate(sortedW[2])}
S3i = {c: i for i, c in enumerate(sortedW[3])}
piv = {}; kernel = []
for c in sortedW[2]:
    col = 0
    for i in range(3):
        col ^= 1 << S1i[act(c, coface_T(i, 2), 2, 1)]
    comb = 1 << S2i[c]
    cur, curc = col, comb
    while cur:
        low = cur & -cur
        if low in piv:
            pc, pcc = piv[low]; cur ^= pc; curc ^= pcc
        else:
            piv[low] = (cur, curc); curc = 0; break
    if curc: kernel.append(curc)
d3span = []
def insert(sp, v):
    cur = v
    for p in sp: cur = min(cur, cur ^ p)
    if cur: sp.append(cur); return True
    return False
for c in sortedW[3]:
    v = 0
    for i in range(4):
        v ^= 1 << S2i[act(c, coface_T(i, 3), 3, 2)]
    insert(d3span, v)
surv = []
snap = list(d3span)
for kv in kernel:
    cur = kv and kv  # kernel vectors are already over S2 bits
    for p in snap: cur = min(cur, cur ^ p)
    if cur: snap.append(cur); surv.append(kv)
print(f"Sing(W): Z2 dim {len(kernel)}, d3 rank {len(d3span)}, "
      f"H2 survivors {len(surv)}", flush=True)

# ---- shell box machinery ----
p3, q3, r3 = proj(3,0), proj(3,1), proj(3,2)
PR = {'a2': (pmeet(p3,r3), pmeet(p3,r3)),
      'b2': (pmeet(p3,r3), r3),
      'a1': (const(3,0), pmeet(p3,r3)),
      'b1': (const(3,0), pmeet(p3,r3)),
      'n0': (pmeet(p3,r3), pmeet(q3,r3)),
      'n1': (pmeet(p3,q3,r3), pmeet(r3, pjoin(p3,q3)))}
ZE = {q: const(q,0) for q in range(K+1)}
ON = {q: const(q,1) for q in range(K+1)}
def square_fact(c123, q):
    c1, c2, c3 = c123
    if c1 == c2:     return ('a2', (c1, c3))
    if c2 == ON[q]:  return ('b2', (c1, c3))
    if c1 == ZE[q]:  return ('a1', (c2, c3))
    if c2 == ZE[q]:  return ('b1', (c1, c3))
    if c3 == ZE[q]:  return ('n0', (c1, c2))
    if c3 == ON[q]:  return ('n1', (c1, c2))
    return None
def inP(c, q):
    return c[3] == ZE[q] or square_fact(c[:3], q) is not None
def b_val(c, q):
    if c[3] == ZE[q] and square_fact(c[:3], q) is None:
        return W.cls(q, (const(q,0), const(q,0)))
    n, z = square_fact(c[:3], q)
    sub = (z[0], z[1], c[3])
    return W.cls(q, tuple(compose(comp, sub, 3, q) for comp in PR[n]))
def pos_face(c, i, q):
    Tf = coface_T(i, q)
    return tuple(compose(comp, Tf, q, q - 1) for comp in c)

# generator resolution at levels 2, 3: ('o', cell) or ('n', pos)
def resolve(c, q):
    if inP(c, q): return ('o', b_val(c, q))
    return ('n', c)

# ---- the maps ----
def phi(x, q):   # sort endo of W
    g1, g2 = x
    return W.cls(q, (pmeet(g1, g2), pjoin(g1, g2)))
def psi(s, z, q):   # strict homotopy phi ~ const: H = (w|(u&v), u|v|w)
    g1, g2 = s
    return W.cls(q, (pjoin(z, pmeet(g1, g2)), pjoin(g1, g2, z)))
def theta1(s, z, q):   # shell-wad cell K.(g1,g2,z) = L.(g1,g2,z,1)
    g1, g2 = s
    return resolve((g1, g2, z, ON[q]), q)

TSIG = {0: (o_stat_t(2,3), o_stat_t(3,3)),
        1: (o_stat_t(1,3), o_stat_t(3,3)),
        2: (o_stat_t(1,3), o_stat_t(2,3))}
def eta(x, j):   # degenerate 3-cell x.T(sigma_j)
    return act(x, TSIG[j], 2, 3)
ZETA = {j: o_stat_t(j + 1, 3) for j in (0, 1, 2)}

# sanity: K ends
gen = W.cls(2, (proj(2,0), proj(2,1)))
end0 = b_val((proj(2,0), proj(2,1), const(2,0), ON[2]), 2)
end1 = b_val((proj(2,0), proj(2,1), const(2,1), ON[2]), 2)
print("K ends: r=0 ->", end0 == gen,
      "(iota); r=1 ->", end1 == phi(gen, 2), "(h = phi)", flush=True)

# ---- prism identity check for the K-prism, one sorted 2-cell ----
def bdry3(sym, q=3):
    """faces of a level-3 generator as list of level-2 syms"""
    kind, v = sym
    out = []
    for i in range(4):
        if kind == 'o':
            out.append(('o', act(v, coface_T(i, 3), 3, 2)))
        else:
            fc = pos_face(v, i, 3)
            out.append(resolve(fc, 2))
    return out

def check_prism(x, verbose=False):
    """F2: does d(P1 x) + P1(dx) + i0x + i1x = 0 in R1-syms?"""
    from collections import Counter
    cnt = Counter()
    for j in (0, 1, 2):
        s = eta(x, j)
        sym = theta1(s, ZETA[j], 3)
        for f in bdry3(sym):
            cnt[f] ^= 1 if False else 1
    # accumulate mod 2 properly
    cnt = Counter()
    for j in (0, 1, 2):
        sym = theta1(eta(x, j), ZETA[j], 3)
        for f in bdry3(sym):
            cnt[f] += 1
    # P1(dx): faces of x, prism at level 2: P(y) for 1-cell y:
    # 2-simplices (eta_j y, zeta_j), j = 0,1
    TS1 = {0: (o_stat_t(2,2),), 1: (o_stat_t(1,2),)}
    Z1 = {0: o_stat_t(1,2), 1: o_stat_t(2,2)}
    for i in range(3):
        y = act(x, coface_T(i, 2), 2, 1)
        for j in (0, 1):
            s2 = act(y, TS1[j], 1, 2)
            g1, g2 = s2
            cnt[resolve((g1, g2, Z1[j], ON[2]), 2)] += 1
    # ends
    cnt[('o', x)] += 1                       # i0 = id end
    cnt[('o', phi(x, 2))] += 1               # i1 = phi end
    bad = {k: v for k, v in cnt.items() if v % 2}
    if verbose and bad:
        for k, v in list(bad.items())[:12]:
            print("   leftover:", v % 2, k[0],
                  (k[1] if k[0] == 'n' else 'W-cell'), flush=True)
    return len(bad)

nbad = 0
for x in sortedW[2]:
    b = check_prism(x)
    if b: nbad += 1
print(f"K-prism identity: {nbad}/{len(sortedW[2])} sorted 2-cells "
      f"FAIL", flush=True)
if nbad:
    for x in sortedW[2]:
        if check_prism(x):
            print("first failing cell:", flush=True)
            check_prism(x, verbose=True)
            break

# ---- psi-prism identity ----
def check_prism2(x):
    from collections import Counter
    cnt = Counter()
    for j in (0, 1, 2):
        s = eta(x, j)
        w3 = psi(s, ZETA[j], 3)
        for i in range(4):
            cnt[act(w3, coface_T(i, 3), 3, 2)] += 1
    TS1 = {0: (o_stat_t(2,2),), 1: (o_stat_t(1,2),)}
    Z1 = {0: o_stat_t(1,2), 1: o_stat_t(2,2)}
    for i in range(3):
        y = act(x, coface_T(i, 2), 2, 1)
        for j in (0, 1):
            s2 = act(y, TS1[j], 1, 2)
            cnt[psi(s2, Z1[j], 2)] += 1
    cnt[phi(x, 2)] += 1
    cnt[W.cls(2, (const(2,1), const(2,1)))] += 1  # const v11 end
    return sum(1 for v in cnt.values() if v % 2)

nbad2 = sum(1 for x in sortedW[2] if check_prism2(x))
print(f"psi-prism identity: {nbad2}/{len(sortedW[2])} FAIL", flush=True)
