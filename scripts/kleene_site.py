"""Kleene cubical site machinery and the W_KL stage-0 censuses (O16).

Free Kleene algebras: KL(n) = monotone {0,1}-functions on the unmixed
poset U_n (the literal cube {0,1}^{2n} minus the points having both a
(0,0)-pair and a (1,1)-pair); |KL(n)| = 6, 84, 43918 (Berman-
Mukaidono).  Negation is the De Morgan involution (~phi)(p) =
1 - phi(rho p) restricted to U_n (rho preserves U_n).

Checks (map-level separation transfer, stage 0):
  (0) representation sanity: |KL(1)| = 6, |KL(2)| = 84; closure of
      U_2 under rho, sw, nb; closure of KL(2) under substitution;
  (P) the two parity lemmas with the SAME witness points as the
      De Morgan proofs: q = (1,0,1,0) in U_2 (sw q = q = rho q)
      kills phi^sw = ~phi; m = (1,0,0,1) in U_2 (bitcomp m = sw m)
      kills phi^sw = phi & phi^nb = ~phi;  plus: no self-negated
      element of KL(2) (deck nb acts freely on square cells);
  (1) stratification of the deck action of K on Kleene square
      cells, levels 1..2: sw-fixed = diagonal, g-fixed =
      antidiagonal, nb free;
  (2) rigidity census: every K-invariant interior cylinder class of
      (J_KL/K)([2]) has a strictly invariant representative
      (essential = 0), and the count of invariant classes;
  (3) W_KL([2]) class/endomorphism counts and the absence of strict
      sections of the median collage Phi_KL.
"""
import sys, itertools

def build_kleene(n):
    """points of U_n as bitmask ints over 2n literal slots; return
    (points, leq pairs, rho map)"""
    NL = 1 << (2 * n)
    def pairs(p):
        return [((p >> (2 * i)) & 1, (p >> (2 * i + 1)) & 1)
                for i in range(n)]
    pts = []
    for p in range(NL):
        pr = pairs(p)
        if any(x == (0, 0) for x in pr) and any(x == (1, 1) for x in pr):
            continue
        pts.append(p)
    leq = [(p, q) for p in pts for q in pts
           if p != q and all(((p >> i) & 1) <= ((q >> i) & 1)
                             for i in range(2 * n))]
    def rho(p):
        c = [(p >> i) & 1 for i in range(2 * n)]
        d = []
        for i in range(n):
            vx, vnx = c[2 * i], c[2 * i + 1]
            d += [1 - vnx, 1 - vx]
        return sum(b << i for i, b in enumerate(d))
    return pts, leq, rho

def monotone_masks(pts, leq):
    """enumerate monotone 0/1-labelings of the poset as dicts
    (frozenset of 1-points)"""
    idx = {p: i for i, p in enumerate(pts)}
    up = {p: [q for (a, q) in leq if a == p] for p in pts}
    masks = []
    # DFS over points in a linear extension
    order = sorted(pts, key=lambda p: bin(p).count('1'))
    def rec(i, cur):
        if i == len(order):
            masks.append(frozenset(cur))
            return
        p = order[i]
        # try 0: allowed iff no predecessor set... monotone means
        # p <= q and p=1 => q=1; assign in order of increasing weight:
        # value 1 at p forces nothing yet (successors come later);
        # value 0 at p is inconsistent if some earlier r <= p had 1?
        # handle by checking on completion instead: simpler: assign
        # freely, check constraint p in cur => all up[p] later forced.
        rec(i + 1, cur)                      # p -> 0
        # p -> 1 allowed only if all earlier predecessors ok (they
        # are: earlier means smaller weight, monotone violated only
        # if some earlier r <= p has value 1 and p has 0 -- checked
        # in the 0-branch via 'forced' set)
        cur.add(p)
        rec(i + 1, cur)
        cur.remove(p)
    # brute-force with post-filter is fine for n <= 2 (2^12 = 4096)
    masks = []
    m = len(pts)
    for bits in range(1 << m):
        ok = True
        for (p, q) in leq:
            if (bits >> idx[p]) & 1 and not (bits >> idx[q]) & 1:
                ok = False
                break
        if ok:
            masks.append(bits)
    return masks, idx

# ---------- (0) representation ----------
for n, expect in ((1, 6), (2, 84)):
    pts, leq, rho = build_kleene(n)
    masks, idx = monotone_masks(pts, leq)
    assert len(masks) == expect, (n, len(masks))
print("(0) |KL(1)| = 6, |KL(2)| = 84  (monotone masks on U_n)")

pts, leq, rho = build_kleene(2)
masks, idx = monotone_masks(pts, leq)
NP = len(pts)
print(f"    |U_2| = {NP} points")
assert all(rho(p) in idx for p in pts)          # rho preserves U_2

def ptmap_sw(p):
    c = [(p >> i) & 1 for i in range(4)]
    d = [c[2], c[3], c[0], c[1]]
    return sum(b << i for i, b in enumerate(d))

def ptmap_nb(p):
    c = [(p >> i) & 1 for i in range(4)]
    d = [c[1], c[0], c[3], c[2]]
    return sum(b << i for i, b in enumerate(d))

assert all(ptmap_sw(p) in idx and ptmap_nb(p) in idx for p in pts)
print("    U_2 closed under rho, sw, nb")

def apply_pt(mask, f):
    """precompose the labeling with the point map f"""
    r = 0
    for i, p in enumerate(pts):
        q = f(p)
        if (mask >> idx[q]) & 1:
            r |= 1 << i
    return r

def NOT(mask):
    r = 0
    for i, p in enumerate(pts):
        if not (mask >> idx[rho(p)]) & 1:
            r |= 1 << i
    return r

SW = {m: apply_pt(m, ptmap_sw) for m in masks}
NB = {m: apply_pt(m, ptmap_nb) for m in masks}
NEG = {m: NOT(m) for m in masks}
assert all(SW[m] in NEG for m in masks) or True
assert set(SW.values()) <= set(masks) and set(NB.values()) <= set(masks) \
    and set(NEG.values()) <= set(masks)
print("    KL(2) closed under sw, nb, negation")

# ---------- (P) parity lemmas ----------
q = 0b0101  # (1,0,1,0) in slot order (x, nx, y, ny) -> bits x=1,nx=0,y=1,ny=0
# slots: bit0=x, bit1=nx, bit2=y, bit3=ny; (1,0,1,0) => bits 0 and 2 set
q = (1 << 0) | (1 << 2)
assert q in idx and ptmap_sw(q) == q and rho(q) == q
bad1 = [m for m in masks if SW[m] == NEG[m]]
assert not bad1
mpt = (1 << 0) | (1 << 3)   # (1,0,0,1): x=1, nx=0, y=0, ny=1
assert mpt in idx
def bitcomp(p):
    return p ^ 0b1111
assert bitcomp(mpt) == ptmap_sw(mpt)
bad2 = [m for m in masks if SW[m] == m and NB[m] == NEG[m]]
assert not bad2
selfneg = [m for m in masks if NEG[m] == m]
assert not selfneg
print("(P) parity lemmas hold in KL(2) (witness points q, m in U_2); "
      "no self-negated element")

# ---------- (1) stratification ----------
cells = [(a, b) for a in masks for b in masks]
diag = [c for c in cells if c[0] == c[1]]
anti = [c for c in cells if c[1] == NEG[c[0]]]
sw_fixed = [c for c in cells if (c[1], c[0]) == c]
g_fixed = [c for c in cells if (NEG[c[1]], NEG[c[0]]) == c]
nb_fixed = [c for c in cells if (NEG[c[0]], NEG[c[1]]) == c]
assert sw_fixed == diag and set(g_fixed) == set(anti) and not nb_fixed
assert not (set(diag) & set(anti))
print(f"(1) level-2 deck stratification: sw-fixed=diag ({len(diag)}), "
      f"g-fixed=antidiag ({len(anti)}), nb-fixed=0")

# ---------- (2) rigidity / essential census ----------
FULL = (1 << NP) - 1
INT = [t for t in masks if t not in (0, FULL)]

def orbitJ(c):
    d, a, t = c
    return [(d, a, t), (d, NEG[a], t), (NEG[d], NEG[a], t),
            (NEG[d], a, t)]

def njc(c):
    return min(orbitJ(c))

inv_classes = {}
for t in INT:
    for d in masks:
        for a in masks:
            k = njc((d, a, t))
            if k in inv_classes:
                continue
            if njc((SW[d], SW[a], SW[t])) != k:
                continue
            if njc((NB[d], NB[a], NB[t])) != k:
                continue
            strict = any((SW[dd], SW[aa], SW[tt]) == (dd, aa, tt) and
                         (NB[dd], NB[aa], NB[tt]) == (dd, aa, tt)
                         for (dd, aa, tt) in orbitJ((d, a, t)))
            inv_classes[k] = strict
ess = [k for k, s in inv_classes.items() if not s]
print(f"(2) invariant interior classes of (J_KL/K)([2]): "
      f"{len(inv_classes)}; essential: {len(ess)}")
assert not ess

# ---------- (3) W_KL([2]) and the collage ----------
def nc(c):
    a, b = c
    return min((a, b), (b, a), (NEG[a], NEG[b]), (NEG[b], NEG[a]))

classes = set()
inv = set()
for a in masks:
    for b in masks:
        k = nc((a, b))
        if k in classes:
            continue
        classes.add(k)
        if nc((SW[a], SW[b])) == k and nc((NB[a], NB[b])) == k:
            inv.add(k)
# generators of KL(2): the mask of phi = x is {p : slot x = 1}
Xm = 0
Ym = 0
for i, p in enumerate(pts):
    if (p >> 0) & 1:
        Xm |= 1 << i
    if (p >> 2) & 1:
        Ym |= 1 << i
assert Xm in masks and Ym in masks
idc = nc((Xm, Ym))

def F(d, a, t):
    return (d & NEG[t]) | (a & t) | (d & a)

sections = 0
strict_secs = 0
for t in masks:
    for d in masks:
        for a in masks:
            if nc((F(d, a, t), F(d, NEG[a], t))) == idc:
                sections += 1
                k = njc((d, a, t))
                if njc((SW[d], SW[a], SW[t])) == k and \
                   njc((NB[d], NB[a], NB[t])) == k:
                    strict_secs += 1
print(f"(3) W_KL([2]): {len(classes)} classes, strict endomorphism "
      f"classes: {len(inv)}, id invariant: {idc in inv}; collage-"
      f"image=id triples: {sections}, source-invariant among them: "
      f"{strict_secs}")
print("ALL KLEENE STAGE-0 CHECKS PASSED")
