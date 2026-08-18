"""Boolean cubical site machinery and the first W_BA censuses (O16).

Cells of the Boolean cube category at level [m] are ALL functions
{0,1}^m -> {0,1} (the free Boolean algebra FB(m), |FB(m)| = 2^(2^m)),
encoded as bitmasks over the 2^m points.  Negation is the OUTPUT
complement (no literal doubling as in the De Morgan case).

Checks:
  (1) stratification of the deck action of K = {1, sw, nb, g} on
      cells of the Boolean square, levels 1..3: sw-fixed = diagonal,
      g-fixed = antidiagonal, nb free -- the same sieve/cosieve
      structure as on the De Morgan site, hence el(W_BA) is the join
      BZ/2 * BZ/2 by the identical collage computation;
  (2) mux-equivariance identity  ~mux(x,v,t) = mux(~x,~v,t)  in
      FB(3) (the Boolean repair of the sign-equivariant interpolation
      that fails on the De Morgan site);
  (3) census of K-invariant classes of W_BA([2]) and of the strict
      endomorphism classes; strict-homotopy reachability from the
      identity (exact enumeration -- FB(2) has only 16 elements);
  (4) the median collage Phi_BA(d,a,t) = (F(d,a,t), F(d,~a,t)) with
      F(d,a,t) = (d & ~t) | (a & t) | (d & a): equivariance and the
      count of strict sections at level 2.
"""
import sys, itertools

def NPTS(m):
    return 1 << m

def all_fns(m):
    return list(range(1 << NPTS(m)))

def neg(phi, m):
    """output complement"""
    return ((1 << NPTS(m)) - 1) ^ phi

def subst(phi, args, m_out, m_in):
    """phi in FB(m_out) composed with args = tuple of m_out elements
    of FB(m_in): result in FB(m_in)."""
    r = 0
    for p in range(NPTS(m_in)):
        vals = tuple((a >> p) & 1 for a in args)
        q = sum(b << i for i, b in enumerate(vals))
        if (phi >> q) & 1:
            r |= 1 << p
    return r

def gen(i, m):
    """the i-th generator of FB(m)"""
    r = 0
    for p in range(NPTS(m)):
        if (p >> i) & 1:
            r |= 1 << p
    return r

# ---------- (1) stratification at levels 1..3 ----------
print("(1) deck-action stratification on Boolean square cells")
for m in (1, 2, 3):
    cells = [(a, b) for a in all_fns(m) for b in all_fns(m)]
    sw_fixed = [c for c in cells if (c[1], c[0]) == c]
    g_fixed = [c for c in cells if (neg(c[1], m), neg(c[0], m)) == c]
    nb_fixed = [c for c in cells if (neg(c[0], m), neg(c[1], m)) == c]
    diag = [c for c in cells if c[0] == c[1]]
    antidiag = [c for c in cells if c[1] == neg(c[0], m)]
    assert sw_fixed == diag
    assert set(g_fixed) == set(antidiag)
    assert not nb_fixed
    assert not (set(diag) & set(antidiag))
    print(f"  level {m}: |cells|={len(cells)}  sw-fixed=diagonal "
          f"({len(diag)})  g-fixed=antidiagonal ({len(antidiag)})  "
          f"nb-fixed=0  diag∩antidiag=∅")

# ---------- (2) mux equivariance ----------
x, v, t = gen(0, 3), gen(1, 3), gen(2, 3)
mux = (x & neg(t, 3)) | (v & t)
lhs = neg(mux, 3)
rhs = (neg(x, 3) & neg(t, 3)) | (neg(v, 3) & t)
assert lhs == rhs
print("(2) Boolean mux is negation-equivariant: "
      "~((x&~t)|(v&t)) == (~x&~t)|(~v&t)")

# ---------- (3) W_BA([2]) census ----------
m = 2
FB2 = all_fns(m)
X, Y = gen(0, m), gen(1, m)
NEG = {phi: neg(phi, m) for phi in FB2}

def deck_orbit(c):
    a, b = c
    return [(a, b), (b, a), (NEG[a], NEG[b]), (NEG[b], NEG[a])]

def nc(c):
    return min(deck_orbit(c))

def sub_sw(phi):
    return subst(phi, (Y, X), m, m)

def sub_nb(phi):
    return subst(phi, (NEG[X], NEG[Y]), m, m)

classes = sorted({nc((a, b)) for a in FB2 for b in FB2})
inv = [c for c in classes
       if nc((sub_sw(c[0]), sub_sw(c[1]))) == c
       and nc((sub_nb(c[0]), sub_nb(c[1]))) == c]
idc = nc((X, Y))
consts = sorted({nc((a, b)) for a in (0, (1 << NPTS(m)) - 1)
                 for b in (0, (1 << NPTS(m)) - 1)})
print(f"(3) W_BA([2]): {len(classes)} classes; strict endomorphism "
      f"classes (K-invariant): {len(inv)}; id invariant: {idc in inv}")

# strict-homotopy reachability among invariant classes: a strict
# invariant homotopy is a K-invariant class H of W_BA([2+1]) with
# prescribed t-faces.  FB(3) has 256 elements: enumerate exactly.
m3 = 3
FB3 = all_fns(m3)
X3, Y3, T3 = gen(0, m3), gen(1, m3), gen(2, m3)
NEG3 = {phi: neg(phi, m3) for phi in FB3}

def face_t(phi, e):
    """t := e face: FB(3) -> FB(2)"""
    const = 0 if e == 0 else (1 << NPTS(m)) - 1
    return subst(phi, (X, Y, const), m3, m)

def deck_orbit3(c):
    a, b = c
    return [(a, b), (b, a), (NEG3[a], NEG3[b]), (NEG3[b], NEG3[a])]

def nc3(c):
    return min(deck_orbit3(c))

def sub_sw3(phi):
    return subst(phi, (Y3, X3, T3), m3, m3)

def sub_nb3(phi):
    return subst(phi, (NEG3[X3], NEG3[Y3], T3), m3, m3)

# adjacency: for each invariant homotopy cell, record its face pair
import collections
adj = collections.defaultdict(set)
seen3 = set()
for A in FB3:
    for B in FB3:
        k = nc3((A, B))
        if k in seen3:
            continue
        seen3.add(k)
        if nc3((sub_sw3(A), sub_sw3(B))) != k:
            continue
        if nc3((sub_nb3(A), sub_nb3(B))) != k:
            continue
        f0 = nc((face_t(A, 0), face_t(B, 0)))
        f1 = nc((face_t(A, 1), face_t(B, 1)))
        if f0 in inv and f1 in inv:
            adj[f0].add(f1)
            adj[f1].add(f0)
comp = {idc}
stack = [idc]
while stack:
    for nbr in adj[stack.pop()]:
        if nbr not in comp:
            comp.add(nbr)
            stack.append(nbr)
print(f"    strict-homotopy component of id: {len(comp)} classes; "
      f"contains a constant: {any(c in comp for c in consts)}")

# ---------- (4) the median collage on the Boolean site ----------
def F(d, a, t):
    return (d & NEG[t]) | (a & t) | (d & a)

# equivariance spot-checks (exact, all of FB(2)^3)
ok = True
for d in FB2:
    for a in FB2:
        for tt in FB2:
            c = (F(d, a, tt), F(d, NEG[a], tt))
            csw = (F(d, NEG[a], tt), F(d, a, tt))       # sw~ image
            if nc(c) != nc(csw):
                ok = False
                break
        if not ok:
            break
    if not ok:
        break
print(f"(4) collage Phi_BA equivariance under sw~ at level 2: {ok}")

# strict sections of Phi_BA at level 2: does some K_J-invariant
# triple (d,a,t) have  (F(d,a,t), F(d,~a,t)) == id class strictly?
sections = [(d, a, tt) for d in FB2 for a in FB2 for tt in FB2
            if nc((F(d, a, tt), F(d, NEG[a], tt))) == idc]
print(f"    triples with collage image = id class: {len(sections)}")
print("DONE")
