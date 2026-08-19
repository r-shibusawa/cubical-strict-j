"""F2 Betti assembly for el(cube^n/H) via the master collage formula
(O20):  el = hocolim( el(Sigma/H) <- (el Sigma)_{hH} -> BH ).

Generic machinery: cochain complexes over F2 (sparse), chain maps,
double-mapping-cylinder assembly; bar complexes of finite groups with
induced maps along homomorphisms.

Validation: the Klein quotient at n = 2:
  el(W_K) = hocolim( L u L  <-  BK u BK  ->  BK )
with L = B(Z/2), maps = the two quotient characters; expected
H^k dims = those of the join BZ/2 * BZ/2: 1,0,0,1,2,3,... (k>=0).
"""
import itertools as it

# ---------- sparse F2 linear algebra ----------
def rank_sparse(rows):
    """rows: list of python ints (bitsets).  Returns rank."""
    piv = {}
    r = 0
    for v in rows:
        while v:
            b = v.bit_length() - 1
            if b in piv:
                v ^= piv[b]
            else:
                piv[b] = v
                r += 1
                break
    return r

# ---------- cochain complexes ----------
class Cx:
    """cochain complex over F2 in degrees 0..D: dims[k], and
    differentials d[k]: C^k -> C^{k+1} given as list-of-columns
    (column j = bitset over C^{k+1} coordinates)."""
    def __init__(self, dims, d):
        self.dims = dims          # list length D+1
        self.d = d                # list length D: d[k] = list of ints
    def betti(self):
        D = len(self.dims) - 1
        ranks = []
        for k in range(D):
            ranks.append(rank_sparse(list(self.d[k])))
        out = []
        for k in range(D + 1):
            rk_in = ranks[k - 1] if k >= 1 else 0
            rk_out = ranks[k] if k < D else 0   # NOTE: top degree truncated
            out.append(self.dims[k] - rk_in - rk_out)
        return out  # last entry unreliable (truncation)

class Map:
    """chain map f: A -> B, degreewise columns: f[k][j] = bitset in B^k
    for the j-th basis vector of A^k."""
    def __init__(self, cols):
        self.cols = cols

def pushout_cx(A, B, C, f, g):
    """Cochain model of the double mapping cylinder (homotopy pushout)
    of  A <-f- C -g-> B:
      X^k = A^k + B^k + C^{k-1},
      d(a, b, c) = (dA a, dB b, f*(a) + g*(b) + dC c),
    where f, g are the COCHAIN maps C^*(A) -> C^*(C), C^*(B) -> C^*(C)
    induced by the space-level legs.  (Homotopy pullback of cochains.)
    Returns (Cx, projections pA, pB as cochain maps X -> is not needed;
    we return the complex only, plus offset data for building further
    maps.)"""
    D_ = len(C.dims) - 1
    dims = [A.dims[k] + B.dims[k] + (C.dims[k - 1] if k >= 1 else 0)
            for k in range(D_ + 1)]
    d = []
    for k in range(D_):
        oA1, oB1 = A.dims[k + 1], B.dims[k + 1]
        cols = []
        for j2 in range(A.dims[k]):
            v = A.d[k][j2]
            v |= (f.cols[k][j2] << (oA1 + oB1))
            cols.append(v)
        for j2 in range(B.dims[k]):
            v = B.d[k][j2] << oA1
            v |= (g.cols[k][j2] << (oA1 + oB1))
            cols.append(v)
        if k >= 1:
            for j2 in range(C.dims[k - 1]):
                v = (C.d[k - 1][j2] << (oA1 + oB1))
                cols.append(v)
        d.append(cols)
    return Cx(dims, d)

def hocolim_betti(A, B, C, f, g, D):
    """Betti of the double mapping cylinder of A <-f- C -g-> B via the
    Mayer-Vietoris exact sequence:
      -> H^{k-1}(C) -> H^k(X) -> H^k(A)+H^k(B) -(f*-g*)-> H^k(C) ->
    dim H^k(X) = dim ker(delta_k) + dim coker(delta_{k-1}) where
    delta_k: H^k(A)+H^k(B) -> H^k(C).  We compute delta on cohomology:
    need cocycle bases and the induced maps."""
    # cocycle/coboundary bases per complex
    def coho_basis(Z):
        D_ = len(Z.dims) - 1
        bases = []
        for k in range(D_ + 1):
            # cocycles: kernel of d[k] (if k < D_), else all (unreliable)
            if k < D_:
                # kernel via elimination on columns
                piv = {}
                ker = []
                for j in range(Z.dims[k]):
                    v = Z.d[k][j]
                    w = 1 << j          # track combination
                    while v:
                        b = v.bit_length() - 1
                        if b in piv:
                            v ^= piv[b][0]; w ^= piv[b][1]
                        else:
                            piv[b] = (v, w)
                            w = None
                            break
                    if w is not None:
                        ker.append(w)   # combination = a cocycle
            else:
                ker = [1 << j for j in range(Z.dims[k])]
            # coboundaries: image of d[k-1] as bitsets over C^k coords
            img = list(Z.d[k-1]) if k >= 1 else []
            bases.append((ker, img))
        return bases
    bA, bB, bC = coho_basis(A), coho_basis(B), coho_basis(C)

    def expand(comb, cols_dim):
        """comb: bitset over basis indices of C^k (a cocycle as a
        combination of standard basis vectors) -> the actual cochain
        bitset IS the comb itself (cocycles tracked in standard
        coordinates)."""
        return comb

    out = []
    prev_coker = 0
    for k in range(len(A.dims)):
        # H^k dims and delta_k rank
        def hdim(b, Z, k):
            ker, img = b[k]
            # dim H = #independent cocycles mod coboundaries
            piv = {}
            r_img = 0
            for v in img:
                vv = v
                while vv:
                    t = vv.bit_length() - 1
                    if t in piv: vv ^= piv[t]
                    else:
                        piv[t] = vv; r_img += 1; break
            r_tot = r_img
            reps = []
            for v in ker:
                vv = v
                while vv:
                    t = vv.bit_length() - 1
                    if t in piv: vv ^= piv[t]
                    else:
                        piv[t] = vv; r_tot += 1; reps.append(v); break
            return reps, piv, img
        repsA, _, imgA = hdim(bA, A, k)
        repsB, _, imgB = hdim(bB, B, k)
        # delta on reps: f*(a) - g*(b) in H^k(C): map cochains, reduce
        # mod coboundaries of C and mod... compute rank of the images
        # of (repsA via f*, repsB via g*) in H^k(C):
        piv = {}
        for v in bC[k][1]:   # coboundaries of C first
            vv = v
            while vv:
                t = vv.bit_length() - 1
                if t in piv: vv ^= piv[t]
                else: piv[t] = vv; break
        rank_delta = 0
        def push(vec):
            nonlocal rank_delta
            vv = vec
            while vv:
                t = vv.bit_length() - 1
                if t in piv: vv ^= piv[t]
                else:
                    piv[t] = vv; rank_delta += 1; break
        def apply_map(m, comb, srcdim):
            out = 0
            j = 0
            c = comb
            while c:
                if c & 1:
                    out ^= m.cols[k][j]
                c >>= 1; j += 1
            return out
        for a in repsA:
            push(apply_map(f, a, A.dims[k]))
        for b_ in repsB:
            push(apply_map(g, b_, B.dims[k]))
        hA, hB = len(repsA), len(repsB)
        # dim H^k(C) needed for coker
        repsC, _, _ = hdim(bC, C, k)
        hC = len(repsC)
        hX = (hA + hB - rank_delta) + prev_coker
        out.append(hX)
        prev_coker = hC - rank_delta
    return out

# ---------- bar complexes ----------
def bar_complex(G, mul, D):
    """G: list of elements (index 0 = identity NOT required);
    mul: dict (i,j)->k.  C^q = functions on (G*)^q? Use normalized:
    functions on tuples of NON-identity elements (normalized bar):
    much smaller.  d f(g1..g_{q+1}) = f(g2..) + sum f(..g_i g_{i+1}..)
    + f(..g_q); terms with identity products drop (normalized)."""
    idg = None
    for i in range(len(G)):
        if all(mul[(i, j)] == j for j in range(len(G))):
            idg = i; break
    nz = [i for i in range(len(G)) if i != idg]
    idx = {g: t for t, g in enumerate(nz)}
    m = len(nz)
    tuples = {0: [()]}
    for q in range(1, D + 1):
        tuples[q] = [t + (g,) for t in tuples[q - 1] for g in nz]
    tindex = {q: {t: i for i, t in enumerate(tuples[q])}
              for q in range(D + 1)}
    dims = [len(tuples[q]) for q in range(D + 1)]
    d = []
    for q in range(D):
        cols = [0] * dims[q]
        # d^T easier: for each (q+1)-tuple, its boundary hits q-tuples;
        # we need columns over C^{q}: column j (a q-cochain basis dual
        # to tuple t) maps to sum over (q+1)-tuples whose boundary
        # contains t.  Build via rows then transpose implicitly:
        for i1, tt in enumerate(tuples[q + 1]):
            faces = []
            faces.append(tt[1:])
            for pos in range(q):
                p = mul[(tt[pos], tt[pos + 1])]
                if p == idg:
                    continue
                faces.append(tt[:pos] + (p,) + tt[pos + 2:])
            faces.append(tt[:-1])
            acc = {}
            for fc in faces:
                acc[fc] = acc.get(fc, 0) ^ 1
            for fc, c in acc.items():
                if c:
                    cols[tindex[q][fc]] ^= (1 << i1)
        d.append(cols)
    return Cx(dims, d), nz, tuples, tindex

def induced_map(Gsrc, mulsrc, Gtgt, multgt, hom, barS, barT, D):
    """cochain map C^*(B Gtgt) -> C^*(B Gsrc) along hom: Gsrc -> Gtgt
    (contravariant: restriction).  barS/barT = (Cx, nz, tuples, tindex).
    Returns Map with cols[k][j] = image bitset."""
    CxT, nzT, tupT, tidxT = barT
    CxS, nzS, tupS, tidxS = barS
    # identity of target
    idT = None
    for i in range(len(Gtgt)):
        if all(multgt[(i, j)] == j for j in range(len(Gtgt))):
            idT = i; break
    cols = []
    for k in range(D + 1):
        c = [0] * CxT.dims[k]
        for i_s, ts in enumerate(tupS[k]):
            imgt = tuple(hom[g] for g in ts)
            if any(g == idT for g in imgt):
                continue           # normalized: drops
            c[tidxT[k][imgt]] |= (1 << i_s)
        cols.append(c)
    return Map(cols)

# ---------- validation: the Klein quotient ----------
if __name__ == "__main__":
    D = 6
    # groups: K = Z/2 x Z/2 as indices 0..3 (0 = id, 1 = sw, 2 = nb, 3 = g)
    K = list(range(4))
    mulK = {}
    for a in range(4):
        for b in range(4):
            mulK[(a, b)] = a ^ b
    Z2 = [0, 1]
    mul2 = {(a, b): a ^ b for a in range(2) for b in range(2)}
    barK = bar_complex(K, mulK, D)
    bar2 = bar_complex(Z2, mul2, D)
    # sanity: Betti of BK, BZ/2
    print("H^*(BZ/2):", bar2[0].betti()[:D])
    print("H^*(BK):  ", barK[0].betti()[:D])
    # el(W_K): A = L u L (two BZ/2's), B = BK, C = BK u BK
    # maps: f: C -> A = (quotient K -> K/<sw>) u (K -> K/<g>)
    #       g: C -> B = id u id
    def direct_sum_cx(X, Y):
        D_ = len(X.dims) - 1
        dims = [X.dims[k] + Y.dims[k] for k in range(D_ + 1)]
        d = []
        for k in range(D_):
            cols = [X.d[k][j] for j in range(X.dims[k])] + \
                   [Y.d[k][j] << X.dims[k + 1] for j in range(Y.dims[k])]
            d.append(cols)
        return Cx(dims, d)
    def direct_sum_map(f1, f2, XA, XB, YA, YB):
        cols = []
        for k in range(len(f1.cols)):
            c = [f1.cols[k][j] for j in range(len(f1.cols[k]))] + \
                [f2.cols[k][j] << XA.dims[k] for j in range(len(f2.cols[k]))]
            cols.append(c)
        return Map(cols)
    A = direct_sum_cx(bar2[0], bar2[0])
    Bc = barK[0]
    C = direct_sum_cx(barK[0], barK[0])
    # hom K -> Z/2 killing sw=1: q1: 0,1,2,3 -> 0,0,1,1
    q1 = {0: 0, 1: 0, 2: 1, 3: 1}
    # hom K -> Z/2 killing g=3: q2: 0,1,2,3 -> 0,1,1,0
    q2 = {0: 0, 1: 1, 2: 1, 3: 0}
    f1 = induced_map(K, mulK, Z2, mul2, q1, barK, bar2, D)
    f2 = induced_map(K, mulK, Z2, mul2, q2, barK, bar2, D)
    idm = {i: i for i in range(4)}
    g1 = induced_map(K, mulK, K, mulK, idm, barK, barK, D)
    # cochain map C^*(A) -> C^*(C): A = BZ2(+)BZ2, C = BK(+)BK,
    # blockwise: summand i of A maps into summand i of C
    fcols = []
    for k in range(D + 1):
        c = [f1.cols[k][j] for j in range(bar2[0].dims[k])] + \
            [f2.cols[k][j] << barK[0].dims[k]
             for j in range(bar2[0].dims[k])]
        fcols.append(c)
    fmap = Map(fcols)
    # cochain map C^*(B) = C^*(BK) -> C^*(C): diagonal (both identities)
    gcols = []
    for k in range(D + 1):
        c = [g1.cols[k][j] | (g1.cols[k][j] << barK[0].dims[k])
             for j in range(barK[0].dims[k])]
        gcols.append(c)
    gmap = Map(gcols)
    bettis = hocolim_betti(A, Bc, C, fmap, gmap, D)
    print("H^*(el W_K) computed:", bettis[:D])
    print("expected (join):      [1, 0, 0, 1, 2, 3]")
