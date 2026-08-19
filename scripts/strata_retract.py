"""Non-retraction of el(W) onto the strata part (O18, section 79).

The general-n nullity theorem is RELATIVE: an invariant end class of the
collage need not be strict (section 79 census), so a map W -> R(J/D) is
null OR factors through the strata part S_W = S/D, S = union of the
maximal strata.  The separation therefore needs

    (NR)  id_W does not factor through S_W  ->  W  in Ho(type),

which, applying el (type homotopies are test homotopies), follows from

    el(W) is NOT a retract of el(S_W)     <=  q_* is not surjective,

q : el(S_W) -> el(W) induced by S <= cube^n.

Both sides are computed by the vertex Cech model of section 77: with
V = {0,1}^n and V_i the vertex set of the i-th maximal stratum,

    A_k = F_2[ V^{k+1} / D ]                 computes H_*(el W),
    B_k = F_2[ (U_i V_i^{k+1}) / D ]         computes H_*(el S_W),

(the simplicial subset of tuples lying in a common stratum: each
V_i^{*+1} is the Cech nerve of a nonempty set, hence contractible, and
intersections are the Cech nerves of the intersections, so |B| is the
nerve of the covering = el(S); the D-action is admissible on both), and
q_* is induced by the inclusion of complexes.
"""
import itertools, sys
from collections import deque

def build(n):
    ELEMS = [(p, s) for p in itertools.permutations(range(n))
             for s in itertools.product((0, 1), repeat=n)]
    idx = {e: i for i, e in enumerate(ELEMS)}
    NE = len(ELEMS); ID = idx[(tuple(range(n)), (0,)*n)]
    def mmr(e1, e2):
        (p1, s1), (p2, s2) = e1, e2
        return (tuple(p2[p1[i]] for i in range(n)),
                tuple(s1[i] ^ s2[p1[i]] for i in range(n)))
    MUL = [[idx[mmr(ELEMS[a], ELEMS[b])] for b in range(NE)] for a in range(NE)]
    INV = [next(b for b in range(NE) if MUL[a][b] == ID) for a in range(NE)]
    ACT = []
    for a in range(NE):
        p, s = ELEMS[a]
        ACT.append([sum(((((v >> p[i]) & 1) ^ s[i]) << i) for i in range(n))
                    for v in range(1 << n)])
    return ELEMS, idx, ID, NE, MUL, INV, ACT

class Cx:
    """orbit chain complex of a simplicial subset of the Cech nerve"""
    def __init__(s, NV, acts, top, allowed=None):
        s.NV = NV; s.top = top
        s.reps = []; s.ind = []
        for k in range(top + 1):
            m = k + 1; size = NV ** m
            seen = bytearray(size); reps = []; ind = {}
            for code in range(size):
                if seen[code]: continue
                t = []; c = code
                for _ in range(m): t.append(c % NV); c //= NV
                if allowed is not None and not allowed(t):
                    seen[code] = 1; continue
                oid = len(reps); reps.append(code)
                for A in acts:
                    c2 = 0
                    for j in range(m - 1, -1, -1): c2 = c2 * NV + A[t[j]]
                    seen[c2] = 1; ind[c2] = oid
            s.reps.append(reps); s.ind.append(ind)
    def faces(s, code, m):
        t = []; c = code
        for _ in range(m): t.append(c % s.NV); c //= s.NV
        out = []
        for i in range(m):
            u = t[:i] + t[i+1:]; c2 = 0
            for j in range(len(u) - 1, -1, -1): c2 = c2 * s.NV + u[j]
            out.append(c2)
        return out
    def d(s, k):
        """columns of d_k : C_k -> C_{k-1} as bitmasks over C_{k-1}"""
        cols = []
        for code in s.reps[k]:
            v = 0
            for f in s.faces(code, k + 1): v ^= 1 << s.ind[k-1][f]
            cols.append(v)
        return cols

def rank(cols):
    piv = {}; r = 0
    for v in cols:
        while v:
            l = v.bit_length() - 1
            if l in piv: v ^= piv[l]
            else: piv[l] = v; r += 1; break
    return r

def homology(cx, top):
    rk = {k: rank(cx.d(k)) for k in range(1, top + 1)}
    return {k: len(cx.reps[k]) - rk[k] - rk[k+1] for k in range(1, top)}

def analyse(D, ACT, n, Vs, top=4, name=""):
    NV = 1 << n
    acts = [ACT[a] for a in sorted(D)]
    A = Cx(NV, acts, top)
    B = Cx(NV, acts, top, allowed=lambda t: any(all(x in Vi for x in t)
                                                for Vi in Vs))
    HA = homology(A, top); HB = homology(B, top)
    # q_* : H_k(B) -> H_k(A) -- compute rank of the induced map
    surj = {}
    for k in range(1, top):
        # cycles of B in degree k, pushed into A, modulo boundaries of A
        piv = {}
        def add(v):
            while v:
                l = v.bit_length() - 1
                if l in piv: v ^= piv[l]
                else: piv[l] = v; return True
            return False
        base = 0
        for v in A.d(k + 1): add(v)
        base = len(piv)
        # push cycles of B
        # cycle basis of B_k: kernel of d_k
        cols = B.d(k); nB = len(B.reps[k])
        # gaussian: find kernel basis
        piv2 = {}; comb = {}
        kern = []
        for i, v in enumerate(cols):
            c = 1 << i
            while v:
                l = v.bit_length() - 1
                if l in piv2:
                    v ^= piv2[l]; c ^= comb[l]
                else:
                    piv2[l] = v; comb[l] = c; c = None; break
            if c is not None: kern.append(c)
        img = 0
        for c in kern:
            v = 0
            for i in range(nB):
                if (c >> i) & 1:
                    v ^= 1 << A.ind[k][B.reps[k][i]]
            if add(v): img += 1
        surj[k] = (img, HA[k], HB[k])
    return HA, HB, surj
