"""Sharp non-retraction (NR'): a twisted end class factors through ONE
stratum quotient (O18, section 79).

An end cell lies in a single maximal stratum l, so the map W -> S_W has
image in (D.l)/D = l/N_l = cube^m / Q_l  (Q_l = N_l/P_l <= B_m, m < n).
Hence the separation needs only

    (NR')  id_W does not factor through l/N_l -> W   for any maximal l,

and applying el: el(W) is not a retract of el(cube^m/Q_l).  Both sides are
vertex Cech models (section 77) -- the source has only 2^m vertices -- and
the comparison map is induced by V_l <= V, N_l <= D.

Note the clean general case: if Q_l fixes a vertex of l then
el(cube^m/Q_l) is F_2-acyclic (Theorem W1), so a retraction would make
el(W) acyclic, contradicting W1 for the mixed group D.
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build, rank

def orbit_complex(codes_iter, NV, acts, m):
    """orbit reps + index map for tuples of length m over a vertex set"""
    seen = {}; reps = []
    for code in codes_iter:
        if code in seen: continue
        t = []; c = code
        for _ in range(m): t.append(c % NV); c //= NV
        oid = len(reps); reps.append(code)
        for A in acts:
            c2 = 0
            for j in range(m - 1, -1, -1): c2 = c2 * NV + A[t[j]]
            seen[c2] = oid
    return reps, seen

class VC:
    """Cech orbit complex of a D-set given by an explicit vertex list"""
    def __init__(s, verts, acts, top, NV=None):
        s.verts = verts; s.NV = NV if NV is not None else max(verts) + 1
        s.pos = {v: i for i, v in enumerate(verts)}
        s.reps = []; s.ind = []
        for k in range(top + 1):
            m = k + 1
            codes = (sum(t[j] * (s.NV ** j) for j in range(m))
                     for t in itertools.product(verts, repeat=m))
            reps, ind = orbit_complex(codes, s.NV, acts, m)
            s.reps.append(reps); s.ind.append(ind)
    def d(s, k):
        cols = []
        for code in s.reps[k]:
            t = []; c = code
            for _ in range(k + 1): t.append(c % s.NV); c //= s.NV
            v = 0
            for i in range(k + 1):
                u = t[:i] + t[i+1:]
                c2 = sum(u[j] * (s.NV ** j) for j in range(len(u)))
                v ^= 1 << s.ind[k-1][c2]
            cols.append(v)
        return cols

def homology(cx, top):
    rk = {k: rank(cx.d(k)) for k in range(1, top + 1)}
    return {k: len(cx.reps[k]) - rk[k] - rk[k+1] for k in range(1, top)}

def induced_rank(src, tgt, k, phi):
    """rank of H_k(src) -> H_k(tgt); phi maps a src code to a tgt code"""
    piv = {}
    def add(v):
        while v:
            l = v.bit_length() - 1
            if l in piv: v ^= piv[l]
            else: piv[l] = v; return True
        return False
    for v in tgt.d(k + 1): add(v)
    cols = src.d(k); nS = len(src.reps[k])
    piv2 = {}; comb = {}; kern = []
    for i, v in enumerate(cols):
        c = 1 << i
        while v:
            l = v.bit_length() - 1
            if l in piv2: v ^= piv2[l]; c ^= comb[l]
            else: piv2[l] = v; comb[l] = c; c = None; break
        if c is not None: kern.append(c)
    r = 0
    for c in kern:
        v = 0
        for i in range(nS):
            if (c >> i) & 1: v ^= 1 << tgt.ind[k][phi(src.reps[k][i], k + 1)]
        if add(v): r += 1
    return r
