"""Triangulation invariant for Dedekind cubical sets (O22).

Cosimplicial object C: Delta -> cube_Ded, C[q] = [q], with
cofaces (as site maps [q-1] -> [q], i.e. q-tuples over F(q-1)):
  d^0     = (1, y_1, ..., y_{q-1})        (x_1 := 1)
  d^i     = (y_1,..,y_i, y_i, ..,y_{q-1}) (diagonal x_i = x_{i+1})
  d^q     = (y_1, ..., y_{q-1}, 0)        (x_q := 0)
T(W)_q := W([q]) with simplicial faces by precomposition;
unnormalized F2 chains compute H_*(|T(W)|).

Validation targets: T(cube^n) acyclic; T(S^1): H_1 = 1;
T(pinched square) acyclic.  (The asphericity of C is a separate
lemma; here T is used as a machine invariant, validated on
knowns.)
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, cube_cells, all_maps, restrict, Quotient

def coface(i, q):
    """site map [q-1] -> [q] as q-tuple over F(q-1)"""
    ptsq1, fq1 = F(q - 1)
    def fn_var(j):   # y_j as element of F(q-1), j in 1..q-1
        return tuple(p[j-1] for p in ptsq1)
    def fn_const(c): return tuple(c for _ in ptsq1)
    if i == 0:
        return tuple([fn_const(1)] + [fn_var(j) for j in range(1, q)])
    if i == q:
        return tuple([fn_var(j) for j in range(1, q)] + [fn_const(0)])
    return tuple([fn_var(j) for j in range(1, i+1)] + [fn_var(i)] +
                 [fn_var(j) for j in range(i+1, q)])

def rank2(cols):
    piv = {}; r = 0
    for v in cols:
        while v:
            l = v.bit_length() - 1
            if l in piv: v ^= piv[l]
            else: piv[l] = v; r += 1; break
    return r

def tri_homology(W, n, Q):
    """F2 homology of T(W) in degrees 0..Q-1 (chains to level Q)"""
    # level-q simplices = classes of W([q])
    reps = {}; ind = {}
    for q in range(Q + 1):
        lv = W.level(q)
        reps[q] = lv; ind[q] = {c: i for i, c in enumerate(lv)}
    def dmat(q):
        cols = []
        for cell in reps[q]:
            v = 0
            for i in range(q + 1):
                u = coface(i, q)
                fc = W.cls(q - 1, restrict(cell, u, n, q, q - 1))
                v ^= 1 << ind[q - 1][fc]
            cols.append(v)
        return cols
    r = {q: rank2(dmat(q)) for q in range(1, Q + 1)}
    b = [len(reps[0]) - r[1]]
    for q in range(1, Q):
        b.append(len(reps[q]) - r[q] - r[q + 1])
    return b

if __name__ == '__main__':
    # validation
    triv = Quotient(1, [], 4)
    print("T(cube^1) F2-Betti deg0..3:", tri_homology(triv, 1, 4),
          flush=True)
    v0 = ((0,),); v1 = ((1,),)
    s1 = Quotient(1, [(0, v0, v1)], 4)
    print("T(S^1)    F2-Betti deg0..3:", tri_homology(s1, 1, 4),
          flush=True)
    e_x0  = ((0,0),(0,1)); e_pt0 = ((0,0),(0,0))
    pinch = Quotient(2, [(1, e_x0, e_pt0)], 4)
    print("T(pinch)  F2-Betti deg0..3:", tri_homology(pinch, 2, 4),
          flush=True)
    sq = Quotient(2, [], 4)
    print("T(cube^2) F2-Betti deg0..3:", tri_homology(sq, 2, 4),
          flush=True)
