"""Rational homotopy of |cosk_1(c BZ)| computed WITHOUT any splitting assumption.

The simplicial space X_m = Map(|sk_1 Delta^m|, BZ) is the levelwise realization of the
bisimplicial abelian group T_{m,k} = Hom(sk_1 Delta^m x Delta^k, BZ) = normalized
Z-valued 1-cocycles on the simplicial set sk_1 Delta^m x Delta^k, and |X| is the
diagonal D_m = T_{m,m}.  D is a simplicial abelian group; pi_i(D) = H_i of the Moore
complex N_m = ker d_1 ∩ ... ∩ ker d_m with differential d_0, where d_j is induced by
the diagonal coface delta_j x delta_j.  We compute the ranks over Q for m <= mmax.

Prediction A (naive splitting argument):  pi_1 = pi_2 = Q, rest 0     (S^1 x K(Z,2)).
Prediction B (bisimplicial argument): all zero        (contractible = tau_{<=0} S^1).
"""
import itertools as it
import numpy as np

def monotone(q, m):
    """monotone maps [q] -> [m] as tuples"""
    return [t for t in it.product(range(m + 1), repeat=q + 1) if all(t[i] <= t[i + 1] for i in range(q))]

def coface(j, t):
    """delta_j^*: precompose a q-simplex t: [q]->[m'] ... we instead need the map on simplices
    induced by delta_j: [m-1] -> [m] (skip j) applied to the VALUES of t."""
    return tuple(v if v < j else v + 1 for v in t)

def face_index(j, t):
    """d_j on a simplex t: [q] -> [m]: skip position j of the tuple"""
    return t[:j] + t[j + 1:]

def cocycles(m):
    """Basis (columns) of Z^1(sk_1 Delta^m x Delta^m; Q) as vectors indexed by edges (a,b).
    Edges: a, b in Hom([1],[m]); a always has image of size <= 2.  Degenerate edge (a,b both
    constant) forced to 0.  Cocycle condition on 2-simplices (a,b) with |im a| <= 2."""
    E = [(a, b) for a in monotone(1, m) for b in monotone(1, m)]
    idx = {e: i for i, e in enumerate(E)}
    rows = []
    for a, b in E:
        if a[0] == a[1] and b[0] == b[1]:
            r = np.zeros(len(E)); r[idx[(a, b)]] = 1; rows.append(r)
    for a in monotone(2, m):
        if len(set(a)) > 2:
            continue
        for b in monotone(2, m):
            r = np.zeros(len(E))
            # c(d2) - c(d1) + c(d0) = 0 where d_i drops vertex i
            for sgn, i in ((1, 2), (-1, 1), (1, 0)):
                e = (face_index(i, a), face_index(i, b))
                r[idx[e]] += sgn
            rows.append(r)
    A = np.array(rows)
    u, s, vt = np.linalg.svd(A)
    rank = int((s > 1e-9).sum())
    return E, idx, vt[rank:].T  # kernel basis

def face_matrix(j, m, E, idx, E2, idx2):
    """d_j: Z^1(P_m) -> Z^1(P_{m-1}) induced by delta_j x delta_j (on cochains: pullback)"""
    M = np.zeros((len(E2), len(E)))
    for (a, b), i2 in idx2.items():
        M[i2, idx[(coface(j, a), coface(j, b))]] = 1
    return M

def main(mmax=4):
    data = {m: cocycles(m) for m in range(mmax + 1)}
    Nbasis = {}
    for m in range(mmax + 1):
        E, idx, Z = data[m]
        if m == 0:
            Nbasis[m] = Z; continue
        E2, idx2, Z2 = data[m - 1]
        # condition: d_j z in Z^1(P_{m-1}) is zero for j = 1..m (as a cochain, since d_j z is automatically a cocycle)
        blocks = [face_matrix(j, m, E, idx, E2, idx2) @ Z for j in range(1, m + 1)]
        A = np.vstack(blocks)
        u, s, vt = np.linalg.svd(A) if A.size else (None, np.array([]), np.eye(Z.shape[1]))
        rank = int((s > 1e-9).sum())
        Nbasis[m] = Z @ vt[rank:].T
    dims = [Nbasis[m].shape[1] for m in range(mmax + 1)]
    bd = [0]
    for m in range(1, mmax + 1):
        E, idx, _ = data[m]; E2, idx2, _ = data[m - 1]
        D = face_matrix(0, m, E, idx, E2, idx2) @ Nbasis[m]
        bd.append(int(np.linalg.matrix_rank(D)) if D.size else 0)
    homot = [dims[m] - bd[m] - (bd[m + 1] if m + 1 <= mmax else 0) for m in range(mmax)]
    print("dim N_m       :", dims)
    print("rank d_0      :", bd)
    print("pi_0..pi_%d(Q) :" % (mmax - 1), homot, "(pi_%d needs N_%d)" % (mmax - 1, mmax))

if __name__ == "__main__":
    main(4)
