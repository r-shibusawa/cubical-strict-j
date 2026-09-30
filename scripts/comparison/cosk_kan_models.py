"""Cross-check for the saturation theorem in simplicial spaces.

For a levelwise discrete simplicial space (= a simplicial set X), cosk_{n+1} in
simplicial spaces agrees with the simplicial-set coskeleton, and for a KAN X the
realization |cosk_{n+1} X| is the Postnikov section tau_{<=n}|X|.  We check the
rational homotopy of cosk_{n+1} X for the simplicial abelian group models

    X = B Z      (n = 0):  (cosk_1 X)_m = C^1(Delta^m; Z)       -> expect contractible
    X = K(Z,2)   (n = 1):  (cosk_2 X)_m = C^2_norm(Delta^m; Z)  -> expect contractible
    X = K(Z,3)   (n = 2):  (cosk_3 X)_m = C^3_norm(Delta^m; Z)  -> expect contractible

via the Moore complex N_m = ker d_1 ∩ ... ∩ ker d_m, differential d_0 (ranks over Q).
Here (cosk_k K(Z,k))_m = Hom(sk_k Delta^m, K(Z,k)) = normalized k-cocycles on
sk_k Delta^m = all k-cochains (no (k+1)-simplices), so the model is the simplicial
abelian group of k-cochains with faces = restriction; expected value: P_{k-1}K(Z,k) = pt.

For contrast, the NON-Kan oriented 3-cycle C_3 (n = 0) is 1-coskeletal with
|C_3| = S^1, so |cosk_1 C_3| is not 0-truncated: the Kan hypothesis is used.
"""
import itertools as it
import numpy as np

def simplices(m, k):
    return list(it.combinations(range(m + 1), k + 1))

def face_restriction(m, k, i):
    """d_i: C^k(Delta^m) -> C^k(Delta^{m-1}) restricting to the face missing vertex i."""
    S, S2 = simplices(m, k), simplices(m - 1, k)
    vert = [v for v in range(m + 1) if v != i]
    R = np.zeros((len(S2), len(S)), dtype=int)
    for r, s in enumerate(S2):
        R[r, S.index(tuple(vert[a] for a in s))] = 1
    return R

def moore_ranks(k, mmax):
    """Rational homotopy ranks of the simplicial abelian group Y_m = C^k(Delta^m).
    Y_m = cosk_k(K(Z,k))_m for the normalized cocycle model (cocycle condition vacuous on sk_k)."""
    N = {}
    for m in range(mmax + 1):
        dimY = len(simplices(m, k))
        if m == 0 or dimY == 0:
            N[m] = np.eye(dimY, dtype=int) if dimY else np.zeros((0, 0), dtype=int)
            continue
        A = np.vstack([face_restriction(m, k, i) for i in range(1, m + 1)])
        # kernel basis of A (over Q) via SVD
        u, s, vt = np.linalg.svd(A.astype(float))
        rank = int((s > 1e-9).sum())
        N[m] = vt[rank:].T  # columns = basis of ker
    ranks = []
    for m in range(mmax + 1):
        dimN = N[m].shape[1] if N[m].size else 0
        # d_0 : N_m -> N_{m-1}
        if m == 0:
            r_out = 0
        else:
            D = face_restriction(m, k, 0) @ N[m] if dimN else np.zeros((0, 0))
            r_out = int(np.linalg.matrix_rank(D)) if D.size else 0
        ranks.append((dimN, r_out))
    homot = []
    for m in range(mmax):
        dimN, r_out = ranks[m]
        r_in = ranks[m + 1][1]
        homot.append(dimN - r_out - r_in)
    return homot

if __name__ == "__main__":
    print("cosk_1 (B Z) = C^1 cochains         pi_0..pi_5 ranks:", moore_ranks(1, 6))
    print("cosk_2 K(Z,2) = C^2 cochains        pi_0..pi_5 ranks:", moore_ranks(2, 6))
    print("cosk_3 K(Z,3) = C^3 cochains        pi_0..pi_5 ranks:", moore_ranks(3, 6))
    # sanity: cosk_k K(Z,k) contractible for all k (it is P_{k-1} K(Z,k) = pt)
    # the non-Kan 3-cycle: 1-coskeletal, realization S^1 -> not 0-truncated
