"""Alternating torsion filtrations of persistence modules.

A persistence module is a representation  ... -> M_2 -> M_1 -> M_0  of the ordinal omega in vector spaces
(here over GF(2), finite support).  T = modules supported on the even vertices, T' = on the odd vertices,
two hereditary torsion theories; t(M)_n = Ker(M_n -> M_{n-1}) for n even (t(M)_0 = M_0), 0 for n odd,
and symmetrically t'.  The canonical alternating filtration of M is
    X_1 = t'(M),  X_2 = preimage of t(M/X_1),  X_3 = preimage of t'(M/X_2), ...
and M lies in E_k iff X_{2k} = M.  The script computes the length of this filtration for interval modules
k[a,b] and for direct sums, confirming that k[0,N] needs length N+2 (unbounded in N), while any module is
exhausted at a finite stage (the join torsion theory is everything).
"""
import itertools as it

def rank2(rows):
    """rank over GF(2) of a list of row bitmasks"""
    rows = list(rows); r = 0
    for bit in range(64):
        piv = next((i for i in range(r, len(rows)) if rows[i] >> bit & 1), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i] >> bit & 1: rows[i] ^= rows[r]
        r += 1
    return r

class PMod:
    """M[n] = dimension d_n; maps A_n : M_n -> M_{n-1} as lists of column bitmasks (image of basis vectors)"""
    def __init__(self, dims, maps):
        self.dims = dims            # list, index n
        self.maps = maps            # maps[n] : list of bitmasks (length dims[n]), images in M_{n-1}; maps[0] unused
    @staticmethod
    def interval(a, b):
        N = b + 1; dims = [1 if a <= n <= b else 0 for n in range(N)]
        maps = [None] + [[1] if (a < n <= b) else [0] * dims[n] for n in range(1, N)]
        return PMod(dims, maps)
    @staticmethod
    def dsum(A, B):
        N = max(len(A.dims), len(B.dims)); dims = [(A.dims[n] if n < len(A.dims) else 0) + (B.dims[n] if n < len(B.dims) else 0) for n in range(N)]
        maps = [None]
        for n in range(1, N):
            da = A.dims[n - 1] if n - 1 < len(A.dims) else 0
            ma = A.maps[n] if n < len(A.maps) and A.maps[n] is not None else []
            mb = B.maps[n] if n < len(B.maps) and B.maps[n] is not None else []
            maps.append(list(ma) + [v << da for v in mb])
        return PMod(dims, maps)

def subspace_from_kernel(M, n):
    """basis (bitmasks over M_n) of Ker(M_n -> M_{n-1}); for n = 0 the whole space"""
    d = M.dims[n]
    if d == 0: return []
    if n == 0: return [1 << i for i in range(d)]
    # kernel of the linear map given by columns M.maps[n]
    cols = M.maps[n]; basis = []
    # brute force over GF(2)^d (dims are tiny)
    vecs = []
    for v in range(1, 1 << d):
        img = 0
        for i in range(d):
            if v >> i & 1: img ^= cols[i]
        if img == 0: vecs.append(v)
    # extract a basis
    for v in vecs:
        if rank2(basis + [v]) > len(basis): basis.append(v)
    return basis

def filtration_length(M, start_odd=True):
    """length of the canonical alternating filtration (number of nonzero steps until exhaustion)"""
    N = len(M.dims)
    # represent the current subobject X by a basis per vertex; work with quotient M/X implicitly:
    # we track, per vertex, a subspace X_n and compute t or t' of the quotient.
    X = [[] for _ in range(N)]
    def dim(n): return rank2(X[n])
    steps = 0
    parity_odd = start_odd
    while any(dim(n) < M.dims[n] for n in range(N)):
        steps += 1
        # new elements: at vertices of the right parity, vectors v with image in X_{n-1} (kernel modulo X)
        newX = [list(b) for b in X]
        for n in range(N):
            if (n % 2 == 1) != parity_odd: continue
            d = M.dims[n]
            if d == 0: continue
            for v in range(1, 1 << d):
                img = 0
                if n > 0:
                    for i in range(d):
                        if v >> i & 1: img ^= M.maps[n][i]
                in_prev = (n == 0) or rank2(X[n - 1] + [img]) == rank2(X[n - 1])
                if in_prev and rank2(newX[n] + [v]) > rank2(newX[n]): newX[n].append(v)
        if newX == X and steps > 2 * N + 2: return None
        X = newX; parity_odd = not parity_odd
    return steps

if __name__ == "__main__":
    for Nv in range(0, 8):
        I = PMod.interval(0, Nv)
        print(f"k[0,{Nv}]: canonical alternating filtration length = {filtration_length(I)}  (expected N+2 = {Nv+2})")
    S = PMod.interval(0, 2)
    for Nv in range(3, 7): S = PMod.dsum(S, PMod.interval(0, Nv))
    print("direct sum k[0,2]+...+k[0,6]: length =", filtration_length(S), "(= max of the summands, 8)")
    print("k[3,5]: length =", filtration_length(PMod.interval(3, 5)), "(interval not starting at 0: 3-5 peeled from the bottom)")
