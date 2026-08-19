"""SP^2 in degree 6: the off-diagonal complex (O18, section 86).

For a simplicial set X the symmetric square SP^2 X = (X x X)/Sigma_2 has
    C_*(SP^2 X; F_2) = ( C_*(X) (x) C_*(X) )_{Sigma_2}
(the action on simplices is admissible: a pair fixed setwise is fixed
pointwise), the diagonal simplices span a SUBCOMPLEX D_* = C_*(X), and the
quotient Q_* (off-diagonal pairs) is a FREE F_2[Sigma_2]-complex, so
Tor_1(F_2, Q) = 0 and

    0 -> C_*(X) -> C_*(SP^2 X) -> (Q_*)_{Sigma_2} -> 0

is short exact, with the first map the DIAGONAL -- which is exactly the
map j induced by the diagonal carrier of R4.  Hence

    Delta_* : H_k(X) -> H_k(SP^2 X) is onto  <=>  H_k(SP^2X) -> H_k(Q_{S2})
    is zero, and the LES turns the question into a computation of
    H_*((Q_*)_{Sigma_2}), whose degree-k basis is the set of UNORDERED
    pairs of distinct k-simplices: (n_k^2 - n_k)/2 elements, far fewer
    than SP^2 itself.

Here X is the Cech model of el(cube^2/K) (n_k = 2, 6, 20, 72, 272, 1056).
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build

E2, i2, ID2, NE2, MUL2, INV2, ACT2 = build(2)
def close2(g):
    S = {ID2}; dq = deque([ID2])
    while dq:
        x = dq.popleft()
        for a in g:
            y = MUL2[x][a]
            if y not in S: S.add(y); dq.append(y)
    return frozenset(S)
K = sorted(close2([i2[((1, 0), (0, 0))], i2[((0, 1), (1, 1))]]))
acts = [ACT2[a] for a in K]

TOP = 5
# S_k = V_2^{k+1}/K  with face maps (delete a coordinate)
reps = []; index = []
for k in range(TOP + 1):
    m = k + 1
    seen = {}; R = []
    for t in itertools.product(range(4), repeat=m):
        if t in seen: continue
        oid = len(R); R.append(t)
        for A in acts:
            seen[tuple(A[x] for x in t)] = oid
    reps.append(R); index.append(seen)
print("n_k =", [len(r) for r in reps])

def face(t, i):
    return t[:i] + t[i+1:]

def rank(cols):
    piv = {}; r = 0
    for v in cols:
        while v:
            l = v.bit_length() - 1
            if l in piv: v ^= piv[l]
            else: piv[l] = v; r += 1; break
    return r

# ---- complexes: X (S_k), SP^2 (unordered pairs incl. diagonal), Q (strict) ----
def build_complex(kind):
    """kind in {'X','SP2','Q'}; returns list of basis and index dict"""
    basis = []; idxs = []
    for k in range(TOP + 1):
        n = len(reps[k])
        if kind == 'X':
            B = [(i,) for i in range(n)]
        elif kind == 'SP2':
            B = [(i, j) for i in range(n) for j in range(i, n)]
        else:
            B = [(i, j) for i in range(n) for j in range(i + 1, n)]
        basis.append(B); idxs.append({b: t for t, b in enumerate(B)})
    return basis, idxs

def boundary(kind, basis, idxs, k):
    cols = []
    for b in basis[k]:
        v = 0
        for i in range(k + 1):
            if kind == 'X':
                t = reps[k][b[0]]
                f = index[k-1][face(t, i)]
                key = (f,)
            else:
                t1 = reps[k][b[0]]; t2 = reps[k][b[1]]
                f1 = index[k-1][face(t1, i)]; f2 = index[k-1][face(t2, i)]
                a, c = min(f1, f2), max(f1, f2)
                if kind == 'Q' and a == c: continue   # lands in the diagonal
                key = (a, c)
            v ^= 1 << idxs[k-1][key]
        cols.append(v)
    return cols

for kind in ('X', 'SP2', 'Q'):
    basis, idxs = build_complex(kind)
    rk = {k: rank(boundary(kind, basis, idxs, k)) for k in range(1, TOP + 1)}
    H = {k: len(basis[k]) - rk[k] - rk[k+1] for k in range(1, TOP)}
    print(f"{kind:4s}: sizes {[len(b) for b in basis]}  "
          f"H_1..H_{TOP-1} = {[H[k] for k in range(1, TOP)]}", flush=True)


# ---- the diagonal chain map X -> SP^2 X and its rank on homology ----
print()
print("diagonal Delta : X -> SP^2 X, induced rank on H_k")
bX, iX = build_complex('X'); bS, iS = build_complex('SP2')
def hom_rank_map(k):
    # cycles of X in degree k, pushed to SP2, modulo boundaries of SP2
    piv = {}
    def add(v):
        while v:
            l = v.bit_length() - 1
            if l in piv: v ^= piv[l]
            else: piv[l] = v; return True
        return False
    for v in boundary('SP2', bS, iS, k + 1): add(v)
    cols = boundary('X', bX, iX, k); nX = len(bX[k])
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
        for i in range(nX):
            if (c >> i) & 1:
                j = bX[k][i][0]
                v ^= 1 << iS[k][(j, j)]
        if add(v): r += 1
    return r, len(kern)
for k in range(1, TOP):
    r, z = hom_rank_map(k)
    print(f"   k={k}: dim Z_k(X)={z}, rank of Delta_* on H_k = {r}")
