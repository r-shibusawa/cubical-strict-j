"""Integer homology of the triangulation T(W) for the 16
stage-1.5-resistant candidates (O22).  H_1(Z) torsion detects
odd/lens phenomena invisible to F_2; if some candidate has
H~_*(Z) = 0 (and is simply connected), it is test-contractible
yet resists filling -- a genuine separation suspect."""
import sys, ast, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, restrict, Quotient
from dedekind_triangulate import coface

def smith_diag(M):
    """Smith normal form diagonal of integer matrix M (list of
    rows).  Small matrices only."""
    import copy
    M = [row[:] for row in M]
    R = len(M); C = len(M[0]) if R else 0
    diag = []
    r = c = 0
    while r < R and c < C:
        # find pivot with minimal nonzero |value|
        piv = None
        for i in range(r, R):
            for j in range(c, C):
                if M[i][j] != 0 and (piv is None or
                                     abs(M[i][j]) < abs(M[piv[0]][piv[1]])):
                    piv = (i, j)
        if piv is None: break
        i0, j0 = piv
        M[r], M[i0] = M[i0], M[r]
        for row in M: row[c], row[j0] = row[j0], row[c]
        again = True
        while again:
            again = False
            for i in range(R):
                if i != r and M[i][c] % M[r][c] != 0:
                    q = M[i][c] // M[r][c]
                    for j in range(C): M[i][j] -= q * M[r][j]
                    if M[i][c] != 0:
                        M[r], M[i] = M[i], M[r]; again = True
            for j in range(C):
                if j != c and M[r][j] % M[r][c] != 0:
                    q = M[r][j] // M[r][c]
                    for i in range(R): M[i][j] -= q * M[i][c]
                    if M[r][j] != 0:
                        for i in range(R):
                            M[i][c], M[i][j] = M[i][j], M[i][c]
                        again = True
        for i in range(R):
            if i != r and M[i][c] != 0:
                q = M[i][c] // M[r][c]
                for j in range(C): M[i][j] -= q * M[r][j]
        for j in range(C):
            if j != c and M[r][j] != 0:
                q = M[r][j] // M[r][c]
                for i in range(R): M[i][j] -= q * M[i][c]
        diag.append(abs(M[r][c]))
        r += 1; c += 1
    return diag

def zhom(W, Q=3):
    reps = {}; ind = {}
    for q in range(Q + 1):
        lv = W.level(q)
        reps[q] = lv; ind[q] = {c: i for i, c in enumerate(lv)}
    def bmat(q):
        # boundary d_q: C_q -> C_{q-1}, integer entries
        rows = len(reps[q - 1]); cols = len(reps[q])
        M = [[0]*cols for _ in range(rows)]
        for jc, cell in enumerate(reps[q]):
            for i in range(q + 1):
                u = coface(i, q)
                fc = W.cls(q - 1, restrict(cell, u, 2, q, q - 1))
                M[ind[q - 1][fc]][jc] += (-1) ** i
        return M
    d1 = bmat(1); d2 = bmat(2); d3 = bmat(3)
    s1 = smith_diag(d1); s2 = smith_diag(d2); s3 = smith_diag(d3)
    r1 = sum(1 for x in s1 if x != 0)
    r2 = sum(1 for x in s2 if x != 0)
    r3 = sum(1 for x in s3 if x != 0)
    b0 = len(reps[0]) - r1
    b1 = len(reps[1]) - r1 - r2
    b2 = len(reps[2]) - r2 - r3
    t1 = [x for x in s2 if x not in (0, 1)]
    t2 = [x for x in s3 if x not in (0, 1)]
    return (b0, b1, t1, b2, t2)

from sweep2_candidates import CANDIDATES as cands
RESIST = [5,6,11,12,13,14,15,16,18,20,21,22,23,24,25,27]
for i in RESIST:
    W = Quotient(2, cands[i], 3)
    b0, b1, t1, b2, t2 = zhom(W)
    flag = " <== Z-ACYCLIC SUSPECT" if (b0==1 and b1==0 and
        not t1 and b2==0 and not t2) else ""
    print(f"cand-{i:02d}: b0={b0} b1={b1} tors1={t1} b2={b2} "
          f"tors2={t2}{flag}", flush=True)
