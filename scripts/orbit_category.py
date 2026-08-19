"""el(cube^n/D) = B(O_F(D)): the orbit-category formula (O18, section 77).

The cell category X = el(cube^n) is contractible and, for every subgroup
K <= D, the fixed category X^K is the stratum of K -- contractible when K
is FIXED-TYPE (it has a maximal cell) and empty otherwise.  Hence X is a
model for E_F(D), the classifying space of the family
    F(D) := { K <= D : K has a common fixed cell }   (isotropy family),
and, since el of a quotient is the strict quotient of el,

    el(cube^n / D)  =  X / D  =  E_F(D) / D  =  |N(O_F(D))| ,

the classifying space of the ORBIT CATEGORY of the family: objects D/K
(K in F up to conjugacy), morphisms D/K -> D/K' the D-maps xK |-> xgK'
for g with g^{-1} K g <= K'; Aut(D/K) = the Weyl group N_D(K)/K.

Consequences (immediate):
  * pi_1 = D / <K : K in F> = D / <reflections>       (Armstrong)
  * el(cube^n/D) is always Q-ACYCLIC (H_*(X/D;Q) = H_*(X;Q)^D = Q),
    so W1 is intrinsically a TORSION statement -- as every case
    computation of papers 13/14 found (H_3 = Z/2 etc.);
  * for a free action F = {1} and the formula gives BD;
  * for D fixed-type, D/D is terminal and B(O_F(D)) is contractible.

This script computes H_*(B O_F(D); F_2) in low degrees from the normalised
nerve and calibrates against the three published values:
    el(W_K)   : 0, 0, 1   (RP^oo * RP^oo)
    el(W_H8)  : 1, 1, 2
    el(W_H24) : 1, 2, 4
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

def orbit_category(D, MUL, INV, ID, ACT, n):
    """objects = conjugacy classes of fixed-type subgroups of D;
    morphisms D/K -> D/K' = cosets gK' with g^{-1}Kg <= K'."""
    D = sorted(D)
    def close(gens):
        S = {ID}; dq = deque([ID])
        while dq:
            x = dq.popleft()
            for g in gens:
                y = MUL[x][g]
                if y not in S: S.add(y); dq.append(y)
        return frozenset(S)
    subs = {frozenset([ID])}
    frontier = {frozenset([ID])}
    while frontier:
        new = set()
        for H in frontier:
            for g in D:
                if g in H: continue
                H2 = close(sorted(set(H) | {g}))
                if H2 not in subs: new.add(H2)
        subs |= new; frontier = new
    fam = [K for K in subs
           if any(all(ACT[a][v] == v for a in K) for v in range(1 << n))]
    # conjugacy classes
    reps = []; seen = set()
    for K in sorted(fam, key=lambda S: (len(S), sorted(S))):
        key = min(tuple(sorted(MUL[MUL[g][a]][INV[g]] for a in K)) for g in D)
        if key in seen: continue
        seen.add(key); reps.append(sorted(K))
    objs = list(range(len(reps)))
    # cosets of each K
    cos = []
    for K in reps:
        seenc = {}; lst = []
        for g in D:
            c = frozenset(MUL[g][a] for a in K)
            if c not in seenc:
                seenc[c] = len(lst); lst.append((c, g))
        cos.append((seenc, lst))
    mors = {}          # (i,j) -> list of coset-index in K_j
    for i, K in enumerate(reps):
        for j, L in enumerate(reps):
            out = []
            for ci, (c, g) in enumerate(cos[j][1]):
                gi = INV[g]
                if all(MUL[MUL[gi][a]][g] in L for a in K):
                    out.append(ci)
            mors[(i, j)] = out
    def comp(i, j, k, ci, cj):
        g = cos[j][1][ci][1]; h = cos[k][1][cj][1]
        gh = MUL[g][h]
        return cos[k][0][frozenset(MUL[gh][a] for a in reps[k])]
    ident = {}
    for i in range(len(reps)):
        ident[i] = cos[i][0][frozenset(reps[i])]
    return reps, mors, comp, ident

def nerve_homology(reps, mors, comp, ident, top=4, verbose=False):
    """H_d(|N(C)|; F_2) for d <= top-2 via the normalised chain complex."""
    nobj = len(reps)
    arrows = [(i, j, c) for (i, j), L in mors.items() for c in L
              if not (i == j and c == ident[i])]
    if verbose:
        print(f"    objects={nobj} non-identity morphisms={len(arrows)}")
    out_of = {}
    for (i, j, c) in arrows: out_of.setdefault(i, []).append((j, c))
    chains = [[(i,) for i in range(nobj)], [(a,) for a in arrows]]
    for k in range(2, top + 1):
        prev = chains[-1]; cur = []
        for ch in prev:
            (i, j, c) = ch[-1]
            for (j2, c2) in out_of.get(j, []):
                cur.append(ch + ((j, j2, c2),))
        chains.append(cur)
        if len(cur) > 4_000_000:
            raise MemoryError("nerve too large")
    if verbose:
        print(f"    chain sizes: {[len(c) for c in chains]}")
    index = [{ch: t for t, ch in enumerate(ck)} for ck in chains]
    def boundary(k):
        """matrix C_k -> C_{k-1} as list of column bitmasks"""
        cols = []
        for ch in chains[k]:
            v = 0
            # d_0 : drop the first arrow (source object becomes ch[0][1])
            if k == 1:
                v ^= 1 << index[0][(ch[0][1],)]
            else:
                v ^= 1 << index[k-1][ch[1:]]
            # d_i for 0<i<k : compose
            for i in range(1, k):
                (a1, b1, c1) = ch[i-1]; (a2, b2, c2) = ch[i]
                cc = comp(a1, b1, b2, c1, c2)
                if a1 == b2 and cc == ident[a1]:
                    pass                       # degenerate: zero in N
                else:
                    nf = ch[:i-1] + ((a1, b2, cc),) + ch[i+1:]
                    v ^= 1 << index[k-1][nf]
            # d_k : drop the last arrow
            if k == 1:
                v ^= 1 << index[0][(ch[0][0],)]
            else:
                v ^= 1 << index[k-1][ch[:-1]]
            cols.append(v)
        return cols
    def rank(cols):
        piv = {}; r = 0
        for v in cols:
            while v:
                l = v.bit_length() - 1
                if l in piv: v ^= piv[l]
                else:
                    piv[l] = v; r += 1; break
        return r
    ranks = {}
    for k in range(1, top + 1):
        ranks[k] = rank(boundary(k))
    dims = {k: len(chains[k]) for k in range(top + 1)}
    H = {}
    for d in range(1, top):
        H[d] = dims[d] - ranks[d] - ranks[d + 1]
    H[0] = dims[0] - ranks[1]
    return H, dims

if __name__ == "__main__":
    print("calibration against the published el-computations")
    # K <= B_2
    E2, idx2, ID2, NE2, MUL2, INV2, ACT2 = build(2)
    def cl(MUL, ID, gens):
        S = {ID}; dq = deque([ID])
        while dq:
            x = dq.popleft()
            for g in gens:
                y = MUL[x][g]
                if y not in S: S.add(y); dq.append(y)
        return frozenset(S)
    sw2 = idx2[((1, 0), (0, 0))]; nb2 = idx2[((0, 1), (1, 1))]
    K = cl(MUL2, ID2, [sw2, nb2])
    reps, mors, comp, ident = orbit_category(K, MUL2, INV2, ID2, ACT2, 2)
    H, dims = nerve_homology(reps, mors, comp, ident, top=4, verbose=True)
    print(f"  K <= B_2 (|D|=4): H_* = {H}   [expected 0,0,1 in d=1,2,3]")

    E3, idx3, ID3, NE3, MUL3, INV3, ACT3 = build(3)
    sw = idx3[((1, 0, 2), (0, 0, 0))]; n011 = idx3[((0, 1, 2), (0, 1, 1))]
    H8 = cl(MUL3, ID3, [sw, n011])
    reps, mors, comp, ident = orbit_category(H8, MUL3, INV3, ID3, ACT3, 3)
    H, dims = nerve_homology(reps, mors, comp, ident, top=4, verbose=True)
    print(f"  H8 <= B_3 (|D|=8): H_* = {H}   [expected 1,1,2]")

    nx = idx3[((0, 1, 2), (1, 0, 0))]; ny = idx3[((0, 1, 2), (0, 1, 0))]
    nz = idx3[((0, 1, 2), (0, 0, 1))]; rot = idx3[((1, 2, 0), (0, 0, 0))]
    H24 = cl(MUL3, ID3, [nx, ny, nz, rot])
    reps, mors, comp, ident = orbit_category(H24, MUL3, INV3, ID3, ACT3, 3)
    H, dims = nerve_homology(reps, mors, comp, ident, top=4, verbose=True)
    print(f"  H24 <= B_3 (|D|=24): H_* = {H}   [expected 1,2,4]")
