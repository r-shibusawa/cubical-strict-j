"""THEOREM W1 (general n), O18 section 77.

    el(cube^n/D) is F_2-acyclic  <=>  D fixes a vertex (D is fixed-type).

Proof (all steps verified below on every subgroup of B_n, n <= 4):

(1) el(cube^n) is the cell category; it has a terminal object (the
    identity cell) so it is contractible, and for K <= D its K-fixed
    subcategory is the cell category of the fixed locus of K -- again
    with a terminal object -- nonempty exactly when K fixes a cell,
    i.e. (C1') when K fixes a VERTEX.  Hence el(cube^n) is a model for
    E_F(D) with F = { K : K fixes a vertex }.

(2) The infinite join V^{*oo} of the vertex D-set V = {0,1}^n has
    (V^{*oo})^K = (V^K)^{*oo}, contractible iff V^K is nonempty, so it is
    a second model; E_F(D) is unique up to D-homotopy and el of a
    quotient presheaf is the quotient of el, so
        el(cube^n/D) ~ V^{*oo}/D .

(3) D permutes only the V-coordinates of a join simplex and the join
    coordinates are pairwise distinct, so the action is admissible and
        H_*(el(cube^n/D); F_2) = H_*( F_2[V^{*+1}]_D )
                               = H_*^F(D; F_2)   (relative group homology).

(4) Higman's criterion: H^F_{>0}(D;F_2) = 0 iff the trivial module is
    F-projective iff some K in F has ODD index in D, i.e. iff some
    D-orbit on V has odd size.

(5) AFFINE FIXED-POINT LEMMA: V = F_2^n and D acts affinely
    (v |-> P_h v + s_h), so a fixed vertex exists iff the cocycle class
    [s] in H^1(D; F_2^n) vanishes.  That class is 2-primary and
    restriction to a Sylow 2-subgroup S is injective on the 2-primary
    part (cor . res = [D:S] = odd).  Hence
        D fixes a vertex <=> S fixes a vertex <=> some vertex orbit is odd.

(3)+(4)+(5) give the theorem; with pi_1 = D/<reflections> (Armstrong) it
also yields: el(cube^n/D) is contractible <=> D is fixed-type.
"""
import sys, itertools
from collections import deque, Counter
sys.path.insert(0, 'scripts')
from el_homology import build, el_homology

for n in (1, 2, 3, 4):
    ELEMS, idx, ID, NE, MUL, INV, ACT = build(n)
    def close(gens):
        S = {ID}; dq = deque([ID])
        while dq:
            x = dq.popleft()
            for g in gens:
                y = MUL[x][g]
                if y not in S: S.add(y); dq.append(y)
        return frozenset(S)
    subs = {frozenset([ID]): []}
    frontier = list(subs.items())
    while frontier:
        new = []
        for H, gens in frontier:
            for g in range(NE):
                if g in H: continue
                H2 = close(gens + [g])
                if H2 not in subs:
                    subs[H2] = gens + [g]; new.append((H2, gens + [g]))
        frontier = new
    subs = list(subs)
    # (5) some vertex orbit has odd size  <=>  D fixes a vertex
    bad = 0
    for H in subs:
        V = 1 << n
        seenv = [False]*V; odd = False
        for v in range(V):
            if seenv[v]: continue
            orb = {ACT[a][v] for a in H}
            for w in orb: seenv[w] = True
            if len(orb) % 2 == 1: odd = True
        fix = any(all(ACT[a][v] == v for a in H) for v in range(V))
        if odd != fix: bad += 1
    print(f"n={n}: subgroups {len(subs)};  "
          f"[some vertex orbit odd] == [D fixes a vertex]: "
          f"{'ALL AGREE' if bad == 0 else f'{bad} MISMATCHES'}")
    # (3)+(4): F_2-acyclicity of el vs fixed-type, on conjugacy classes
    classes = {}
    for H in subs:
        key = min(tuple(sorted(MUL[MUL[g][a]][INV[g]] for a in H))
                  for g in range(NE))
        classes.setdefault(key, H)
    top = 5 if n <= 3 else 4
    mism = []
    for H in classes.values():
        if len(H) == 1: continue
        Hh = el_homology(H, ACT, n, top=top)
        acyc = all(Hh[d] == 0 for d in range(1, top))
        fix = any(all(ACT[a][v] == v for a in H) for v in range(1 << n))
        if acyc != fix: mism.append((len(H), fix,
                                     [Hh[d] for d in range(1, top)]))
    print(f"      conjugacy classes {len(classes)}; "
          f"[el F_2-acyclic in degrees 1..{top-1}] == [D fixed-type]: "
          f"{'ALL AGREE' if not mism else mism}")
