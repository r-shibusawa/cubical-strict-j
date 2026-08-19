"""Maximal-stratum data of a subgroup D <= B_n, for the general W1
theorem (O18, section 77).

For each reflection r (= element fixing a cell = all cycles even) the
fixed locus is the solution set of the parity system
    v_i = v_{p_r(i)} + s_r(i)   (a parity partition Pi(r) of the slots);
the locus is a parametrised subcube l_r : cube^{m} -> cube^n with
m = #blocks of Pi(r).  Loci are ordered by inclusion (coarser partition =
smaller locus), so the MAXIMAL strata are the minimal (finest) partitions
occurring.  For a maximal stratum l:
    N_l := { h in D : h(l) = l }        (setwise stabiliser),
    P_l := { h in D : h fixes l cellwise } = kernel of N_l -> Aut(l),
and the established el-model (section 40/41, calibrated in coho_ranks.py)
is
    el(cube^n/D)  ~  hocolim( +_i el(l_i/N_i)  <-  +_i B N_i  ->  B D )
over D-orbit representatives l_i of the maximal strata, with
el(l_i/N_i) itself a lower-dimensional instance (= B(N_i/P_i) when
N_i/P_i acts freely on the cells of l_i).

This script computes, for every reflection-generated mixed subgroup of
B_n (n <= 4), the maximal-stratum data together with the 2-ranks needed
by the Quillen growth argument.
"""
import itertools, sys
from collections import deque, Counter

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
    def cyc(e):
        p, s = e; seen = [False]*n; out = []
        for i in range(n):
            if seen[i]: continue
            sg = s[i]; j = p[i]; seen[i] = True; L = [i]
            while j != i:
                seen[j] = True; sg ^= s[j]; L.append(j); j = p[j]
            out.append((tuple(L), sg & 1))
        return out
    REFL = [a != ID and all(g == 0 for _, g in cyc(ELEMS[a]))
            for a in range(NE)]
    ACT = []
    for a in range(NE):
        p, s = ELEMS[a]
        ACT.append([sum(((((v >> p[i]) & 1) ^ s[i]) << i) for i in range(n))
                    for v in range(1 << n)])
    return ELEMS, idx, ID, NE, MUL, INV, REFL, ACT, cyc

def pattern(e, n, cyc):
    """slot -> (block, sign): the parametrisation of the fixed locus of a
    reflection e (signs propagated along each even cycle)."""
    pat = [None]*n
    p, s = e
    for j, (L, sg) in enumerate(cyc(e)):
        assert sg == 0
        i = L[0]; cur = 0
        for _ in range(len(L)):
            pat[i] = (j, cur); cur ^= s[i]; i = p[i]
    return tuple(pat)

def act_pattern(h, pat, n):
    """pattern of h.c for c of pattern pat: (h.c)(i) = ~^{s_i} c(p(i))"""
    p, s = h
    return tuple((pat[p[i]][0], pat[p[i]][1] ^ s[i]) for i in range(n))

def norm_pattern(pat, n):
    """canonical form: blocks renumbered by first occurrence, sign of the
    first slot of each block set to 0"""
    ren = {}; base = {}
    out = []
    for i in range(n):
        b, sg = pat[i]
        if b not in ren:
            ren[b] = len(ren); base[b] = sg
        out.append((ren[b], sg ^ base[b]))
    return tuple(out)

def run(n):
    ELEMS, idx, ID, NE, MUL, INV, REFL, ACT, cyc = build(n)
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

    def rank2(H):
        """maximal rank of an elementary abelian 2-subgroup"""
        invol = [a for a in H if a != ID and MUL[a][a] == ID]
        best = 0
        # greedy over all commuting subsets via BFS on generated subgroups
        seen = {frozenset([ID])}
        stack = [(frozenset([ID]), 0)]
        while stack:
            E, r = stack.pop()
            best = max(best, r)
            for a in invol:
                if a in E: continue
                if any(MUL[a][b] != MUL[b][a] for b in E): continue
                E2 = close(sorted(set(E) | {a}))
                if any(MUL[x][x] != ID for x in E2): continue
                if E2 in seen: continue
                seen.add(E2); stack.append((E2, r + 1))
        return best

    out = []
    for H in subs:
        R = [a for a in H if REFL[a]]
        if not R: continue
        if any(all(ACT[a][v] == v for a in R) for v in range(1 << n)):
            continue                                    # not mixed
        if close(R) != H: continue                      # not reflection-gen
        # maximal strata = finest parity partitions among reflections
        pats = {}
        for a in R:
            pt = norm_pattern(pattern(ELEMS[a], n, cyc), n)
            pats.setdefault(pt, []).append(a)
        def nblocks(pt): return len(set(b for b, _ in pt))
        mx = max(nblocks(pt) for pt in pats)
        maximal = [pt for pt in pats if nblocks(pt) == mx]
        # D-orbits of maximal strata
        orbs = []; left = set(maximal)
        while left:
            pt = next(iter(left)); orb = set()
            dq = deque([pt])
            while dq:
                q = dq.popleft()
                if q in orb: continue
                orb.add(q)
                for h in H:
                    q2 = norm_pattern(act_pattern(ELEMS[h], q, n), n)
                    if q2 not in orb: dq.append(q2)
            left -= orb; orbs.append(sorted(orb))
        data = []
        for orb in orbs:
            pt = orb[0]
            N = frozenset(h for h in H
                          if norm_pattern(act_pattern(ELEMS[h], pt, n), n) == pt)
            P = frozenset(h for h in H
                          if act_pattern(ELEMS[h], pt, n) == pt)
            data.append((len(orb), pt, N, P))
        out.append((H, mx, data))
    print(f"n={n}: reflection-generated mixed subgroups: {len(out)}")
    stat = Counter(); fails = []
    for H, mx, data in out:
        rD = rank2(H)
        ok = all(rank2(N) < rD for _, _, N, _ in data)
        stat[(len(data), ok)] += 1
        if not ok:
            fails.append((H, mx, data, rD))
    print(f"   (#orbits of maximal strata, rank2(N) < rank2(D) for ALL "
          f"orbits): {dict(sorted(stat.items()))}")
    print(f"   groups where some maximal stratum has rank2(N) = rank2(D): "
          f"{len(fails)}")
    shown = set()
    for H, mx, data, rD in fails:
        key = (len(H), rD, tuple(sorted((len(N), len(P), k)
                                        for k, _, N, P in data)))
        if key in shown: continue
        shown.add(key)
        print(f"      |D|={len(H):3d} rank2={rD} strata-dim={mx} "
              f"orbits={[(k, len(N), len(P), rank2(N)) for k, _, N, P in data]}"
              f"   (orbit size, |N|, |P|, rank2 N)")
    return out

for n in (2, 3, 4):
    run(n)
    print()


# ============================================================
# Quillen test for W1 (section 77):
#   el(W) acyclic  =>  (Mayer-Vietoris exactness at the middle term)
#   res : H^*(BD;F_p) -> (+)_i H^*(BN_i;F_p) is INJECTIVE
#   =>  (Quillen stratification) every elementary abelian p-subgroup of
#       D is conjugate INTO some maximal-stratum stabiliser N_i.
# So if some elementary abelian E <= D is conjugate into NO N_i, then
# el(W) is not F_p-acyclic and W1 holds.
# ============================================================
print("=" * 62)
print("Quillen test: is every elementary abelian 2-subgroup of D")
print("conjugate into some maximal-stratum stabiliser N_i?")
for n in (2, 3, 4):
    ELEMS, idx, ID, NE, MUL, INV, REFL, ACT, cyc = build(n)
    def close(gens):
        S = {ID}; dq = deque([ID])
        while dq:
            x = dq.popleft()
            for g in gens:
                y = MUL[x][g]
                if y not in S: S.add(y); dq.append(y)
        return frozenset(S)
    data = run(n) if False else None
    # recompute (run() already printed; redo silently)
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
    covered = 0; witnessed = 0; wit_examples = []
    for H in subs:
        R = [a for a in H if REFL[a]]
        if not R: continue
        if any(all(ACT[a][v] == v for a in R) for v in range(1 << n)):
            continue
        if close(R) != H: continue
        pats = {}
        for a in R:
            pt = norm_pattern(pattern(ELEMS[a], n, cyc), n)
            pats.setdefault(pt, []).append(a)
        mx = max(len(set(b for b, _ in pt)) for pt in pats)
        maximal = [pt for pt in pats if len(set(b for b, _ in pt)) == mx]
        Ns = []
        seen_orb = set()
        for pt in maximal:
            if pt in seen_orb: continue
            orb = set(); dq = deque([pt])
            while dq:
                q = dq.popleft()
                if q in orb: continue
                orb.add(q)
                for h in H:
                    dq.append(norm_pattern(act_pattern(ELEMS[h], q, n), n))
            seen_orb |= orb
            Ns.append(frozenset(h for h in H
                      if norm_pattern(act_pattern(ELEMS[h], pt, n), n) == pt))
        # elementary abelian 2-subgroups of H
        invol = [a for a in H if a != ID and MUL[a][a] == ID]
        elabs = set()
        stack = [frozenset([ID])]
        while stack:
            E = stack.pop()
            for a in invol:
                if a in E: continue
                if any(MUL[a][b] != MUL[b][a] for b in E): continue
                E2 = close(sorted(set(E) | {a}))
                if any(MUL[x][x] != ID for x in E2): continue
                if E2 in elabs: continue
                elabs.add(E2); stack.append(E2)
        bad = None
        for E in elabs:
            if not any(frozenset(MUL[MUL[g][a]][INV[g]] for a in E) <= N
                       for N in Ns for g in H):
                bad = E; break
        if bad is None: covered += 1
        else:
            witnessed += 1
            if len(wit_examples) < 4:
                wit_examples.append((len(H), len(bad), len(Ns)))
    print(f"  n={n}: reflection-generated mixed groups: "
          f"{covered + witnessed};  W1 by Quillen (some elementary abelian "
          f"misses every N_i): {witnessed};  fully covered: {covered}")
    if wit_examples:
        print(f"        examples (|D|, |E|, #orbits): {wit_examples}")
