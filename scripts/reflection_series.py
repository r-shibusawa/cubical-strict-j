"""The reflection-derived series and the closed-form separation criterion.

Definition.  For H <= B_n put R(H) = { h in H : h fixes a cell }
(equivalently every cycle of h has even sign-sum, equivalently h fixes a
vertex), and D(H) := << R(H) >>_H, the normal closure of R(H) IN H.
The *reflection-derived series* is H = M_0 > M_1 > ... with
M_{i+1} = D(M_i); it stabilises at M_oo(H) = the largest
reflection-generated "core".

CRITERION (G-sharp):   cube^n / H  separates  <=>  M_oo(H) is MIXED
(i.e. M_oo has a reflection but no common fixed vertex).

Rationale.  (i) M_oo is reflection-generated, hence certified by
Theorem P''; (ii) each step M_{i+1} <| M_i contains all reflections of
M_i, so M_i / M_{i+1} acts freely on the cells of cube^n / M_{i+1} and
the collage map descends: Phi_{M_i} = Phi_{M_{i+1}} / (M_i/M_{i+1}),
a quotient of a free action on both sides, so it is a type weak
equivalence iff Phi_{M_{i+1}} is (up: free quotients preserve weak
equivalences between free objects; down: covering Lemma C of section 67).

This script tests the criterion against the complete De Morgan n = 3
classification of paper 14 (78 AGREE / 20 SEP over the 98 subgroups of
B_3) and prints the general census for n <= 4.
"""
import itertools
from collections import deque

def tools(n):
    ELEMS = [(p, s) for p in itertools.permutations(range(n))
             for s in itertools.product((0, 1), repeat=n)]
    ID = (tuple(range(n)), (0,)*n)
    def mm(e1, e2):
        (p1, s1), (p2, s2) = e1, e2
        return (tuple(p2[p1[i]] for i in range(n)),
                tuple(s1[i] ^ s2[p1[i]] for i in range(n)))
    def inv(e):
        p, s = e
        q = [0]*n; t = [0]*n
        for i in range(n): q[p[i]] = i
        for i in range(n): t[i] = s[q[i]]
        return (tuple(q), tuple(t))
    def cyc(e):
        p, s = e; seen = [False]*n; out = []
        for i in range(n):
            if seen[i]: continue
            sg = s[i]; j = p[i]; seen[i] = True; L = 1
            while j != i:
                seen[j] = True; sg ^= s[j]; j = p[j]; L += 1
            out.append((L, sg & 1))
        return out
    def refl(e):
        return e != ID and all(sg == 0 for _, sg in cyc(e))
    def close(gens):
        S = {ID} | set(gens); dq = deque(S)
        while dq:
            x = dq.popleft()
            for g in list(S):
                for y in (mm(x, g), mm(g, x)):
                    if y not in S: S.add(y); dq.append(y)
        return frozenset(S)
    def act(e, v):
        p, s = e; q = 0
        for i in range(n): q |= (((v >> p[i]) & 1) ^ s[i]) << i
        return q
    return ELEMS, ID, mm, inv, refl, close, act

def analyse(n):
    ELEMS = [(p, s) for p in itertools.permutations(range(n))
             for s in itertools.product((0, 1), repeat=n)]
    idx = {e: i for i, e in enumerate(ELEMS)}
    NE = len(ELEMS)
    IDe = (tuple(range(n)), (0,)*n)
    ID = idx[IDe]
    def mmr(e1, e2):
        (p1, s1), (p2, s2) = e1, e2
        return (tuple(p2[p1[i]] for i in range(n)),
                tuple(s1[i] ^ s2[p1[i]] for i in range(n)))
    MUL = [[idx[mmr(ELEMS[a], ELEMS[b])] for b in range(NE)]
           for a in range(NE)]
    INV = [0]*NE
    for a in range(NE):
        for b in range(NE):
            if MUL[a][b] == ID: INV[a] = b; break
    def cyc(e):
        p, s = e; seen = [False]*n; out = []
        for i in range(n):
            if seen[i]: continue
            sg = s[i]; j = p[i]; seen[i] = True; L = 1
            while j != i:
                seen[j] = True; sg ^= s[j]; j = p[j]; L += 1
            out.append((L, sg & 1))
        return out
    REFL = [a != ID and all(sg == 0 for _, sg in cyc(ELEMS[a]))
            for a in range(NE)]
    def close(gens):
        S = {ID}; dq = deque([ID])
        while dq:
            x = dq.popleft()
            for g in gens:
                y = MUL[x][g]
                if y not in S: S.add(y); dq.append(y)
        return frozenset(S)
    ACT = []
    for a in range(NE):
        p, s = ELEMS[a]
        ACT.append([sum(((((v >> p[i]) & 1) ^ s[i]) << i)
                        for i in range(n)) for v in range(1 << n)])
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
    def fixed_vertices(H):
        return [v for v in range(1 << n) if all(ACT[a][v] == v for a in H)]
    memoD = {}
    def D(H):
        if H in memoD: return memoD[H]
        R = [a for a in H if REFL[a]]
        if not R:
            memoD[H] = frozenset([ID]); return memoD[H]
        S = set(R); dq = deque(S)
        while dq:
            x = dq.popleft()
            for g in H:
                y = MUL[MUL[g][x]][INV[g]]
                if y not in S: S.add(y); dq.append(y)
        memoD[H] = close(sorted(S)); return memoD[H]
    def core(H):
        chain = [H]
        while True:
            M = D(chain[-1])
            if M == chain[-1]: return M, chain
            chain.append(M)
    def kind(H):
        if len(H) == 1: return 'trivial'
        if not any(REFL[a] for a in H): return 'free'
        return 'fixed' if fixed_vertices(H) else 'mixed'
    res = {}
    for H in subs:
        M, chain = core(H)
        res[H] = ('SEP' if kind(M) == 'mixed' else 'AGREE', M, len(chain))
    return subs, res, kind, fixed_vertices, ELEMS, ID, MUL, INV, REFL, close

for n in (1, 2, 3, 4):
    subs, res, kind, fixv, ELEMS, ID, MUL, INV, REFL, close = analyse(n)
    sep = [H for H in subs if res[H][0] == 'SEP']
    agree = [H for H in subs if res[H][0] == 'AGREE']
    print(f"n={n}: subgroups={len(subs)}  AGREE={len(agree)}  SEP={len(sep)}")
    from collections import Counter
    print("      SEP order distribution:",
          dict(sorted(Counter(len(H) for H in sep).items())))
    print("      taxonomy:",
          dict(sorted(Counter(kind(H) for H in subs).items())))
    steps = Counter(res[H][2] for H in subs)
    print("      derived-series length (1 = already stable):",
          dict(sorted(steps.items())))
    print("      groups whose core is a PROPER nontrivial fixed-type "
          "subgroup (the degenerate branch):",
          sum(1 for H in subs
              if res[H][0] == 'AGREE' and 1 < len(res[H][1]) < len(H)))
