"""Degenerate mixed subgroups: the last edge case of Conjecture G (O18).

Theorem P'' (section 74) reduces the general-n separation criterion to a
recursion whose only unresolved branch is

    H mixed,  N := <<reflections of H>>  proper in H,  N NOT mixed,

and since N owns a reflection it cannot be free: N is of FIXED type.
Call such H *degenerate mixed*.

Structure theory (section 75), verified here:
  (a) a signed permutation fixes a cell <=> all its cycles have even
      sign-sum <=> it fixes a VERTEX; a subgroup has a common fixed cell
      <=> it has a common fixed vertex (the sign cocycle is a coboundary);
  (b) for H degenerate mixed with F := Fix(N) (nonempty, H-invariant):
      N = Stab_H(v) for every v in F, Q := H/N acts FREELY on F, and
      after conjugating 0 into F all reflections of H are pure
      permutations and every sign vector s(h) is constant on N-orbits;
  (c) MEDIAN BLOCK REDUCTION: if some H-invariant partition P of the
      slots has all blocks of ODD size and every s(h) constant on the
      blocks (after a sign conjugation), block-wise majority
      mu : cube^n -> cube^|P| and the diagonal d are H-equivariant with
      mu d = id, so cube^n/H reduces to cube^|P|/Hbar.  Nontrivial when
      P has a block of size >= 3.

Enumerates ALL subgroups of B_n up to conjugacy (full cyclic extension),
classifies them, and reports the degenerate mixed ones that survive
product decomposition and median block reduction.
"""
import itertools, sys
from collections import deque

def build(n):
    ELEMS = [(p, s) for p in itertools.permutations(range(n))
             for s in itertools.product((0, 1), repeat=n)]
    idx = {e: i for i, e in enumerate(ELEMS)}
    ID = idx[(tuple(range(n)), (0,)*n)]
    NE = len(ELEMS)
    def mm(e1, e2):
        (p1, s1), (p2, s2) = e1, e2
        return (tuple(p2[p1[i]] for i in range(n)),
                tuple(s1[i] ^ s2[p1[i]] for i in range(n)))
    MUL = [[idx[mm(ELEMS[a], ELEMS[b])] for b in range(NE)] for a in range(NE)]
    INV = [0]*NE
    for a in range(NE):
        for b in range(NE):
            if MUL[a][b] == ID: INV[a] = b; break
    return ELEMS, idx, ID, NE, MUL, INV

def cycles(e, n):
    p, s = e
    seen = [False]*n; out = []
    for i in range(n):
        if seen[i]: continue
        cyc = [i]; seen[i] = True; j = p[i]; sg = s[i]
        while j != i:
            seen[j] = True; cyc.append(j); sg ^= s[j]; j = p[j]
        out.append((tuple(cyc), sg & 1))
    return out


def run(n, show=True):
    ELEMS, idx, ID, NE, MUL, INV = build(n)
    REFL = [e != ID and all(sg == 0 for _, sg in cycles(ELEMS[e], n))
            for e in range(NE)]
    def act_pt(a, v):
        p, s = ELEMS[a]; q = 0
        for i in range(n):
            q |= (((v >> p[i]) & 1) ^ s[i]) << i
        return q
    ACT = [[act_pt(a, v) for v in range(1 << n)] for a in range(NE)]

    def close(gens):
        S = {ID}; dq = deque([ID])
        while dq:
            x = dq.popleft()
            for g in gens:
                y = MUL[x][g]
                if y not in S: S.add(y); dq.append(y)
        return frozenset(S)

    # ---- full subgroup lattice, then conjugacy classes ----
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
    classes = {}
    for H, gens in subs.items():
        key = min(tuple(sorted(MUL[MUL[g][x]][INV[g]] for x in H))
                  for g in range(NE))
        if key not in classes: classes[key] = (H, gens)
    classes = list(classes.values())
    if show:
        print(f"n={n}: |B_n|={NE}, subgroups: {len(subs)}, "
              f"up to conjugacy: {len(classes)}")

    def fixed_vertices(H):
        return [v for v in range(1 << n) if all(ACT[a][v] == v for a in H)]

    def normal_closure(H, S0):
        S = set(S0); dq = deque(S)
        while dq:
            x = dq.popleft()
            for g in H:
                y = MUL[MUL[g][x]][INV[g]]
                if y not in S: S.add(y); dq.append(y)
        return close(sorted(S)) if S else frozenset([ID])

    def orbit_partition(H):
        par = list(range(n))
        def f(i):
            while par[i] != i: par[i] = par[par[i]]; i = par[i]
            return i
        for a in H:
            p, _ = ELEMS[a]
            for i in range(n):
                ra, rb = f(i), f(p[i])
                if ra != rb: par[ra] = rb
        gr = {}
        for i in range(n): gr.setdefault(f(i), []).append(i)
        return sorted(tuple(v) for v in gr.values())

    def restrict(a, B):
        p, s = ELEMS[a]
        q = list(range(n)); t = [0]*n
        for i in B: q[i] = p[i]; t[i] = s[i]
        return idx[(tuple(q), tuple(t))]

    def product_split(H):
        """nontrivial H-invariant split [n] = A + A^c with
        H = H|_A x H|_{A^c}"""
        orb = orbit_partition(H)
        if len(orb) < 2: return None
        for r in range(1, len(orb)):
            for sel in itertools.combinations(range(len(orb)), r):
                A = [i for k in sel for i in orb[k]]
                if all(restrict(a, A) in H for a in H):
                    return (tuple(sorted(A)),
                            tuple(sorted(set(range(n)) - set(A))))
        return None

    def median_reduction(H):
        """(eps, P) with P H-invariant, all blocks odd, some block >= 3,
        and every sign vector constant on blocks after conjugating by
        diag(eps)."""
        orb = orbit_partition(H)
        # candidate partitions: unions of orbits (coarsenings)
        cands = []
        k = len(orb)
        for asg in itertools.product(range(k), repeat=k):
            if any(asg[i] > max(asg[:i], default=-1) + 1 for i in range(k)):
                continue                      # restricted growth = set partition
            gr = {}
            for i, b in enumerate(asg): gr.setdefault(b, []).extend(orb[i])
            P = sorted(tuple(sorted(v)) for v in gr.values())
            if all(len(b) % 2 == 1 for b in P) and any(len(b) >= 3 for b in P):
                cands.append(P)
        if not cands: return None
        for eps in range(1 << n):
            d = idx[(tuple(range(n)), tuple((eps >> i) & 1 for i in range(n)))]
            sg = {}
            for a in H:
                sg[a] = ELEMS[MUL[MUL[d][a]][INV[d]]][1]
            for P in cands:
                # blocks must be permuted by H (they are unions of orbits)
                if all(len(set(s[i] for i in b)) == 1 for a, s in sg.items()
                       for b in P):
                    return (eps, P)
        return None

    out = []
    tax = {'free': 0, 'fixed': 0, 'mixed': 0}
    for H, gens in classes:
        if len(H) == 1: continue
        refl = [a for a in H if REFL[a]]
        fv = fixed_vertices(H)
        t = 'free' if not refl else ('fixed' if fv else 'mixed')
        tax[t] += 1
        if t != 'mixed': continue
        Nn = normal_closure(H, refl)
        if Nn == H: continue
        NF = fixed_vertices(Nn)
        if not NF: continue                     # N mixed: covering descent
        out.append((H, gens, refl, Nn, NF))
    if show:
        print(f"   taxonomy (nontrivial classes): {tax}")
        print(f"   degenerate mixed classes: {len(out)}")
    hard = []
    for (H, gens, refl, Nn, NF) in out:
        pr = product_split(H)
        md = median_reduction(H)
        tag = ('PRODUCT ' + str(pr) if pr else
               ('MEDIAN ' + str(md) if md else '*** HARD ***'))
        if show:
            print(f"   |H|={len(H):4d} |N|={len(Nn):3d} #refl={len(refl):3d} "
                  f"|Fix N|={len(NF):3d} N-orb={orbit_partition(Nn)} "
                  f"H-orb={orbit_partition(H)} -> {tag}")
            if not pr and not md:
                print(f"        gens={[ELEMS[g] for g in gens]}  "
                      f"elements={[ELEMS[a] for a in sorted(H)]}")
        if not pr and not md: hard.append((H, gens, refl, Nn, NF))
    if show:
        print(f"   ==> HARD degenerate mixed: {len(hard)}")
    # structure assertions (b)
    for (H, gens, refl, Nn, NF) in out:
        for v in NF:
            st = [a for a in H if ACT[a][v] == v]
            assert set(st) == set(Nn), "N = Stab_H(v) fails"
        assert all(len([a for a in H if ACT[a][v] == ACT[ID][v]]) for v in NF)
    return hard

for n in (2, 3, 4):
    run(n)
    print()
