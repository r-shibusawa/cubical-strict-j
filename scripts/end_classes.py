"""End classes of the E-resolution collage: the last base-case ingredient
of the general-n nullity theorem (O18, section 79).

Set-up.  J = (cube^n x E_G)  u_i  (l_i x E_G x cube^1), the horn of the
maximal stratum l_i being collapsed at t=1 onto l_i, so the END part of
J/D is S/D with S = union of the maximal strata, a subpresheaf of cube^n.
A map W = cube^n/D -> J/D landing in the end part is a D-invariant class
of a cell of S, i.e. a cell phi of cube^n with image in some stratum l
together with a homomorphism delta : D -> D with

        phi . sigma_h  =  sigma_{delta(h)} . phi      (h in D).

On the Boolean site the cells of cube^m at level n are EXACTLY the maps
of vertex sets {0,1}^n -> {0,1}^m, so the system is exactly

        f : V_n -> V_l   with   f(sigma_h v) = sigma_{delta(h)} f(v),

i.e. a delta-equivariant map of vertex sets; and such an f exists iff for
every D-orbit representative v there is w in V_l fixed by
delta(Stab_D(v)).  (Boolean is the largest inversion site, so exclusion
here implies exclusion on the De Morgan and Kleene sites.)

If delta(D) lies in the pointwise stabiliser P_l of the stratum then
sigma_{delta(h)} acts as the identity on cells of l, so the cell is
STRICTLY invariant, factors through W -> l = cube^m, and the end class is
null (contract the representable by a connection and postcompose).

END EXCLUSION (to be tested): for D reflection-generated and mixed, every
delta admitting a delta-equivariant f has delta(D) contained in P_l.
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
    ACT = []
    for a in range(NE):
        p, s = ELEMS[a]
        ACT.append([sum(((((v >> p[i]) & 1) ^ s[i]) << i) for i in range(n))
                    for v in range(1 << n)])
    return ELEMS, idx, ID, NE, MUL, INV, ACT

def run(n, verbose=True):
    ELEMS, idx, ID, NE, MUL, INV, ACT = build(n)
    # action convention check: ACT[a*b] = ACT[a] o ACT[b] or ACT[b] o ACT[a]?
    conv = None
    for a in range(NE):
        for b in range(NE):
            l = [ACT[a][ACT[b][v]] for v in range(1 << n)]
            r = [ACT[b][ACT[a][v]] for v in range(1 << n)]
            if ACT[MUL[a][b]] == l: conv = 'ab = a o b' if conv in (None, 'ab = a o b') else 'mixed'
            elif ACT[MUL[a][b]] == r: conv = 'ab = b o a' if conv in (None, 'ab = b o a') else 'mixed'
            else: conv = 'none'
            break
        break
    def close(gens):
        S = {ID}; dq = deque([ID])
        while dq:
            x = dq.popleft()
            for g in gens:
                y = MUL[x][g]
                if y not in S: S.add(y); dq.append(y)
        return frozenset(S)
    REFL = []
    for a in range(NE):
        p, s = ELEMS[a]
        seen = [False]*n; ok = a != ID
        for i in range(n):
            if seen[i]: continue
            sg = s[i]; j = p[i]; seen[i] = True
            while j != i:
                seen[j] = True; sg ^= s[j]; j = p[j]
            if sg & 1: ok = False
        REFL.append(ok)
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
        key = min(tuple(sorted(MUL[MUL[g][a]][INV[g]] for a in H))
                  for g in range(NE))
        classes.setdefault(key, (H, gens))
    tgt = []
    for H, gens in classes.values():
        R = [a for a in H if REFL[a]]
        if not R: continue
        if any(all(ACT[a][v] == v for a in R) for v in range(1 << n)): continue
        if close(R) != H: continue
        tgt.append((sorted(H), gens))
    print(f"n={n} (convention: {conv}); reflection-generated mixed classes: "
          f"{len(tgt)}")
    total_bad = 0
    for H, gens in tgt:
        NV = 1 << n
        # maximal strata: vertex sets of fixed loci of reflections, maximal
        loci = {}
        for a in H:
            if not REFL[a]: continue
            L = frozenset(v for v in range(NV) if ACT[a][v] == v)
            loci.setdefault(L, []).append(a)
        maximal = [L for L in loci if not any(L < L2 for L2 in loci)]
        # generators of H (small set)
        gg = None
        for i, a in enumerate(H):
            for b in H[i:]:
                if len(close([a, b])) == len(H): gg = [a, b]; break
            if gg: break
        if gg is None:
            gg = []
            span = {ID}
            for a in H:
                if a in span: continue
                gg.append(a); span = set(close(gg))
                if len(span) == len(H): break
        word = {ID: []}
        dq = deque([ID])
        while dq:
            x = dq.popleft()
            for k, g in enumerate(gg):
                y = MUL[x][g]
                if y not in word: word[y] = word[x] + [k]; dq.append(y)
        # vertex orbits and stabilisers
        orbreps = []; seenv = [False]*NV
        for v in range(NV):
            if seenv[v]: continue
            for a in H: seenv[ACT[a][v]] = True
            orbreps.append(v)
        stabs = [[a for a in H if ACT[a][v] == v] for v in orbreps]
        bad = []
        for L in maximal:
            Ls = sorted(L)
            Nl = [a for a in H if {ACT[a][v] for v in Ls} == set(Ls)]
            Pl = [a for a in H if all(ACT[a][v] == v for v in Ls)]
            Plset = set(Pl)
            for imgs in itertools.product(Nl, repeat=len(gg)):
                d = {}
                for x in H:
                    y = ID
                    for k in word[x]: y = MUL[y][imgs[k]]
                    d[x] = y
                ok = all(d[MUL[a][b]] == MUL[d[a]][d[b]] for a in H for b in H)
                if not ok: continue
                # delta-equivariant f : V_n -> L, orbit by orbit; the cell
                # is STRICTLY invariant iff every chosen w is delta(D)-fixed
                # (then sigma_{delta(h)} o f = f), so a genuinely twisted
                # end class needs one orbit with a valid w that is NOT
                # delta(D)-fixed, and valid choices on all other orbits.
                choices = []
                for v, St in zip(orbreps, stabs):
                    ws = [w for w in Ls if all(ACT[d[a]][w] == w for a in St)]
                    choices.append(ws)
                if any(not ws for ws in choices): continue
                nonstrict = any(any(not all(ACT[d[x]][w] == w for x in H)
                                    for w in ws) for ws in choices)
                if nonstrict:
                    bad.append((len(L), sorted(set(d.values()))))
        if bad:
            total_bad += 1
            print(f"   |D|={len(H):3d}: END TWIST SURVIVES x{len(bad)} "
                  f"(e.g. |l|={bad[0][0]}, image size {len(bad[0][1])})")
    print(f"   groups with a surviving nontrivial end twist: {total_bad}"
          f" / {len(tgt)}")
    return total_bad

for n in (2, 3, 4):
    run(n)
