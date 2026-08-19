"""Structure of the tree8a/tree8b factorization witnesses (O20).

For each witness r (one-step type homotopy id ~ j o g):
 - the image vertex set and which stratum contains it;
 - the residual group res(P) of that stratum (signed perms of the
   plane in its 2 free coordinate classes);
 - whether r|_P is a bijection of P's vertices, and if so which
   element of res(P) it induces;
 - the type of res(P): common fixed cell (agreement stratum) or
   mixed (and reflection-generated?) -- i.e. the n=2 status of
   the reduced quotient P/res.

If r|_P is a bijection then P/res -> cube^4/N -> P/res composes
to an iso-class, so cube^4/N ~ P/res in BOTH structures, and the
class inherits the n=2 classification of res(P)."""
import sys, itertools
from collections import deque, Counter
sys.path.insert(0, 'scripts')
from strata_retract import build

n = 4
ELEMS, idx, ID, NE, MUL, INV, ACT = build(n)
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
def cyc(a):
    p, s = ELEMS[a]
    seen = [False]*n; out = []
    for i in range(n):
        if seen[i]: continue
        sg = s[i]; j = p[i]; seen[i] = True; ln = 1
        while j != i:
            seen[j] = True; ln += 1; sg ^= s[j]; j = p[j]
        out.append((ln, sg & 1))
    return tuple(sorted(out))
SIGS = {
 'tree8a': (8,  {((1,0),(1,0),(1,0),(1,0)):1, ((1,1),(1,1),(2,0)):2,
                 ((2,0),(2,0)):3, ((4,0),):2}),
 'tree8b': (8,  {((1,0),(1,0),(1,0),(1,0)):1,
                 ((1,0),(1,0),(1,1),(1,1)):1, ((1,0),(1,0),(2,0)):3,
                 ((1,1),(1,1),(2,0)):1, ((2,0),(2,0)):2}),
}
subs = {frozenset([ID]): []}
fr = list(subs.items())
while fr:
    new = []
    for H, gens in fr:
        for g in range(NE):
            if g in H: continue
            H2 = close(gens + [g])
            if H2 not in subs:
                subs[H2] = gens + [g]; new.append((H2, gens + [g]))
    fr = new
classes = {}
for H in subs:
    key = min(tuple(sorted(MUL[MUL[g][a]][INV[g]] for a in H))
              for g in range(NE))
    classes.setdefault(key, H)
found = {}
for H in classes.values():
    R = [a for a in H if REFL[a]]
    if not R or close(R) != H: continue
    if any(all(ACT[a][v] == v for a in R) for v in range(1 << n)): continue
    sig = (len(H), dict(Counter(cyc(a) for a in H)))
    for name, (sz, ct) in SIGS.items():
        if sig == (sz, ct): found[name] = sorted(H)

V = 1 << n
for name in sorted(found):
    N = found[name]
    print(f"\n### {name}  |N|={len(N)}", flush=True)
    # strata (maximal loci)
    loci = {}
    for a in N:
        if REFL[a]:
            L = frozenset(v for v in range(V) if ACT[a][v] == v)
            loci[L] = 1
    maximal = [L for L in loci if not any(L < L2 for L2 in loci)]
    # collect ALL witnesses (all c)
    orb_of = {}; reps = []
    for v in range(V):
        if v in orb_of: continue
        reps.append(v)
        for h in N: orb_of[ACT[h][v]] = v
    stab = {v: [h for h in N if ACT[h][v] == v] for v in reps}
    wits = []
    for c in N:
        ci = INV[c]
        allowed = []
        for v in reps:
            conj = [MUL[MUL[ci][h]][c] for h in stab[v]]
            allowed.append([w for w in range(V)
                            if all(ACT[g][w] == w for g in conj)])
        for choice in itertools.product(*allowed):
            r = [None]*V; ok = True
            for v, w in zip(reps, choice):
                for h in N:
                    tv = ACT[h][v]; tw = ACT[MUL[MUL[ci][h]][c]][w]
                    if r[tv] is None: r[tv] = tw
                    elif r[tv] != tw: ok = False; break
                if not ok: break
            if not ok: continue
            if not all(r[ACT[h][v]] == ACT[MUL[MUL[ci][h]][c]][r[v]]
                       for h in N for v in range(V)): continue
            stabs = [s for s in N if s != ID and
                     all(ACT[s][r[v]] == r[v] for v in range(V))]
            if stabs: wits.append((c, tuple(r)))
    print(f"witnesses: {len(wits)}")
    # analyze image structure
    kinds = Counter()
    best = {}
    for c, r in wits:
        img = frozenset(r)
        inP = [L for L in maximal if img <= L]
        onto = inP and img == inP[0] if inP else False
        bij = None; resel = None
        if inP:
            P = sorted(inP[0])
            restr = tuple(r[v] for v in P)
            bij = len(set(restr)) == len(P)
        kinds[(len(img), bool(inP), bool(onto and bij))] += 1
        if inP and onto and bij and (c,) not in best:
            best[(c,)] = (r, inP[0])
    print("witness kinds (|img|, img in a stratum, r|_P bijective):",
          dict(kinds))
    # pick a witness with bijective restriction if any
    for key, (r, P) in list(best.items())[:1]:
        Ps = sorted(P)
        setw = [g for g in N if frozenset(ACT[g][v] for v in P) == P]
        # residual as permutations of P's vertices
        res = sorted({tuple(ACT[g][v] for v in Ps) for g in setw})
        rP = tuple(r[v] for v in Ps)
        print(f"example: image = stratum {Ps}")
        print(f"  |setwise|={len(setw)}  |res|={len(res)}  "
              f"r|_P in res: {rP in res}")
        # classify res as signed 2-dim group: find the 2 free coords
        # pattern of P: which coordinate classes vary
        # (P = 4 vertices => 2 free directions); compute res's action
        # in terms of reflections/mixedness on those
        # mixedness: res (as subgroup of Sym(P)) has a common fixed
        # vertex? and reflection content: elements of setw that are
        # reflections of cube^4 restrict to 'reflections' of P
        common = [v for v in Ps
                  if all(ACT[g][v] == v for g in setw)]
        refl_in_res = sorted({tuple(ACT[g][v] for v in Ps)
                              for g in setw if REFL[g]})
        res_from_refl = None
        # subgroup of res generated by refl_in_res
        gen = {tuple(Ps.index(x) for x in t) for t in refl_in_res}
        idp = tuple(range(len(Ps)))
        S = {idp} | gen; dq = deque(S)
        def comp(a, b): return tuple(a[b[i]] for i in range(len(b)))
        while dq:
            x = dq.popleft()
            for y in list(S):
                for z in (comp(x, y), comp(y, x)):
                    if z not in S: S.add(z); dq.append(z)
        resperm = {tuple(Ps.index(x) for x in t) for t in res}
        print(f"  common fixed vertex of res: {common}")
        print(f"  reflections generate res: {S == resperm}  "
              f"(|<refl>|={len(S)}, |res|={len(resperm)})")
        # does res have a fixed vertex at all / which n=2 class?
        fixv = [v for v in Ps if all(t[Ps.index(v)] == v for t in res)]
        print(f"  res mixed (no common fixed vertex): {not fixv}")
