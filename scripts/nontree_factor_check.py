"""One-step sieve-factorization / dimension-reduction search for
the three NON-tree frontier classes (orders 16, 32, 192) at n=4
(O20).  Same engine as tree_factor_check.py; additionally
analyzes witness structure (single-stratum image, bijective
restriction, residual type) to detect dimension reduction."""
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
 'circ16':  (16, {((1,0),(1,0),(1,0),(1,0)):1, ((1,0),(1,0),(1,1),(1,1)):2,
                  ((1,1),(1,1),(1,1),(1,1)):1, ((1,0),(1,0),(2,0)):4,
                  ((1,1),(1,1),(2,0)):4, ((2,0),(2,0)):4}),
 'wedge32': (32, {((1,0),(1,0),(1,0),(1,0)):1, ((1,0),(1,0),(1,1),(1,1)):2,
                  ((1,1),(1,1),(1,1),(1,1)):1, ((1,0),(1,0),(2,0)):4,
                  ((1,1),(1,1),(2,0)):4, ((2,0),(2,0)):8,
                  ((2,1),(2,1)):4, ((4,0),):8}),
 'sph192':  (192,{((1,0),(1,0),(1,0),(1,0)):1, ((1,0),(1,0),(1,1),(1,1)):6,
                  ((1,1),(1,1),(1,1),(1,1)):1, ((1,0),(1,0),(2,0)):12,
                  ((1,0),(1,1),(2,1)):24, ((1,1),(1,1),(2,0)):12,
                  ((1,0),(3,0)):32, ((1,1),(3,1)):32, ((2,0),(2,0)):12,
                  ((2,1),(2,1)):12, ((4,0),):48}),
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
print("matched:", sorted(found), flush=True)

V = 1 << n
for name in sorted(found):
    N = found[name]
    loci = {}
    for a in N:
        if REFL[a]:
            L = frozenset(v for v in range(V) if ACT[a][v] == v)
            loci[L] = 1
    maximal = [L for L in loci if not any(L < L2 for L2 in loci)]
    orb_of = {}; reps = []
    for v in range(V):
        if v in orb_of: continue
        reps.append(v)
        for h in N: orb_of[ACT[h][v]] = v
    stab = {v: [h for h in N if ACT[h][v] == v] for v in reps}
    print(f"\n### {name} |N|={len(N)} orbits={len(reps)}", flush=True)
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
    if not wits:
        print("  no one-step factorization", flush=True)
        continue
    kinds = Counter()
    example = None
    for c, r in wits:
        img = frozenset(r)
        inP = [L for L in maximal if img <= L]
        bij = False
        if inP:
            P = sorted(inP[0])
            restr = [r[v] for v in P]
            bij = len(set(restr)) == len(set(P) & set(restr)) and \
                  set(restr) == set(P)
        kinds[(len(img), bool(inP), bij)] += 1
        if inP and bij and example is None:
            example = (c, r, sorted(inP[0]))
    print(f"  ONE-STEP FACTORIZATION: {len(wits)} witnesses; kinds "
          f"(|img|, in-stratum, r|_P onto P): {dict(kinds)}", flush=True)
    if example:
        c, r, Ps = example
        setw = [g for g in N if frozenset(ACT[g][v] for v in Ps)
                == frozenset(Ps)]
        res = sorted({tuple(ACT[g][v] for v in Ps) for g in setw})
        rP = tuple(r[v] for v in Ps)
        common = [v for v in Ps if all(t[Ps.index(v)] == v for t in res)]
        refl_res = {tuple(ACT[g][v] for v in Ps) for g in setw if REFL[g]}
        idp = tuple(Ps)
        S = {idp} | refl_res; dq = deque(S)
        pos = {v: i for i, v in enumerate(Ps)}
        def comp(a, b): return tuple(a[pos[b[i]]] for i in range(len(b)))
        while dq:
            x = dq.popleft()
            for y in list(S):
                for z in (comp(x, y), comp(y, x)):
                    if z not in S: S.add(z); dq.append(z)
        print(f"  reduction example: P={Ps} |res|={len(res)} "
              f"r|_P in res: {rP in res} common fixed: {common} "
              f"refl generate res: {S == set(res)}", flush=True)
