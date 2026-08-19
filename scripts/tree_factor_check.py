"""Type-side stage-zero decision for the three tree-arrangement
frontier classes (O20): does the identity of cube^4/N factor
through the sieve Sigma/N by a ONE-STEP strict invariant homotopy
on the Boolean site?

Setup.  A strict endomorphism of cube^4/N at stage zero is a
vertex function F: V -> V (V = {0,1}^4; on the Boolean site a
level-4 cell IS an arbitrary vertex function, and every cell of a
product factors through the generic cell) subject to the deck
condition: forall h in N exists d in N with F o sigma_h =
sigma_d o F pointwise.  A one-step invariant homotopy is a map
(cube^4/N) x cube^1 -> cube^4/N, i.e. a pair of slices sharing
the SAME deck element d(h).  Taking slice 0 = sigma_a
(representing the identity class), d(h) = a h a^{-1} is forced
(sigma_a is a bijection), so slice 1 = sigma_b o r satisfies

    r o sigma_h = sigma_{c^{-1} h c} o r   (c := a^{-1} b in N),

a c-twisted equivariant map.  The homotopy lands in the sieve iff
r is a stabilized cell: exists s != 1 with sigma_s o r = r.

Search: for each c in N, r is determined by its values on vertex
orbit representatives, with r(v) in Fix(c^{-1} Stab(v) c);
enumerate all choices, extend equivariantly, verify, and test the
stabilizer condition.  A hit is an unconditional YES (the
factorization exists); no hit means no ONE-step homotopy (deeper
chains are a separate question).
"""
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

SIGS = {   # the three tree classes, by (|D|, cycle-type counter)
 'tree8a': (8,  {((1,0),(1,0),(1,0),(1,0)):1, ((1,1),(1,1),(2,0)):2,
                 ((2,0),(2,0)):3, ((4,0),):2}),
 'tree8b': (8,  {((1,0),(1,0),(1,0),(1,0)):1,
                 ((1,0),(1,0),(1,1),(1,1)):1, ((1,0),(1,0),(2,0)):3,
                 ((1,1),(1,1),(2,0)):1, ((2,0),(2,0)):2}),
 'tree24': (24, {((1,0),(1,0),(1,0),(1,0)):1, ((1,1),(1,1),(2,0)):6,
                 ((1,0),(3,0)):8, ((2,0),(2,0)):3, ((4,0),):6}),
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
        if sig == (sz, ct):
            found[name] = sorted(H)
print("matched:", sorted(found), flush=True)

V = 1 << n
for name in sorted(found):
    N = found[name]
    # vertex orbits + stabilizers
    orb_of = {}; reps = []
    for v in range(V):
        if v in orb_of: continue
        reps.append(v)
        for h in N: orb_of[ACT[h][v]] = (v, )
    stab = {v: [h for h in N if ACT[h][v] == v] for v in reps}
    print(f"\n{name}: |N|={len(N)}  vertex orbits={len(reps)} "
          f"(sizes {[sum(1 for w in range(V) if orb_of[w][0]==v) for v in reps]})",
          flush=True)
    hits = []
    for c in N:
        ci = INV[c]
        # allowed values per rep: Fix(c^{-1} Stab(v) c)
        allowed = []
        for v in reps:
            conj = [MUL[MUL[ci][h]][c] for h in stab[v]]
            allowed.append([w for w in range(V)
                            if all(ACT[g][w] == w for g in conj)])
        for choice in itertools.product(*allowed):
            r = [None]*V
            ok = True
            for v, w in zip(reps, choice):
                for h in N:
                    tv, tw = ACT[h][v], ACT[MUL[MUL[ci][h]][c]][w]
                    if r[tv] is None: r[tv] = tw
                    elif r[tv] != tw: ok = False; break
                if not ok: break
            if not ok: continue
            # verify twisted equivariance completely
            if not all(r[ACT[h][v]] == ACT[MUL[MUL[ci][h]][c]][r[v]]
                       for h in N for v in range(V)):
                continue
            stabs = [s for s in N if s != ID and
                     all(ACT[s][r[v]] == r[v] for v in range(V))]
            if stabs:
                hits.append((c, tuple(r), stabs[0]))
    if hits:
        c, r, s0 = hits[0]
        img = sorted(set(r))
        print(f"  ONE-STEP FACTORIZATION EXISTS: {len(hits)} witnesses; "
              f"e.g. c={ELEMS[c]}, |image|={len(img)}, "
              f"stabilized by {ELEMS[s0]}", flush=True)
    else:
        print(f"  no one-step factorization (all c in N exhausted)",
              flush=True)
