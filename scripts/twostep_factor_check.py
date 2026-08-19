"""Two-step sieve-factorization search (O20) for the four
frontier classes with no one-step witness (orders 24, 16, 32,
192 at n=4).

A two-step chain id ~ F ~ r consists of:
  step 1: F is c-twisted equivariant for some c in N
          (F o sigma_h = sigma_{c^-1 h c} o F) -- forced shape;
  step 2: a cylinder with slices (F, r') sharing deck elements:
          forall h exists d in D_F(h) cap D_{r'}(h), where
          D_G(h) := {d : G o sigma_h = sigma_d o G pointwise};
  r' stabilized (lands in the sieve).

If every D_F(h) is the singleton {c^-1 h c} the chain collapses
to the one-step case (already excluded), so only F with deck
freedom (some |D_F(h)| > 1, i.e. non-injective F) can help.
For such F we search r' by choosing deck values on a generating
set and propagating over vertex orbits."""
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
 'tree24': (24, {((1,0),(1,0),(1,0),(1,0)):1, ((1,1),(1,1),(2,0)):6,
                 ((1,0),(3,0)):8, ((2,0),(2,0)):3, ((4,0),):6}),
 'circ16': (16, {((1,0),(1,0),(1,0),(1,0)):1, ((1,0),(1,0),(1,1),(1,1)):2,
                 ((1,1),(1,1),(1,1),(1,1)):1, ((1,0),(1,0),(2,0)):4,
                 ((1,1),(1,1),(2,0)):4, ((2,0),(2,0)):4}),
 'wedge32':(32, {((1,0),(1,0),(1,0),(1,0)):1, ((1,0),(1,0),(1,1),(1,1)):2,
                 ((1,1),(1,1),(1,1),(1,1)):1, ((1,0),(1,0),(2,0)):4,
                 ((1,1),(1,1),(2,0)):4, ((2,0),(2,0)):8,
                 ((2,1),(2,1)):4, ((4,0),):8}),
 'sph192': (192,{((1,0),(1,0),(1,0),(1,0)):1, ((1,0),(1,0),(1,1),(1,1)):6,
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
    classes.setdefault(key, (H, subs[H]))
found = {}
for H, gens in classes.values():
    R = [a for a in H if REFL[a]]
    if not R or close(R) != H: continue
    if any(all(ACT[a][v] == v for a in R) for v in range(1 << n)): continue
    sig = (len(H), dict(Counter(cyc(a) for a in H)))
    for name, (sz, ct) in SIGS.items():
        if sig == (sz, ct): found[name] = (sorted(H), gens)
print("matched:", sorted(found), flush=True)

V = 1 << n
def enum_twisted(N, stab, reps, c):
    """all c-twisted equivariant F, as value tuples on V"""
    ci = INV[c]
    allowed = []
    for v in reps:
        conj = [MUL[MUL[ci][h]][c] for h in stab[v]]
        allowed.append([w for w in range(V)
                        if all(ACT[g][w] == w for g in conj)])
    out = []
    for choice in itertools.product(*allowed):
        F = [None]*V; ok = True
        for v, w in zip(reps, choice):
            for h in N:
                tv = ACT[h][v]; tw = ACT[MUL[MUL[ci][h]][c]][w]
                if F[tv] is None: F[tv] = tw
                elif F[tv] != tw: ok = False; break
            if not ok: break
        if ok and all(F[ACT[h][v]] == ACT[MUL[MUL[ci][h]][c]][F[v]]
                      for h in N for v in range(V)):
            out.append(tuple(F))
    return out

for name in sorted(found):
    N, gens = found[name]
    orb_of = {}; reps = []
    for v in range(V):
        if v in orb_of: continue
        reps.append(v)
        for h in N: orb_of[ACT[h][v]] = v
    stab = {v: [h for h in N if ACT[h][v] == v] for v in reps}
    print(f"\n### {name} |N|={len(N)} gens={len(gens)}", flush=True)
    # collect all F with deck freedom
    total_F = 0; free_F = []
    for c in N:
        for F in enum_twisted(N, stab, reps, c):
            total_F += 1
            D = {}
            free = False
            okF = True
            for h in N:
                Fh = tuple(F[ACT[h][v]] for v in range(V))
                Dh = [d for d in N
                      if all(ACT[d][F[v]] == Fh[v] for v in range(V))]
                if not Dh: okF = False; break
                D[h] = Dh
                if len(Dh) > 1: free = True
            if okF and free:
                free_F.append((F, D))
    print(f"  twisted-equivariant F: {total_F}, with deck freedom: "
          f"{len(free_F)}", flush=True)
    hit = None
    seenF = set()
    for F, D in free_F:
        if F in seenF: continue
        seenF.add(F)
        # search r': choose d(g) on generators, propagate on orbits
        for dchoice in itertools.product(*[D.get(g, [None])
                                           for g in gens]):
            if None in dchoice: break
            # propagate r' over each vertex orbit from rep value
            for choice in itertools.product(range(V), repeat=len(reps)):
                r = [None]*V; ok = True
                for v, w in zip(reps, choice):
                    if r[v] is None: r[v] = w
                    elif r[v] != w: ok = False
                if not ok: continue
                # BFS closure under generators
                dq = deque(reps)
                while dq and ok:
                    v = dq.popleft()
                    for g, d in zip(gens, dchoice):
                        tv = ACT[g][v]; tw = ACT[d][r[v]]
                        if r[tv] is None:
                            r[tv] = tw; dq.append(tv)
                        elif r[tv] != tw: ok = False; break
                if not ok or any(x is None for x in r): continue
                # full shared-deck check + stabilized
                if not all(any(all(ACT[d][r[v]] == r[ACT[h][v]]
                                   for v in range(V)) and d in D[h]
                               for d in N) for h in N):
                    continue
                if not any(s != ID and
                           all(ACT[s][r[v]] == r[v] for v in range(V))
                           for s in N):
                    continue
                hit = (F, r, dchoice); break
            if hit: break
        if hit: break
    if hit:
        F, r, dc = hit
        print(f"  TWO-STEP FACTORIZATION FOUND: |im F|="
              f"{len(set(F))}, |im r|={len(set(r))}", flush=True)
    else:
        print(f"  no two-step factorization "
              f"(searched {len(seenF)} deck-free F)", flush=True)
