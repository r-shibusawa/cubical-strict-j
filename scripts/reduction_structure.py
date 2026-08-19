"""Machine verification of the reduction-structure theorem (O20)
on the two (R)-classes at n=4:
  (i)   S := Stab(F) is normalized by N, for every witness F;
  (ii)  im F lies in Fix(S), which is N-invariant;
  (iii) some power F^k restricts to a bijection of T := im F^k,
        and T is N-invariant;
  (iv)  the induced action of N on T is fixed-point-free (auto
        from mixedness), and its image M in Sym(T) is generated
        by elements WITH fixed points on T (recursion input is
        again 'reflection-generated mixed' in the E(T)-sense).
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
    orb_of = {}; reps = []
    for v in range(V):
        if v in orb_of: continue
        reps.append(v)
        for h in N: orb_of[ACT[h][v]] = v
    stab = {v: [h for h in N if ACT[h][v] == v] for v in reps}
    ok_norm = ok_fix = ok_pow = ok_gen = True
    checked = 0
    for c in N:
        ci = INV[c]
        allowed = []
        for v in reps:
            conj = [MUL[MUL[ci][h]][c] for h in stab[v]]
            allowed.append([w for w in range(V)
                            if all(ACT[g][w] == w for g in conj)])
        for choice in itertools.product(*allowed):
            F = [None]*V; ok = True
            for v, w in zip(reps, choice):
                for h in N:
                    tv = ACT[h][v]; tw = ACT[MUL[MUL[ci][h]][c]][w]
                    if F[tv] is None: F[tv] = tw
                    elif F[tv] != tw: ok = False; break
                if not ok: break
            if not ok: continue
            if not all(F[ACT[h][v]] == ACT[MUL[MUL[ci][h]][c]][F[v]]
                       for h in N for v in range(V)): continue
            S = [s for s in N if all(ACT[s][F[v]] == F[v]
                                     for v in range(V))]
            if len(S) == 1: continue   # not stabilized
            checked += 1
            Sset = set(S)
            # (i) normality
            if any(MUL[MUL[h][s]][INV[h]] not in Sset
                   for h in N for s in S): ok_norm = False
            # (ii) im F in Fix(S), Fix(S) N-invariant
            FixS = [v for v in range(V)
                    if all(ACT[s][v] == v for s in S)]
            if not set(F) <= set(FixS): ok_fix = False
            if any(ACT[h][v] not in set(FixS) for h in N
                   for v in FixS): ok_fix = False
            # (iii) power to bijection on T, T N-invariant
            G = list(F)
            for _ in range(V):
                T = sorted(set(G))
                if len(set(G[t] for t in T)) == len(T): break
                G = [G[G[v]] if False else G[F[v]] for v in range(V)]
            # recompute properly: iterate F
            G = list(F); k = 1
            while True:
                T = sorted(set(G))
                if all(len(set(G[v] for v in T)) == len(T)
                       for _ in [0]) and \
                   len({G[t] for t in T}) == len(T) and \
                   set(G[t] for t in T) == set(T): break
                G = [F[G[v]] for v in range(V)]; k += 1
                if k > 2*V: break
            T = sorted(set(G))
            if not (len({G[t] for t in T}) == len(T)
                    and set(G[t] for t in T) == set(T)):
                ok_pow = False
            if any(ACT[h][t] not in set(T) for h in N for t in T):
                ok_pow = False
            # (iv) fixed-point-free + generated by fix-having images
            im = {}
            for h in N:
                im.setdefault(tuple(ACT[h][t] for t in T), h)
            perms = set(im)
            if any(all(pm[i] == T[i] for i in range(len(T)))
                   for pm in perms if pm != tuple(T)): pass
            fixed_pt_free = not any(all(ACT[h][t] == t for h in N)
                                    for t in T)
            if not fixed_pt_free: ok_gen = False
            withfix = [pm for pm in perms
                       if any(pm[i] == T[i] for i in range(len(T)))]
            # closure of withfix inside perms
            pos = {t: i for i, t in enumerate(T)}
            def comp(a, b): return tuple(a[pos[b[i]]] for i in range(len(b)))
            idp = tuple(T)
            Sp = {idp} | set(withfix); dq = deque(Sp)
            while dq:
                x = dq.popleft()
                for y in list(Sp):
                    for z in (comp(x, y), comp(y, x)):
                        if z not in Sp: Sp.add(z); dq.append(z)
            if Sp != perms: ok_gen = False
    print(f"{name}: stabilized witnesses checked={checked}  "
          f"S normal: {ok_norm}  im in Fix(S) & invariant: {ok_fix}  "
          f"power->bijection & T invariant: {ok_pow}  "
          f"M fixed-point-free & refl-generated: {ok_gen}", flush=True)
