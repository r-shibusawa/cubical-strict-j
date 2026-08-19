"""(R-ret) from idempotent splitting (O18, section 83).

A twisted end class is a delta-equivariant vertex map f : V -> V_l, i.e.
a self-map of V with image in V_l.  Since V is finite, the eventual image
    A := f^N(V)      (N large)
satisfies f|_A : A -> A bijective, so some power F := f^{N r} is an
IDEMPOTENT delta^{Nr}-equivariant self-map of V with image A and
F|_A = id_A.

Presheaves are idempotent complete, so the induced strict endomorphism
e := rho . j of W' splits; writing W'' for the splitting one gets
    jhat := j . j' : W'' -> W,     rhohat := rho' . rho : W -> W''
with  jhat . rhohat = (j rho)^{r+1} ~ id_W   and
      rhohat . jhat ~ rho' e^r j' = id_{W''}.
So jhat is an ISOMORPHISM in Ho(type) with NO extra hypothesis: the
strict retraction of (R-ret) is not an assumption but a consequence, PROVIDED
the splitting object W'' is again a cube quotient, i.e. provided the
eventual image A is the full vertex set of the sub-cube it spans.

This script tests exactly that for every twisted end class of every
reflection-generated mixed class of B_n, n <= 4:
    A = eventual image of f    ==?==   V_{parity closure of A}.
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build

def parity_closure(A, n):
    NV = 1 << n
    A = sorted(A)
    const = {}
    for i in range(n):
        vals = {(v >> i) & 1 for v in A}
        if len(vals) == 1: const[i] = vals.pop()
    free = [i for i in range(n) if i not in const]
    rel = []
    for a in range(len(free)):
        for b in range(a + 1, len(free)):
            i, j = free[a], free[b]
            ss = {((v >> i) & 1) ^ ((v >> j) & 1) for v in A}
            if len(ss) == 1: rel.append((i, j, ss.pop()))
    out = []
    for v in range(NV):
        if any(((v >> i) & 1) != c for i, c in const.items()): continue
        if any((((v >> i) & 1) ^ ((v >> j) & 1)) != s for i, j, s in rel):
            continue
        out.append(v)
    return out

for n in (2, 3, 4):
    ELEMS, idx, ID, NE, MUL, INV, ACT = build(n)
    NV = 1 << n
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
    def close(g):
        S = {ID}; dq = deque([ID])
        while dq:
            x = dq.popleft()
            for a in g:
                y = MUL[x][a]
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
    classes = {}
    for H in subs:
        key = min(tuple(sorted(MUL[MUL[g][a]][INV[g]] for a in H))
                  for g in range(NE))
        classes.setdefault(key, H)
    tgt = []
    for H in classes.values():
        R = [a for a in H if REFL[a]]
        if not R: continue
        if any(all(ACT[a][v] == v for a in R) for v in range(NV)): continue
        if close(R) != H: continue
        tgt.append(sorted(H))
    tot = bad = 0
    examples = []
    for H in tgt:
        loci = {}
        for a in H:
            if REFL[a]:
                L = frozenset(v for v in range(NV) if ACT[a][v] == v)
                loci[L] = 1
        maximal = [sorted(L) for L in loci if not any(L < L2 for L2 in loci)]
        gg = None
        for i, a in enumerate(H):
            for b in H[i:]:
                if len(close([a, b])) == len(H): gg = [a, b]; break
            if gg: break
        if gg is None:
            gg = []; span = {ID}
            for a in H:
                if a in span: continue
                gg.append(a); span = set(close(gg))
                if len(span) == len(H): break
        word = {ID: []}; dq = deque([ID])
        while dq:
            x = dq.popleft()
            for k, g in enumerate(gg):
                y = MUL[x][g]
                if y not in word: word[y] = word[x] + [k]; dq.append(y)
        orbs = []; seenv = [False]*NV
        for v in range(NV):
            if seenv[v]: continue
            orb = {ACT[a][v] for a in H}
            for w in orb: seenv[w] = True
            orbs.append(sorted(orb))
        seen = set()
        for Ls in maximal:
            key = min(tuple(sorted(ACT[g][v] for v in Ls)) for g in H)
            if key in seen: continue
            seen.add(key)
            Nl = [a for a in H if {ACT[a][v] for v in Ls} == set(Ls)]
            for imgs in itertools.product(Nl, repeat=len(gg)):
                d = {}
                for x in H:
                    y = ID
                    for k in word[x]: y = MUL[y][imgs[k]]
                    d[x] = y
                if not all(d[MUL[a][b]] == MUL[d[a]][d[b]]
                           for a in H for b in H): continue
                ch = []
                for orb in orbs:
                    v = orb[0]; St = [a for a in H if ACT[a][v] == v]
                    ws = [w for w in Ls if all(ACT[d[a]][w] == w for a in St)]
                    ch.append((orb, ws))
                if any(not ws for _, ws in ch): continue
                for pick in itertools.product(*[ws for _, ws in ch]):
                    if all(all(ACT[d[x]][w] == w for x in H) for w in pick):
                        continue                    # strict already
                    # build f : V -> V_l
                    f = {}
                    okf = True
                    for (orb, _), w in zip(ch, pick):
                        v0 = orb[0]
                        for h in H:
                            u = ACT[h][v0]; val = ACT[d[h]][w]
                            if u in f and f[u] != val: okf = False; break
                            f[u] = val
                        if not okf: break
                    if not okf: continue
                    tot += 1
                    # eventual image
                    A = set(range(NV))
                    for _ in range(2 * NV):
                        A2 = {f[v] for v in A}
                        if A2 == A: break
                        A = A2
                    pc = parity_closure(A, n)
                    if set(pc) != A:
                        bad += 1
                        if len(examples) < 3:
                            examples.append((len(H), sorted(A), pc))
    print(f"n={n}: twisted end classes examined {tot}; "
          f"eventual image NOT a full sub-cube: {bad}", flush=True)
    for e in examples:
        print(f"    |D|={e[0]} A={e[1]} parity closure={e[2]}")
