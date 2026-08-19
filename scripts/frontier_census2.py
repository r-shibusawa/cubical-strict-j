"""Follow-up: full F2 homology (b0..b3) of the loci order complex
el(Sigma) for the six n=4 frontier classes, fixing the b2-blind
'contractible' call of frontier_census.py.  Consistency test:
el(Sigma) contractible  ==>  el(q) equivalence  ==>
H(elS) = H(elW); the |D|=192 class violates the RHS, so its
order complex must have higher homology."""
import sys, itertools
from collections import deque, Counter
sys.path.insert(0, 'scripts')
from strata_retract import build, rank

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
        c = [i]; sg = s[i]; j = p[i]; seen[i] = True
        while j != i:
            seen[j] = True; c.append(j); sg ^= s[j]; j = p[j]
        out.append((len(c), sg & 1))
    return tuple(sorted(out))

# frontier signatures from frontier_census.py output
SIGS = [
 (8,  {((1,0),(1,0),(1,0),(1,0)):1, ((1,1),(1,1),(2,0)):2, ((2,0),(2,0)):3, ((4,0),):2}),
 (8,  {((1,0),(1,0),(1,0),(1,0)):1, ((1,0),(1,0),(1,1),(1,1)):1, ((1,0),(1,0),(2,0)):3, ((1,1),(1,1),(2,0)):1, ((2,0),(2,0)):2}),
 (16, {((1,0),(1,0),(1,0),(1,0)):1, ((1,0),(1,0),(1,1),(1,1)):2, ((1,1),(1,1),(1,1),(1,1)):1, ((1,0),(1,0),(2,0)):4, ((1,1),(1,1),(2,0)):4, ((2,0),(2,0)):4}),
 (24, {((1,0),(1,0),(1,0),(1,0)):1, ((1,1),(1,1),(2,0)):6, ((1,0),(3,0)):8, ((2,0),(2,0)):3, ((4,0),):6}),
 (32, {((1,0),(1,0),(1,0),(1,0)):1, ((1,0),(1,0),(1,1),(1,1)):2, ((1,1),(1,1),(1,1),(1,1)):1, ((1,0),(1,0),(2,0)):4, ((1,1),(1,1),(2,0)):4, ((2,0),(2,0)):8, ((2,1),(2,1)):4, ((4,0),):8}),
 (192,{((1,0),(1,0),(1,0),(1,0)):1, ((1,0),(1,0),(1,1),(1,1)):6, ((1,1),(1,1),(1,1),(1,1)):1, ((1,0),(1,0),(2,0)):12, ((1,0),(1,1),(2,1)):24, ((1,1),(1,1),(2,0)):12, ((1,0),(3,0)):32, ((1,1),(3,1)):32, ((2,0),(2,0)):12, ((2,1),(2,1)):12, ((4,0),):48}),
]
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

found = []
for H in classes.values():
    R = [a for a in H if REFL[a]]
    if not R or close(R) != H: continue
    if any(all(ACT[a][v] == v for a in R) for v in range(1 << n)): continue
    sig = (len(H), dict(Counter(cyc(a) for a in H)))
    for t, (sz, ct) in enumerate(SIGS):
        if sig == (sz, ct):
            found.append((t, H))
print(f"matched {len(found)}/6 frontier classes", flush=True)

for t, H in sorted(found):
    Hs = sorted(H)
    loci = {}
    for a in H:
        if REFL[a]:
            L = frozenset(v for v in range(1 << n) if ACT[a][v] == v)
            loci[L] = 1
    allL = set(loci)
    changed = True
    while changed:
        changed = False
        for L1 in list(allL):
            for L2 in list(allL):
                I = L1 & L2
                if I and I not in allL:
                    allL.add(I); changed = True
    allL = sorted(allL, key=lambda L: (-len(L), sorted(L)))
    V = len(allL)
    lt = [[False]*V for _ in range(V)]
    for i, L1 in enumerate(allL):
        for j, L2 in enumerate(allL):
            lt[i][j] = allL[i] < allL[j]
    # chains up to length 4 (simplices dim <= 3)
    ch = {0: [(i,) for i in range(V)]}
    for k in range(1, 4):
        ch[k] = [c + (j,) for c in ch[k-1] for j in range(V)
                 if lt[c[-1]][j]]
    ind = {k: {c: i for i, c in enumerate(ch[k])} for k in ch}
    def dmat(k):
        cols = []
        for c in ch[k]:
            v = 0
            for i in range(len(c)):
                f = c[:i] + c[i+1:]
                v ^= 1 << ind[k-1][f]
            cols.append(v)
        return cols
    r = {k: rank(dmat(k)) for k in range(1, 4)}
    b0 = V - r[1]
    b1 = len(ch[1]) - r[1] - r[2]
    b2 = len(ch[2]) - r[2] - r[3]
    dims = [len(ch[k]) for k in range(4)]
    print(f"class {t}: |D|={len(H):3d} loci={V:2d} chains={dims} "
          f"el(Sigma) F2-Betti = [{b0}, {b1}, {b2}]"
          + ("  (contractible iff [1,0,0] AND dim<=2... see note)"
             if (b0, b1, b2) == (1, 0, 0) else ""), flush=True)
