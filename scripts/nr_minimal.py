"""(NR') sharpened to the MINIMAL subobject (O18, section 80).

A twisted end class is a delta-equivariant vertex map f : V -> V_l, and
the cell it classifies factors through the smallest sub-cube l' of l
containing im(f) -- the parity closure of im(f): the constraints
    x_i = c   and   x_i = x_j + s
satisfied by every point of im(f).  So the map W -> S_W actually factors
through l'/N', N' = the setwise stabiliser of l' in D, and (NR') only has
to be checked against this smaller object.  In particular the two general
kills apply to l':
   (K1) Q' fixes a vertex of l'  =>  el(l'/N') acyclic  =>  contradiction
        with W1;
   (K2) Q' free on the cells of l'  =>  el(l'/N') = BQ', and el(W) is
        simply connected, so a retraction lifts to the contractible
        universal cover and el(W) would be contractible -- again W1.
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build
from nr_sharp import VC, homology, induced_rank

n = 4
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

def parity_closure(A):
    """smallest sub-cube of {0,1}^n containing the vertex set A"""
    A = sorted(A)
    const = {}
    for i in range(n):
        vals = {(v >> i) & 1 for v in A}
        if len(vals) == 1: const[i] = vals.pop()
    rel = []
    free = [i for i in range(n) if i not in const]
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

RES = [
    ("R1 = <twisted diagonal, block swap>",
     [idx[((0, 1, 3, 2), (1, 1, 0, 0))], idx[((1, 0, 2, 3), (0, 0, 1, 1))],
      idx[((2, 3, 0, 1), (0, 0, 0, 0))]]),
    ("R2 = <sw01> x K_23",
     [idx[((1, 0, 2, 3), (0, 0, 0, 0))], idx[((0, 1, 3, 2), (0, 0, 0, 0))],
      idx[((0, 1, 2, 3), (0, 0, 1, 1))]]),
    ("R3 (|D|=24)",
     [idx[((0, 1, 3, 2), (1, 1, 0, 0))], idx[((1, 2, 0, 3), (0, 0, 0, 0))],
      idx[((0, 2, 1, 3), (1, 1, 1, 1))]]),
    ("R4 = K wr Z/2",
     [idx[((1, 0, 2, 3), (0, 0, 0, 0))], idx[((0, 1, 2, 3), (1, 1, 0, 0))],
      idx[((2, 3, 0, 1), (0, 0, 0, 0))]]),
]
for name, gens in RES:
    D = sorted(close(gens))
    A = VC(list(range(NV)), [ACT[a] for a in D], 4, NV=NV)
    HA = homology(A, 4)
    loci = {}
    for a in D:
        if REFL[a]:
            L = frozenset(v for v in range(NV) if ACT[a][v] == v)
            loci[L] = 1
    maximal = [sorted(L) for L in loci if not any(L < L2 for L2 in loci)]
    gg = None
    for i, a in enumerate(D):
        for b in D[i:]:
            if len(close([a, b])) == len(D): gg = [a, b]; break
        if gg: break
    if gg is None:
        gg = []; span = {ID}
        for a in D:
            if a in span: continue
            gg.append(a); span = set(close(gg))
            if len(span) == len(D): break
    word = {ID: []}; dq = deque([ID])
    while dq:
        x = dq.popleft()
        for k, g in enumerate(gg):
            y = MUL[x][g]
            if y not in word: word[y] = word[x] + [k]; dq.append(y)
    orbs = []; seenv = [False]*NV
    for v in range(NV):
        if seenv[v]: continue
        orb = {ACT[a][v] for a in D}
        for w in orb: seenv[w] = True
        orbs.append(sorted(orb))
    print(f"{name}: |D|={len(D)} H(elW)={[HA[k] for k in (1,2,3)]}")
    minimal_targets = set()
    seen = set()
    for Ls in maximal:
        key = min(tuple(sorted(ACT[g][v] for v in Ls)) for g in D)
        if key in seen: continue
        seen.add(key)
        Nl = [a for a in D if {ACT[a][v] for v in Ls} == set(Ls)]
        for imgs in itertools.product(Nl, repeat=len(gg)):
            d = {}
            for x in D:
                y = ID
                for k in word[x]: y = MUL[y][imgs[k]]
                d[x] = y
            if not all(d[MUL[a][b]] == MUL[d[a]][d[b]]
                       for a in D for b in D): continue
            ch = []
            for orb in orbs:
                v = orb[0]; St = [a for a in D if ACT[a][v] == v]
                ws = [w for w in Ls if all(ACT[d[a]][w] == w for a in St)]
                ch.append((orb, ws))
            if any(not ws for _, ws in ch): continue
            for pick in itertools.product(*[ws for _, ws in ch]):
                if all(all(ACT[d[x]][w] == w for x in D) for w in pick):
                    continue                     # strict: already null
                im = set()
                for (orb, _), w in zip(ch, pick):
                    v = orb[0]
                    for h in D: im.add(ACT[d[h]][w])
                minimal_targets.add(tuple(parity_closure(im)))
    for Lm in sorted(minimal_targets, key=len):
        Lm = list(Lm)
        Nm = [a for a in D if {ACT[a][v] for v in Lm} == set(Lm)]
        Pm = [a for a in Nm if all(ACT[a][w] == w for w in Lm)]
        k1 = any(all(ACT[a][w] == w for a in Nm) for w in Lm)
        k2 = not any(a not in Pm and any(ACT[a][w] == w for w in Lm)
                     for a in Nm)
        tag = "K1 acyclic-kill" if k1 else ("K2 free-kill" if k2 else None)
        if tag is None:
            S = VC(Lm, [ACT[a] for a in Nm], 4, NV=NV)
            HS = homology(S, 4)
            r = {k: induced_rank(S, A, k, lambda c, m: c) for k in (1, 2, 3)}
            bad = [k for k in (1, 2, 3) if r[k] < HA[k]]
            tag = f"deg{bad}" if bad else f"INCONCLUSIVE (H(el l'/N')={[HS[k] for k in (1,2,3)]}, ranks={r})"
        print(f"    minimal target |l'|={len(Lm):2d} |N'|={len(Nm):3d} "
              f"|Q'|={len(Nm)//len(Pm)}: {tag}")
