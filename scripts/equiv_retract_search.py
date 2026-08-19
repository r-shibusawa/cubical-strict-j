"""Search for a D-equivariant retraction onto ANY D-invariant sub-cube
(O18, section 85) -- the general form of transfer route (c).

If l is a D-invariant sub-cube of cube^n admitting a D-equivariant vertex
retraction f (f|_{V_l} = id, f sigma_h = sigma_h f), then the self-dual mux
upgrades f to a D-equivariant deformation retraction (section 81.1), so
W = cube^n/D is homotopy equivalent to l/D in BOTH structures, and the
witness for Q_l = D|_l transfers.  The stratum need not be maximal, and
need not be a fixed locus at all: any D-invariant sub-cube will do.
"""
import sys, itertools
from collections import deque
sys.path.insert(0, 'scripts')
from strata_retract import build

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

def subcubes():
    """all sub-cubes of {0,1}^n: pick constants and parity identifications"""
    out = set()
    for const in itertools.product((None, 0, 1), repeat=n):
        free = [i for i in range(n) if const[i] is None]
        # parity relations among free coordinates: a partition with signs
        for asg in itertools.product(range(len(free) + 1), repeat=len(free)):
            if any(asg[i] > max(asg[:i], default=-1) + 1
                   for i in range(len(free))): continue
            for signs in itertools.product((0, 1), repeat=len(free)):
                if any(signs[i] and asg[:i].count(asg[i]) == 0
                       for i in range(len(free))):
                    continue          # first member of a class has sign 0
                S = []
                for v in range(NV):
                    ok = True
                    for i in range(n):
                        if const[i] is not None and ((v >> i) & 1) != const[i]:
                            ok = False; break
                    if not ok: continue
                    rep = {}
                    for k, i in enumerate(free):
                        b = ((v >> i) & 1) ^ signs[k]
                        if asg[k] in rep:
                            if rep[asg[k]] != b: ok = False; break
                        else: rep[asg[k]] = b
                    if ok: S.append(v)
                if S: out.add(tuple(S))
    return sorted(out, key=len)

CUBES = subcubes()
print(f"sub-cubes of the 4-cube: {len(CUBES)}")

RES = [
    ("R3", [idx[((0, 1, 3, 2), (1, 1, 0, 0))], idx[((1, 2, 0, 3), (0, 0, 0, 0))],
            idx[((0, 2, 1, 3), (1, 1, 1, 1))]]),
    ("R4", [idx[((1, 0, 2, 3), (0, 0, 0, 0))], idx[((0, 1, 2, 3), (1, 1, 0, 0))],
            idx[((2, 3, 0, 1), (0, 0, 0, 0))]]),
]
for name, gens in RES:
    D = sorted(close(gens))
    orbs = []; seenv = [False]*NV
    for v in range(NV):
        if seenv[v]: continue
        orb = sorted({ACT[a][v] for a in D})
        for w in orb: seenv[w] = True
        orbs.append(orb)
    print(f"{name}: |D|={len(D)}")
    found = []
    for Ls in CUBES:
        Lset = set(Ls)
        if len(Ls) == NV: continue
        if any({ACT[a][v] for v in Ls} != Lset for a in D): continue  # invariant
        # D-equivariant retraction?
        ok = True
        for orb in orbs:
            v = orb[0]
            if v in Lset: continue
            St = [a for a in D if ACT[a][v] == v]
            if not any(all(ACT[a][w] == w for a in St) for w in Ls):
                ok = False; break
        if not ok: continue
        # is Q_l separating (closed form)?
        Pl = [a for a in D if all(ACT[a][w] == w for w in Ls)]
        Rq = [a for a in D if a not in Pl and any(ACT[a][w] == w for w in Ls)]
        sep = bool(Rq) and not any(all(ACT[a][w] == w for a in Rq) for w in Ls)
        found.append((len(Ls), len(Pl), len(D)//len(Pl), sep))
    if not found:
        print("   no D-invariant sub-cube with an equivariant retraction")
    for a, p, q, s in found:
        print(f"   sub-cube |l|={a} |P_l|={p} |Q_l|={q} -> "
              f"Q_l {'SEPARATES (transfer works)' if s else 'agrees'}")
