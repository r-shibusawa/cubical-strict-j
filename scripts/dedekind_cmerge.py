"""O27 stage 3: the incomparable-pair merge C -- the smallest
transversal-less atom.  C = spectral quotient of cube^3 merging the
vertices a = (1,0,1), b = (0,1,1) (ints 5, 6 in bit order).

Cells of C at level k = fiber patterns of triples in D(k)^3:
the function {0,1}^k -> P_C, x |-> [sigma(x)] with [5]=[6].
G = cube^3/(a ~ b as vertices) has G(k) = D(k)^3 with the two
constant cells merged; pi: G ->> C.

Compute: |C(k)| for k <= 4; folded classes of pi; whether the
tautological generator is folded; folded GENERATORS at levels 3, 4
(folded tau admitting a monotone section rho with tau o rho = id).
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F
from collections import defaultdict

def to_int(t):
    n = 0
    for i, b in enumerate(t): n |= b << i
    return n

def ints(k):
    pts, D = F(k)
    return [to_int(f) for f in D]

A, B = 5, 6  # merged vertices of {0,1}^3 (bit i = coord i)
LABEL = list(range(8))
LABEL[B] = A  # fiber label

def pattern(sig, npts):
    """sig = triple of ints over npts points -> tuple of labels"""
    out = []
    for x in range(npts):
        vtx = (((sig[0] >> x) & 1) | (((sig[1] >> x) & 1) << 1)
               | (((sig[2] >> x) & 1) << 2))
        out.append(LABEL[vtx])
    return tuple(out)

def vfun(sig, npts):
    out = []
    for x in range(npts):
        out.append(((sig[0] >> x) & 1) | (((sig[1] >> x) & 1) << 1)
                   | (((sig[2] >> x) & 1) << 2))
    return tuple(out)

for k in range(0, 5):
    Dk = ints(k); npts = 1 << k
    pats = defaultdict(set)   # pattern -> set of vertex-functions
    for sig in itertools.product(Dk, repeat=3):
        pats[pattern(sig, npts)].add(vfun(sig, npts))
    nC = len(pats)
    nG = len(set().union(*pats.values()))
    folded = {p: fs for p, fs in pats.items() if len(fs) > 1}
    nfold = sum(len(fs) for fs in folded.values())
    print(f"level {k}: |C| = {nC}, |G-cells here| = {nG}, "
          f"folded classes = {len(folded)}, folded G-cells = {nfold}",
          flush=True)
    if k == 3:
        gen = tuple(LABEL[x] for x in range(8))
        print(f"  generator pattern folded: "
              f"{len(pats[gen]) > 1} (fiber = {len(pats[gen])})")
    if k in (3, 4):
        # folded generators: tau (vertex function {0,1}^k -> {0,1}^3,
        # monotone) in a folded class, admitting monotone section
        def has_section(tau):
            fibers = defaultdict(list)
            for y, val in enumerate(tau): fibers[val].append(y)
            if any(v not in fibers for v in range(8)): return False
            order = sorted(range(8), key=lambda x: bin(x).count('1'))
            chosen = {}
            def bt(pos):
                if pos == 8: return True
                x = order[pos]
                for y in fibers[x]:
                    ok = True
                    for x2, y2 in chosen.items():
                        if (x2 & x) == x2 and not ((y2 & y) == y2):
                            ok = False; break
                        if (x & x2) == x and not ((y & y2) == y):
                            ok = False; break
                    if ok:
                        chosen[x] = y
                        if bt(pos + 1): return True
                        del chosen[x]
                return False
            return bt(0)
        fg = 0; example = None
        for p, fs in folded.items():
            for tau in fs:
                if has_section(tau):
                    fg += 1
                    if example is None: example = tau
                    break
        print(f"  level {k}: folded classes containing a GENERATOR "
              f"(sectioned tau): {fg}"
              + (f"  e.g. tau = {example}" if example else ""), flush=True)
