"""(T-C) part 4: closed form of the collapse locus Z_D and its geometry.

Z_D = { (d,a,t) : F(d,a,t) = F(d,~a,t) }   (diagonal-image cells).
Using F = (d & ~t) | (a & (t|d)):

(G1) test candidate characterizations:
     C1:  a & (t|d)  ==  ~a & (t|d)
     C2:  (t|d)  <=  "a-degeneracy":  t|d <= (a&~a) | ???   -- derived
(G2) closure properties of Z_D needed for the end-retraction:
     - t-lowering: (d,a,t) in Z_D  =>  (d,a,t&s) in Z_D for all s?
     - t=0 face always in the end layer (trivially: t=0 => diag).
     - d-raising/lowering?
Census at level 1 (exhaustive) and level 2 (exhaustive for C1;
sampled for closure probes).
"""
import random
from collage_type_lib import build, monotone_masks, NOT, gen

def setup(n):
    N, leq, rho = build(n)
    dm = monotone_masks(N, leq)
    notf = {m: NOT(m, N, rho) for m in dm}
    return N, dm, notf

def F_of(d, a, t, notf):
    return (d & notf[t]) | (a & t) | (d & a)

for n in (1, 2):
    N, dm, notf = setup(n)
    FULL = (1 << N) - 1
    # collect Z_D over ALL cells (including end t's, for closure tests)
    ZD = set()
    for t in dm:
        for d in dm:
            for a in dm:
                if F_of(d, a, t, notf) == F_of(d, notf[a], t, notf):
                    ZD.add((d, a, t))
    # C1 candidate
    c1_ok = all(((a & (t | d)) == (notf[a] & (t | d))) == ((d, a, t) in ZD)
                for t in dm for d in dm for a in dm) if n == 1 else None
    if n == 2:
        # exhaustive but streamed
        c1_ok = True
        for t in dm:
            for d in dm:
                td = t | d
                for a in dm:
                    inZ = F_of(d, a, t, notf) == F_of(d, notf[a], t, notf)
                    c1 = (a & td) == (notf[a] & td)
                    if inZ != c1:
                        c1_ok = False
                        print("C1 mismatch:", (d, a, t))
                        break
                if not c1_ok: break
            if not c1_ok: break
    print(f"level {n}: |Z_D| = {len(ZD)} of {len(dm)**3};  C1 (a&(t|d) == ~a&(t|d)) exact: {c1_ok}")

    # (G2) t-lowering closure:  (d,a,t) in Z_D  =>  (d,a,t&s) in Z_D ?
    viol = 0; tested = 0
    items = list(ZD) if n == 1 else random.Random(1).sample(list(ZD), min(4000, len(ZD)))
    for (d, a, t) in items:
        for s in (dm if n == 1 else random.Random(2).sample(dm, 20)):
            tested += 1
            if (d, a, t & s) not in ZD and \
               F_of(d, a, t & s, notf) != F_of(d, notf[a], t & s, notf):
                viol += 1
    print(f"  t-lowering closure: {viol} violations / {tested} tests")

    # d-lowering closure: (d,a,t) in Z_D => (d&s, a, t) in Z_D ?
    viol = 0; tested = 0
    for (d, a, t) in items:
        for s in (dm if n == 1 else random.Random(3).sample(dm, 20)):
            tested += 1
            if F_of(d & s, a, t, notf) != F_of(d & s, notf[a], t, notf):
                viol += 1
    print(f"  d-lowering closure: {viol} violations / {tested} tests")
