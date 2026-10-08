"""Is the closure of {p} under meet, join and x -> (x -> s), x -> (x -> s') finite in the free Heyting algebra
on p, s, s'?  Fingerprint IPC-terms by their values on all Kripke models (posets with <= K points, all valuations)
for the three variables; count distinct fingerprints as the closure grows (lower bound on the closure size)."""
import itertools as it, sys
from nuclei_join_axiom import HA
from join_inexpressible import posets

K = int(sys.argv[1]) if len(sys.argv) > 1 else 4
models = []
for n in range(1, K + 1):
    for le in posets(n):
        H = HA(n, le)   # down-sets; valuations = elements of H
        models.append(H)
def fp(f):
    """f: function (H, p, s, sp) -> element; fingerprint over all models and valuations (capped)."""
    out = []
    for H in models:
        for p in range(H.n):
            for s in range(H.n):
                for sp in range(H.n):
                    out.append(f(H, p, s, sp))
    return tuple(out)
# represent elements as fingerprints directly: store for each term its value tuple
def val_var(k):
    return fp(lambda H, p, s, sp: (p, s, sp)[k])
cells = []
for H in models:
    for p in range(H.n):
        for s in range(H.n):
            for sp in range(H.n):
                cells.append(H)
def op_meet(a, b): return tuple(H.meet(x, y) for H, x, y in zip(cells, a, b))
def op_join(a, b): return tuple(H.join(x, y) for H, x, y in zip(cells, a, b))
def op_imp(a, b): return tuple(H.imp(x, y) for H, x, y in zip(cells, a, b))
P, S, SP = val_var(0), val_var(1), val_var(2)
D = {P, S, SP}
for rnd in range(6):
    new = set(D)
    L = list(D)
    for a in L:
        new.add(op_imp(a, S)); new.add(op_imp(a, SP))
        for b in L:
            new.add(op_meet(a, b)); new.add(op_join(a, b))
    print("round", rnd, "distinct fingerprints:", len(new), flush=True)
    if new == D: print("closed"); break
    D = new
    if len(D) > 3000: print("growing beyond 3000, stop"); break
