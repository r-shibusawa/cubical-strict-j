r"""Nuclei on truth-value algebras and the classes W_j = {a <= b : j a = j b}.

1. Heyting algebras Up(P), P a random finite poset, nuclei O_C (all nuclei on finite P):
   test whether W_{j1 /\ j2} = W_{j1} /\ W_{j2}  (meet of nuclei is pointwise), and record the
   stabilisation index of the alternating iteration (j1 j2)^n = j1 \/ j2.
2. Finite MV-algebras L_n = {0, 1/n, ..., 1} and products of them: enumerate all nuclei
   (inflationary idempotent monotone maps with j(a)*j(b) <= j(a*b)) and check that each is
   a closed nucleus a |-> a \/ c.
"""
import random, itertools
from fractions import Fraction as F

# ---------- Part 1: Heyting algebras of up-sets ----------
def random_poset(n, p):
    rel = [[i == j for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(i+1, n):
            if random.random() < p: rel[i][j] = True
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if rel[i][k] and rel[k][j]: rel[i][j] = True
    return rel

def upsets(rel):
    n = len(rel)
    for bits in itertools.product([0, 1], repeat=n):
        U = frozenset(i for i in range(n) if bits[i])
        if all(rel[u][v] <= (v in U) for u in U for v in range(n)): yield U

def nec(rel, C, U):
    n = len(rel)
    return frozenset(x for x in range(n) if all((not rel[x][q]) or (q not in C) or (q in U) for q in range(n)))

random.seed(5)
meet_fail = 0; pairs = 0; max_index = 0
for trial in range(40):
    n = random.randint(1, 4); rel = random_poset(n, random.random())
    Us = list(upsets(rel)); P = frozenset(range(n))
    subsets = [frozenset(s) for r in range(n+1) for s in itertools.combinations(range(n), r)]
    for C in subsets:
        for Cp in subsets:
            j1 = {U: nec(rel, C, U) for U in Us}; j2 = {U: nec(rel, Cp, U) for U in Us}
            jm = {U: j1[U] & j2[U] for U in Us}
            for a in Us:
                for b in Us:
                    if a <= b and jm[a] == jm[b] and not (j1[a] == j1[b] and j2[a] == j2[b]):
                        meet_fail += 1
            # stabilisation index of the alternating iteration from each a
            jj = {U: nec(rel, C & Cp, U) for U in Us}  # the join on a finite poset
            for a in Us:
                x = a; k = 0
                while x != jj[a]:
                    x = j1[j2[x]]; k += 1
                    assert k <= 2*n+2
                max_index = max(max_index, k)
            pairs += 1
print(f"Heyting Up(P): {pairs} nucleus pairs; W_(j1 meet j2) = W_j1 cap W_j2 violated {meet_fail} times; max stabilisation index {max_index}")

# ---------- Part 2: MV-algebras ----------
def mv_chain(n):
    els = [F(i, n) for i in range(n+1)]
    tensor = lambda a, b: max(F(0), a + b - 1)
    return els, tensor
def mv_product(A, B):
    (ea, ta), (eb, tb) = A, B
    els = [(a, b) for a in ea for b in eb]
    tensor = lambda x, y: (ta(x[0], y[0]), tb(x[1], y[1]))
    return els, tensor
def leq(x, y):
    return x <= y if not isinstance(x, tuple) else all(u <= v for u, v in zip(x, y))
def join(x, y):
    return max(x, y) if not isinstance(x, tuple) else tuple(max(u, v) for u, v in zip(x, y))

def nuclei(els, tensor):
    top = max(els) if not isinstance(els[0], tuple) else tuple(max(e[i] for e in els) for i in range(2))
    out = []
    for vals in itertools.product(els, repeat=len(els)):
        j = dict(zip(els, vals))
        if not all(leq(a, j[a]) for a in els): continue
        if not all(j[j[a]] == j[a] for a in els): continue
        if not all(leq(j[a], j[b]) for a in els for b in els if leq(a, b)): continue
        if not all(leq(tensor(j[a], j[b]), j[tensor(a, b)]) for a in els for b in els): continue
        out.append(j)
    return out

for name, (els, tensor) in [("L3", mv_chain(2)), ("L4", mv_chain(3)), ("L5", mv_chain(4)), ("L2xL3", mv_product(mv_chain(1), mv_chain(2))), ("L3xL3", mv_product(mv_chain(2), mv_chain(2)))]:
    if len(els) > 6: continue
    N = nuclei(els, tensor)
    closed = 0
    for j in N:
        c = min((j[a] for a in els), key=lambda v: (v if not isinstance(v, tuple) else sum(v)))
        c = j[els[0]]  # j(0) is the least fixed point
        if all(j[a] == join(a, c) for a in els): closed += 1
    print(f"MV {name}: {len(N)} nuclei, {closed} closed (a |-> a v c)")
