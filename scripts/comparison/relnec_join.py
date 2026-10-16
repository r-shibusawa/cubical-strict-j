r"""Joins of relativized necessities on finite posets.

For a poset P and C subset of P, the nucleus O_C on Up(P) is
    O_C(U) = {p : for all q >= p, q in C implies q in U} = P \ down(C \ U).
Checks, on random finite posets:
  1. O_C /\ O_C' = O_{C u C'} (pointwise meet);
  2. the join O_C v O_C' (least common fixed point above U, by iteration)
     equals P \ X_U where X_U is the largest subset X of P \ U with
     X subset down(X n C) n down(X n C')  (greatest fixed point);
  3. on finite posets the join is O_{C n C'} (no infinite alternating chain).
"""
import random, itertools

def random_poset(n, p):
    rel = [[False]*n for _ in range(n)]
    for i in range(n):
        rel[i][i] = True
        for j in range(i+1, n):
            if random.random() < p: rel[i][j] = True
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if rel[i][k] and rel[k][j]: rel[i][j] = True
    return rel

def down(rel, S):
    n = len(rel); return frozenset(p for p in range(n) if any(rel[p][q] for q in S))

def up(rel, S):
    n = len(rel); return frozenset(p for p in range(n) if any(rel[q][p] for q in S))

def nec(rel, C, U):
    n = len(rel); return frozenset(range(n)) - down(rel, C - U)

def join_iter(rel, C, Cp, U):
    V = U
    while True:
        W = nec(rel, Cp, nec(rel, C, V))
        if W == V: return V
        V = W

def join_gfp(rel, C, Cp, U):
    n = len(rel); X = frozenset(range(n)) - U
    while True:
        Y = frozenset(x for x in X if x in down(rel, X & C) and x in down(rel, X & Cp))
        if Y == X: return frozenset(range(n)) - X
        X = Y

def upsets(rel):
    n = len(rel)
    for bits in itertools.product([0,1], repeat=n):
        U = frozenset(i for i in range(n) if bits[i])
        if up(rel, U) == U: yield U

random.seed(1)
tests = 0
for trial in range(300):
    n = random.randint(1, 7); rel = random_poset(n, random.random())
    C = frozenset(i for i in range(n) if random.random() < 0.5)
    Cp = frozenset(i for i in range(n) if random.random() < 0.5)
    for U in upsets(rel):
        assert nec(rel, C, U) & nec(rel, Cp, U) == nec(rel, C | Cp, U)
        j = join_iter(rel, C, Cp, U)
        assert j == join_gfp(rel, C, Cp, U), (rel, C, Cp, U)
        assert j == nec(rel, C & Cp, U)
        tests += 1
print("checked", tests, "cases: meet = O_{C u C'}, join = gfp formula = O_{C n C'} on finite posets")
