"""Iterated cut-point reconstruction (random acyclic graphs with 4-8 vertices) on a finite acyclic digraph G (path category finite).
Presheaf X on P(G): sets X(v), maps X(c) -> X(d) for each edge d -> c.  a_S X = Ran(X|_S): (a_S X)(c) = compatible
families over paths from S-vertices into c.  Y_0 = X, Y_{n+1} = a_S a_T Y_n.  n_min = least n with Y_n a T-sheaf
(then Y_n = join sheafification = a_{S n T} X).  Compare n_min with the alternation bound a (max number of
'T-visit then S-visit' along paths avoiding S n T)."""
import random, itertools as it, sys
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 0)

def paths_into(n, E):
    # all paths (tuples of vertices v0 -> v1 -> ... -> c) into each vertex c, acyclic so finite; include empty path (c,)
    P = {c: [] for c in range(n)}
    for c in range(n):
        st = [(c,)]
        while st:
            p = st.pop(); P[c].append(p)
            for (d, e) in E:
                if e == p[0]: st.append((d,) + p)
    return P

def restrict(X, path, x):
    # path = (v0, v1, ..., c); X(c) -> X(v0): apply edge maps from c backwards
    for i in range(len(path) - 1, 0, -1):
        x = X['res'][(path[i-1], path[i])][x]
    return x

def ran(X, S, n, E, P):
    """Return a_S X as a presheaf with elements = tuples of (path, value) for paths from S into c, and edge maps."""
    Y = {'el': {}, 'res': {}}
    fam = {}
    for c in range(n):
        ps = [p for p in P[c] if p[0] in S]
        ps.sort()
        fams = []
        for vals in it.product(*[X['el'][p[0]] for p in ps]):
            y = dict(zip(ps, vals)); ok = True
            for p in ps:
                for q in P[p[0]]:
                    if q[0] in S and len(q) > 1:
                        pq = q[:-1] + p  # q followed by p
                        if y[pq] != restrict(X, q, y[p]): ok = False; break
                if not ok: break
            if ok: fams.append(tuple(sorted(y.items())))
        Y['el'][c] = fams
    for (d, c) in E:
        m = {}
        for f in Y['el'][c]:
            y = dict(f)
            z = {p: y[p + (c,)] for p in P[d] if p[0] in S}
            m[f] = tuple(sorted(z.items()))
        Y['res'][(d, c)] = m
    # unit X -> a_S X
    unit = {c: {x: tuple(sorted((p, restrict(X, p, x)) for p in P[c] if p[0] in S)) for x in X['el'][c]} for c in range(n)}
    return Y, unit

def is_sheaf(X, S, n, E, P):
    Y, unit = ran(X, S, n, E, P)
    return all(len(set(unit[c].values())) == len(X['el'][c]) == len(Y['el'][c]) for c in range(n))

def max_alt(n, E, S, T):
    X = S & T; best = 0
    P = paths_into(n, E)
    for c in range(n):
        for p in P[c]:
            if any(v in X for v in p): continue
            k = 0; ph = 0
            for v in p:
                if ph == 0 and v in T: ph = 1
                elif ph == 1 and v in S: ph = 0; k += 1
            best = max(best, k)
    return best

stats = {}; worst = []
for trial in range(900):
    n = random.randint(4, 8)
    E = [(i, j) for i in range(n) for j in range(i + 1, n) if random.random() < (0.9 if j == i + 1 else 0.12)]
    if not E: continue
    S = {v for v in range(n) if random.random() < 0.5}; T = {v for v in range(n) if random.random() < 0.5}
    if not S or not T: continue
    P = paths_into(n, E)
    if max(len(P[c]) for c in range(n)) > 12: continue
    X = {'el': {v: list(range(random.randint(1, 2))) for v in range(n)}, 'res': {}}
    for (d, c) in E:
        X['res'][(d, c)] = {x: random.choice(X['el'][d]) for x in X['el'][c]}
    a = max_alt(n, E, S, T)
    Y = X; nmin = None
    for k in range(0, 7):
        if is_sheaf(Y, T, n, E, P) and is_sheaf(Y, S, n, E, P): nmin = k; break
        Z, _ = ran(Y, T, n, E, P); Y, _ = ran(Z, S, n, E, P)
        if max(len(Y['el'][c]) for c in range(n)) > 3000: break
    key = (a, nmin); stats[key] = stats.get(key, 0) + 1
    if nmin is None or nmin > a + 1: worst.append((n, E, sorted(S), sorted(T), a, nmin))
print("(alternation bound a, rounds n_min) -> count:")
for k in sorted(stats, key=lambda t: (t[0], -1 if t[1] is None else t[1])): print(" ", k, stats[k])
print("cases with n_min > a+1 or unresolved:", len(worst))
for w in worst[:5]: print(" ", w)
