"""Path category P(G) of a finite digraph G; object-generated topologies J_S (least cover at c = paths into c passing
through S, identities of S included).  Ideal chain (D_S D_T)^k: a path is in level k iff it has k alternations
"T-visit then S-visit" (positions non-decreasing, a common vertex of S n T gives all levels).
Claim: the chain stabilises iff no closed walk of G avoiding S n T meets both S and T, i.e. iff no strongly connected
component of G - (S n T) meets both S and T (simple cycles do not suffice: s <-> u <-> t with S = {s}, T = {t}).
Test: max alternation over paths avoiding S n T of length <= 3|V| vs. 2|V| (growth = non-stabilisation) against the
component criterion; when it holds, the maximal alternation is checked against the bound min(|S - T|, |T - S|)."""
import random, itertools as it, sys
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 0)

def max_alt(V, E, S, T, L):
    # dynamic programming over paths avoiding S n T: state (vertex, phase) phase in {0: need T, 1: need S}, count
    X = S & T; best = 0
    # paths as walks of length <= L; count alternations greedily (greedy is optimal for subsequence pattern TSTS..)
    from collections import deque
    start = [(v, 1 if v in T else 0, 0) for v in V if v not in X]
    seen = {(v, ph): 0 for (v, ph, k) in start}
    frontier = start
    for step in range(L):
        new = []
        for (v, ph, k) in frontier:
            # at vertex v: update phase
            for w in E.get(v, []):
                if w in X: continue
                ph2, k2 = ph, k
                if ph2 == 0 and w in T: ph2 = 1
                elif ph2 == 1 and w in S: ph2 = 0; k2 += 1
                key = (w, ph2)
                if seen.get(key, -1) < k2: seen[key] = k2; new.append((w, ph2, k2))
        frontier = new
        if not frontier: break
    # also account for the starting vertex itself
    for v in V:
        if v in X: continue
    return max([k for (v, ph), k in seen.items()] + [0])

def bad_cycle(V, E, S, T):
    X = S & T
    # is there a cycle avoiding X that meets S and T?  check: s in S\X, t in T\X with s ~> t and t ~> s in G - X
    def reach(a):
        seen = {a}; st = [a]
        while st:
            v = st.pop()
            for w in E.get(v, []):
                if w not in X and w not in seen: seen.add(w); st.append(w)
        return seen
    R = {v: reach(v) for v in V if v not in X}
    return any(t in R[s] and s in R[t] for s in S - X for t in T - X)

mism = 0; tot = 0; stab = 0; viol = 0
for trial in range(400):
    n = random.randint(3, 7); V = list(range(n))
    E = {v: [w for w in V if random.random() < 0.25] for v in V}
    S = {v for v in V if random.random() < 0.35}; T = {v for v in V if random.random() < 0.35}
    if not S or not T: continue
    a2, a3 = max_alt(V, E, S, T, 2 * n), max_alt(V, E, S, T, 3 * n)
    grows = a3 > a2
    cyc = bad_cycle(V, E, S, T)
    tot += 1; stab += (not cyc)
    if grows != cyc: mism += 1; print("MISMATCH", V, E, S, T, a2, a3, cyc)
    if not cyc and a3 > min(len(S - T), len(T - S)): viol += 1; print("BOUND VIOLATED", V, E, S, T, a3)
print(f"{tot} graphs, {stab} stabilising by the component criterion, {mism} mismatches between growth and the criterion, "
      f"{viol} violations of the bound min(|S-T|,|T-S|)")
