"""Reachability closures on P(X): rho_{R,I}(S) = R^*(S u I) (states reachable from S or from the initial set I).
Checks on random finite systems: (a) rho is a closure, not meet-preserving in general; (b) J := W_rho v W_rho' (2-of-3
saturation) equals D = {S <= T : T <= (rho rho')^k S} = W_{rho join rho'} with rho join rho' = rho_{R u R', I u I'};
(c) the number of alternations needed is <= |X| (uniform bound); (d) cancellation needed (C != J) is common."""
import random, itertools as it, sys
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 0)

def reach(R, I, S, n):
    cur = set(S) | set(I); changed = True
    while changed:
        changed = False
        for (a, b) in R:
            if a in cur and b not in cur: cur.add(b); changed = True
    return frozenset(cur)

def run(n, trials):
    pts = range(n)
    allS = [frozenset(c) for r in range(n + 1) for c in it.combinations(pts, r)]
    idx = {S: i for i, S in enumerate(allS)}
    stats = dict(trials=0, nonmeet=0, cancel=0, J_ne_W=0, kmax=0)
    for _ in range(trials):
        R = {(a, b) for a in pts for b in pts if a != b and random.random() < 0.25}
        R2 = {(a, b) for a in pts for b in pts if a != b and random.random() < 0.25}
        I = {a for a in pts if random.random() < 0.15}; I2 = {a for a in pts if random.random() < 0.15}
        rho = {S: reach(R, I, S, n) for S in allS}; rho2 = {S: reach(R2, I2, S, n) for S in allS}
        rhoj = {S: reach(R | R2, I | I2, S, n) for S in allS}
        stats['trials'] += 1
        if any(rho[S & T] != rho[S] & rho[T] for S in allS for T in allS): stats['nonmeet'] += 1
        le = lambda S, T: S <= T
        W = lambda r: {(S, T) for S in allS for T in allS if S <= T and r[S] == r[T]}
        Wa, Wb, Wj = W(rho), W(rho2), W(rhoj)
        # D and kmax
        D = set(); kmax = 0
        for S in allS:
            chain = [S]; z = S
            while True:
                z2 = rho[rho2[z]]
                if z2 == z: break
                chain.append(z2); z = z2
            kmax = max(kmax, len(chain) - 1)
            assert z == rhoj[S], "lub mismatch"
            for T in allS:
                if S <= T and T <= z: D.add((S, T))
        stats['kmax'] = max(stats['kmax'], kmax)
        # C and J
        C = set(Wa | Wb)
        def compclose(C):
            changed = True
            while changed:
                changed = False
                for (a, b) in list(C):
                    for (c, d) in list(C):
                        if b == c and (a, d) not in C: C.add((a, d)); changed = True
            return C
        C = compclose(C); J = set(C)
        changed = True
        while changed:
            changed = False
            for (x, y) in D - J:
                if any((x, z) in J and (y, z) in J for z in allS if y <= z) or any((w, x) in J and (w, y) in J for w in allS if w <= x):
                    J.add((x, y)); changed = True
            if changed: J = compclose(J)
        if C != J: stats['cancel'] += 1
        if J != Wj or J != D: stats['J_ne_W'] += 1
    print(f"n={n}: {stats}")

run(3, 300); run(4, 150); run(5, 30)
