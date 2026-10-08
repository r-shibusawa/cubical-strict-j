"""Join of two nuclei on a finite Heyting algebra (= finite distributive lattice):
(a) j1 v j2 has fixed points Fix(j1) ∩ Fix(j2) and (j1 v j2)(a) = min{b >= a : j1 b = b = j2 b};
(b) it equals the iterate (j1 j2)^n for large n;
(c) the 'leastness' scheme  (◯1ψ→ψ) ∧ (◯2ψ→ψ) ∧ (φ→ψ)  <=  (◯12φ→ψ)  holds internally.
Heyting algebras = down-set lattices of random finite posets; nuclei enumerated by brute force (small cases)."""
import itertools as it, random, sys

def downsets(n, le):
    pts = range(n)
    D = []
    for mask in range(1 << n):
        S = {i for i in pts if mask >> i & 1}
        if all(j in S for i in S for j in pts if le[j][i]): D.append(frozenset(S))
    return D

class HA:
    def __init__(self, n, le):
        self.el = downsets(n, le); self.idx = {d: i for i, d in enumerate(self.el)}; self.n = len(self.el)
        self.top = self.idx[frozenset(range(n))]; self.bot = self.idx[frozenset()]
    def meet(self, a, b): return self.idx[self.el[a] & self.el[b]]
    def join(self, a, b): return self.idx[self.el[a] | self.el[b]]
    def le(self, a, b): return self.el[a] <= self.el[b]
    def imp(self, a, b):
        # largest c with c ∧ a <= b
        best = self.bot
        for c in range(self.n):
            if self.le(self.meet(c, a), b) and self.le(best, c): best = c
        return best

def nuclei(H):
    """all nuclei: inflationary, idempotent, meet-preserving maps."""
    out = []
    cands = [[b for b in range(H.n) if H.le(a, b)] for a in range(H.n)]
    def rec(i, f):
        if i == H.n:
            if all(f[f[a]] == f[a] for a in range(H.n)) and all(f[H.meet(a, b)] == H.meet(f[a], f[b]) for a in range(H.n) for b in range(H.n)):
                out.append(tuple(f))
            return
        for b in cands[i]:
            f.append(b)
            # prune monotone
            if all(not H.le(a, i) or H.le(f[a], b) for a in range(i)) and all(not H.le(i, a) or H.le(b, f[a]) for a in range(i)):
                rec(i + 1, f)
            f.pop()
    rec(0, [])
    return out

def join_nucleus(H, j1, j2):
    fix = [b for b in range(H.n) if j1[b] == b and j2[b] == b]
    res = []
    for a in range(H.n):
        ups = [b for b in fix if H.le(a, b)]
        m = min(ups, key=lambda b: len(H.el[b]))
        assert all(H.le(m, b) for b in ups)
        res.append(m)
    return tuple(res)

if __name__ == "__main__":
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    tested = 0
    for t in range(trials):
        n = random.choice([2, 3, 3, 4])
        le = [[i == j for j in range(n)] for i in range(n)]
        for _ in range(random.randint(0, n)):
            i, j = random.sample(range(n), 2); le[i][j] = True
        for k in range(n):  # transitive closure
            for i in range(n):
                for j in range(n):
                    if le[i][k] and le[k][j]: le[i][j] = True
        if any(le[i][j] and le[j][i] and i != j for i in range(n) for j in range(n)): continue
        H = HA(n, le)
        if H.n > 12: continue
        N = nuclei(H)
        for j1, j2 in it.product(N, repeat=2):
            J = join_nucleus(H, j1, j2)
            # (b) iterate
            f = tuple(range(H.n)); 
            for _ in range(2 * H.n): f = tuple(j1[j2[f[a]]] for a in range(H.n))
            assert f == J, "iteration"
            # (a) J is a nucleus above both
            assert all(H.le(j1[a], J[a]) and H.le(j2[a], J[a]) for a in range(H.n))
            # (c) scheme
            for phi in range(H.n):
                for psi in range(H.n):
                    lhs = H.meet(H.meet(H.imp(j1[psi], psi), H.imp(j2[psi], psi)), H.imp(phi, psi))
                    rhs = H.imp(J[phi], psi)
                    assert H.le(lhs, rhs), "scheme"
            tested += 1
    print("Heyting algebras with pairs of nuclei tested:", tested, "— join = least common fixed point = iterate; scheme valid")
