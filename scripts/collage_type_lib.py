"""Shared up-set representation of free De Morgan algebras (bit masks)."""

def build(n):
    """Points of L_n = {0,1}^{2n}; return (npoints, leq pairs, involution)."""
    N = 1 << (2 * n)
    def coords(p):
        return [(p >> i) & 1 for i in range(2 * n)]
    leq = []
    for p in range(N):
        cp = coords(p)
        for q in range(N):
            cq = coords(q)
            if all(a <= b for a, b in zip(cp, cq)):
                leq.append((p, q))
    rho = []
    for p in range(N):
        c = coords(p)
        d = []
        for i in range(n):
            vx, vnx = c[2 * i], c[2 * i + 1]
            d += [1 - vnx, 1 - vx]
        q = sum(b << i for i, b in enumerate(d))
        rho.append(q)
    return N, leq, rho

def monotone_masks(N, leq):
    out = []
    for m in range(1 << N):
        ok = True
        for p, q in leq:
            if (m >> p) & 1 and not (m >> q) & 1:
                ok = False
                break
        if ok:
            out.append(m)
    return out

def NOT(m, N, rho):
    r = 0
    for p in range(N):
        if not (m >> rho[p]) & 1:
            r |= 1 << p
    return r

def gen(i, n, N):
    m = 0
    for p in range(N):
        if (p >> (2 * i)) & 1:
            m |= 1 << p
    return m
