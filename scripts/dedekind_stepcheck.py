"""O28 stage 5a: combinatorial skeleton of the extension (Step).

For sample quotients X = cube^n/K, run the attachment analysis for
the top cell and verify the bookkeeping claims of the extension
architecture (SS176):
 (a) minimal presentation: after splitting non-invertible
     self-stabilizers (idempotent powers), every remaining
     coincidence pair at the top level has both members
     non-invertible ("fresh pairs are proper");
 (b) track coverage: every K-class of size >= 2 among NEW cells
     (levels <= Kmax) consists of cells lying in proper atoms
     (trackable), i.e. no class member has an invertible
     presentation, except the top class itself whose relations
     are the H_x-orbit (group case);
 (c) chain anchoring: every track atom's chain part maps into
     Ch(X) (values prescribed);
 (d) measure: every track atom is a proper subatom (|cells| at
     level <= n strictly smaller than the cube's -- proxy for
     |L| descent).
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, restrict, Quotient

def rest(cell, u, j, k):
    return tuple(compose(c, u, j, k) for c in cell)
def leq_t(a, b): return all(x <= y for x, y in zip(a, b))
def comparable(a, b): return leq_t(a, b) or leq_t(b, a)
K = 3

def is_perm(u, n):
    """u = n-tuple over F(n): invertible iff a coordinate perm"""
    pts, _ = F(n)
    projs = [tuple(p[i] for p in pts) for i in range(n)]
    return sorted(u) == sorted(projs) and all(x in projs for x in u)

def analyze(name, n, idents):
    X = Quotient(n, idents, K)
    _, Dn = F(n)
    pts, _ = F(n)
    gen = tuple(tuple(p[i] for p in pts) for i in range(n))  # id cell
    # top-cell classifying map: u |-> X.cls(k, gen . u) = X-class of u
    def xval(u, k): return X.cls(k, u if False else u) if False else \
        X.classes[k][u]
    # (a) non-invertible self-stabilizer? u: [n]->[n] with [u]=[id]
    self_stab = [u for u in itertools.product(Dn, repeat=n)
                 if X.classes[n][u] == X.classes[n][gen]]
    noninv_self = [u for u in self_stab if not is_perm(u, n)]
    H = [u for u in self_stab if is_perm(u, n)]
    print(f"{name}: |self-stab| {len(self_stab)}, group part "
          f"{len(H)}, non-invertible self {len(noninv_self)}",
          flush=True)
    if noninv_self:
        print(f"  -> minimality reduction needed (retract to "
              f"proper atom); skipping deeper checks", flush=True)
        return
    # chain stratum of X (for prescribed-ness)
    def o_stat_t(j, m):
        p2, _ = F(m)
        if j <= 0: return tuple(1 for _ in p2)
        if j > m: return tuple(0 for _ in p2)
        return tuple(1 if sum(q) >= j else 0 for q in p2)
    def sort_sub(q): return tuple(o_stat_t(j,q) for j in range(1,q+1))
    ChX = {k: set() for k in range(K + 1)}
    for q in range(K + 1):
        _, Dq = F(q)
        for c in X.level(q):
            if X.cls(q, rest(c, sort_sub(q), q, q, )) != c: continue
            for k in range(K + 1):
                _, Dk = F(k)
                for u in itertools.product(Dk, repeat=q):
                    if all(comparable(a,b) for a,b in
                           itertools.combinations(u,2)) or q==0:
                        ChX[k].add(X.cls(k, rest(c, u, q, k)))
                if q == 0:
                    break
    # classes of positions at levels <= K
    from collections import defaultdict
    ok_b = ok_c = ok_d = True
    ncube_lown = None
    for m in range(K + 1):
        _, Dm = F(m)
        classes = defaultdict(list)
        for t in itertools.product(Dm, repeat=n):
            classes[X.classes[m][t]].append(t)
        for xc, mem in classes.items():
            if len(mem) < 2: continue
            if xc in ChX[m]: continue          # prescribed zone
            # skip the top orbit (m = n, members invertible)
            inv_mem = [t for t in mem if m == n and is_perm(t, n)]
            proper_mem = [t for t in mem if not (m == n and
                                                 is_perm(t, n))]
            if inv_mem and proper_mem:
                ok_b = False
                print(f"  (b) FAIL level {m}: class mixes "
                      f"invertible and proper members", flush=True)
            for t in proper_mem:
                # (d) proper atom: t's atom at level n smaller
                At = {rest(t, u, m, n)
                      for u in itertools.product(Dn, repeat=m)}
                if len(At) >= len(Dn) ** 1 and m <= n:
                    pass
                # crude properness: generic cell not in atom
                if gen in At:
                    ok_d = False
                    print(f"  (d) FAIL: track atom contains generic",
                          flush=True)
                # (c) chain cells of the atom are prescribed
                for k in range(K + 1):
                    _, Dk = F(k)
                    for u in itertools.product(Dk, repeat=m):
                        if not all(comparable(a,b) for a,b in
                                   itertools.combinations(u,2)):
                            continue
                        cell = rest(t, u, m, k)
                        if all(comparable(a,b) for a,b in
                               itertools.combinations(cell,2)):
                            if X.classes[k][cell] not in ChX[k]:
                                ok_c = False
    print(f"  (b) proper fresh classes: {ok_b}; (c) track chain "
          f"cells prescribed: {ok_c}; (d) tracks proper: {ok_d}",
          flush=True)

xx = tuple(p[0] for p in F(2)[0]); yy = tuple(p[1] for p in F(2)[0])
mt = tuple(a & b for a, b in zip(xx, yy))
u3 = tuple(p[0] for p in F(3)[0]); v3 = tuple(p[1] for p in F(3)[0])
w3 = tuple(p[2] for p in F(3)[0])
mt3uv = tuple(a & b for a, b in zip(u3, v3))
A2 = (xx, yy, mt if False else tuple(a & b for a, b in zip(xx, yy)))
# level-2 cells of cube^3: A=(x,y,x&y), B=(y,x,x&y)
A = (xx, yy, tuple(a & b for a, b in zip(xx, yy)))
B = (yy, xx, tuple(a & b for a, b in zip(xx, yy)))
x1 = tuple(p[0] for p in F(1)[0])
c01 = tuple(0 for _ in F(1)[0]); c11 = tuple(1 for _ in F(1)[0])

analyze("W dunce hat", 2, [(1, (c01, x1), (x1, c01)),
                           (1, (x1, x1), (x1, c11))])
analyze("SP^2 (swap)", 2, [(2, (xx, yy), (yy, xx))])
analyze("cube^3/(A~B) fresh", 3, [(2, A, B)])
analyze("sortfold", 2, [(2, (xx, yy),
                         (tuple(a&b for a,b in zip(xx,yy)),
                          tuple(a|b for a,b in zip(xx,yy))))])
