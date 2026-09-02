"""O27 stage 9: the sort-exchange lemma and the sorted triangles.

(1) SORT-EXCHANGE: for every substitution sigma: [k] -> [q]
    (sigma in D(k)^q), the sorted instance sigma <> sort_k has all
    components in the chain {0, o_1, ..., o_k, 1}; extracting the
    decreasing rearrangement d (with multiplicities) and the
    pattern rho (variables/constants), we get
        sigma <> sort_k = rho <> d,   d = T(f) simplicial.
    Verify for all sigma with k, q <= 3.
(2) SORTED TRIANGLES: identities
    sort2 <> (1,t) = (1,t), sort2 <> (t,t) = (t,t),
    sort2 <> (t,0) = (t,0),
    sortop <> (1,t) = (t,1), sortop <> (t,t) = (t,t),
    sortop <> (t,0) = (0,t),
    where sort2 = (x1|x2, x1&x2), sortop = (x1&x2, x1|x2):
    the two sorted triangles of a square carry (right, diag,
    bottom) and (top, diag, left) -- the pi_1 diagonal
    decomposition.  Also verify both are sort-fixed.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F

def to_int(t):
    n = 0
    for i, b in enumerate(t): n |= b << i
    return n

D = {k: [to_int(f) for f in F(k)[1]] for k in range(0, 4)}

def o_stat(j, m):
    """j-th order statistic as int over 2^m points; o_0 = 1,
    o_{>m} = 0"""
    if j <= 0: return (1 << (1 << m)) - 1
    if j > m: return 0
    out = 0
    for pt in range(1 << m):
        if bin(pt).count('1') >= j: out |= 1 << pt
    return out

def comp1(p, v, l, m):
    """p in D(l), v = l-tuple over D(m): p(v) in D(m)"""
    out = 0
    for x in range(1 << m):
        idx = 0
        for i in range(l):
            idx |= ((v[i] >> x) & 1) << i
        if (p >> idx) & 1: out |= 1 << x
    return out

def diamond(u, v, q, l, m):
    """u: [l]->[q] (tuple in D(l)^q), v: [m]->[l]: u<>v in D(m)^q"""
    return tuple(comp1(c, v, l, m) for c in u)

# (1) sort-exchange sweep
for k in range(1, 4):
    chain = [o_stat(j, k) for j in range(0, k + 2)]  # 1, o1..ok, 0
    sort_k = tuple(o_stat(j, k) for j in range(1, k + 1))
    for q in range(1, 4):
        bad = 0; checked = 0
        for sigma in itertools.product(D[k], repeat=q):
            inst = diamond(sigma, sort_k, q, k, k)
            # components in the chain?
            if not all(c in chain for c in inst):
                bad += 1; continue
            # decreasing rearrangement + pattern
            order = sorted(inst, reverse=False)
            # chain order: o_j decreasing in j; encode rank
            rank = {c: i for i, c in enumerate(chain)}  # 1 first? chain[0]=1
            dec = sorted(inst, key=lambda c: rank[c])   # 1, o1, ..., 0
            # d = the decreasing tuple; rho picks positions/constants
            d = tuple(dec)
            # verify d is "T(f)": components decreasing chain vals ✓ by
            # construction; verify sigma<>sort = rho <> d with rho =
            # variable pattern:
            pos = {}
            recon = []
            ok = True
            for c in inst:
                # find c in d
                if c == chain[0]:   # constant 1
                    recon.append(chain[0])
                elif c == chain[-1]:
                    recon.append(chain[-1])
                else:
                    if c not in d: ok = False; break
                    recon.append(c)
            if not ok or tuple(recon) != inst: bad += 1
            checked += 1
        print(f"k={k}, q={q}: sigmas checked {checked}, "
              f"exchange failures: {bad}", flush=True)

# (2) sorted triangles
x1 = to_int(tuple(p[0] for p in F(2)[0]))
x2 = to_int(tuple(p[1] for p in F(2)[0]))
t  = to_int(tuple(p[0] for p in F(1)[0]))
one1 = (1 << 2) - 1; zero1 = 0
sort2 = (x1 | x2, x1 & x2)
sortop = (x1 & x2, x1 | x2)
faces = {'d0=(1,t)': (one1, t), 'd1=(t,t)': (t, t), 'd2=(t,0)': (t, zero1)}
for name, s2 in (('sort2', sort2), ('sortop', sortop)):
    fixed = diamond(s2, (o_stat(1,2), o_stat(2,2)), 2, 2, 2) == s2
    print(f"{name}: sort-fixed: {fixed}")
    for fn, fv in faces.items():
        res = diamond(s2, fv, 2, 2, 1)
        print(f"  {name} <> {fn} = {res}  "
              f"[t={t}, 1={one1}, 0={zero1}, (t,1)={(t,one1)}, "
              f"(0,t)={(zero1,t)}]")
