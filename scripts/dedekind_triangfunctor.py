"""O27 stage 5: the order-statistics triangulation functor
T : Delta -> A_Ded,  [n] |-> [n],
  T(f)_i = o_{m(f,i)}   for f : [m] -> [n] monotone (ordinal maps
  on {0,...,m} -> {0,...,n}),  where
  o_k(x_1..x_m) = k-th order statistic = OR_{|S|=k} AND_{i in S} x_i
  (o_0 = 1, o_k = 0 for k > m),   m(f,i) = min{k : f(k) >= i}.

Checks:
 1. T(f) is a well-defined tuple of monotone maps (automatic).
 2. FUNCTORIALITY: T(f o g) = T(f) o T(g) for all composable
    ordinal maps up to size N.
 3. T(id) = id.
 4. The special cases: cofaces delta^i = (insert), codegeneracies
    sigma^0 = meet, sigma^(top) = join at the right positions.
 5. RC1: the two vertices T(d1),T(d0): [0] -> [1] are distinct.
All identities are between lattice-polynomial tuples, so checking
on {0,1}-points is complete (D(k) embeds in 2^(2^k) pointwise).
"""
import itertools

def ordinal_maps(m, n):
    """monotone maps {0..m} -> {0..n}"""
    out = []
    for vals in itertools.product(range(n + 1), repeat=m + 1):
        if all(vals[i] <= vals[i + 1] for i in range(m)):
            out.append(vals)
    return out

def order_stat(k, x):
    """k-th order statistic of tuple x (1-indexed); o_0 = 1"""
    m = len(x)
    if k <= 0: return 1
    if k > m: return 0
    return 1 if sum(x) >= k else 0
    # (for 0/1 inputs, OR_{|S|=k} AND_S x = [at least k ones])

def T(f, m, n):
    """the map {0,1}^m -> {0,1}^n : x |-> (T(f)_i(x))_i"""
    idx = []
    for i in range(1, n + 1):
        ks = [k for k in range(m + 1) if f[k] >= i]
        idx.append(min(ks) if ks else m + 1)
    def apply(x):
        return tuple(order_stat(k, x) for k in idx)
    return apply

N = 4
ok = True
for m in range(0, N):
    for n in range(0, N):
        for l in range(0, N):
            for g in ordinal_maps(m, n):
                Tg = T(g, m, n)
                for f in ordinal_maps(n, l):
                    Tf = T(f, n, l)
                    comp = tuple(f[v] for v in g)  # f o g : [m]->[l]
                    Tfg = T(comp, m, l)
                    for x in itertools.product((0, 1), repeat=m):
                        if Tf(Tg(x)) != Tfg(x):
                            ok = False
                            print("FUNCTORIALITY FAILS", m, n, l, g, f, x)
print("functoriality up to size", N, ":", "OK" if ok else "FAIL")

for n in range(0, N):
    idn = tuple(range(n + 1))
    Ti = T(idn, n, n)
    good = all(Ti(x) == x for x in itertools.product((0, 1), repeat=n))
    print(f"T(id_[{n}]) = id: {good}")

# special cases at n = 1, 2
s0 = T((0, 0, 1), 2, 1)   # collapse 0,1
s1 = T((0, 1, 1), 2, 1)   # collapse 1,2
print("sigma^0 = meet:",
      all(s0(x) == (x[0] & x[1],) for x in itertools.product((0,1),repeat=2)))
print("sigma^1 = join:",
      all(s1(x) == (x[0] | x[1],) for x in itertools.product((0,1),repeat=2)))
d0 = T((1,), 0, 1); d1 = T((0,), 0, 1)
print("RC1 endpoints distinct:", d0(()) != d1(()),
      f"(d0 = {d0(())}, d1 = {d1(())})")
# inner coface at n=2: [1]->[2] hitting 0,2
dd = T((0, 2), 1, 2)
print("inner delta duplicates:",
      all(dd((x,)) == (x, x) for x in (0, 1)))
d_top = T((1, 2), 1, 2); d_bot = T((0, 1), 1, 2)
print("delta^0 inserts 1:", all(d_top((x,)) == (1, x) for x in (0,1)))
print("delta^2 inserts 0:", all(d_bot((x,)) == (x, 0) for x in (0,1)))
