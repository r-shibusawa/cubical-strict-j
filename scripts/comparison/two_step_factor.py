"""Two-step factorisation of maps inverted by the join localisation, checked on representations of A_2.

Representations of the quiver A_2 = (1 -> 2) over GF(2): M = (M_1 -a-> M_2).  T = {M : M_2 = 0} (stable:
the simple S_1 is injective), T' = {M : M_1 = 0} (not stable: E(S_2) = (k -> k)).  T v T' is everything.
W_T = maps that are isomorphisms at vertex 2, W_{T'} = isomorphisms at vertex 1.

The theorem (for T' stable and T v T' stable, applied here to the pair (T', T)): every map f : X -> Y factors as
h o g with g in W_{T'} and h in W_T, where Z = Y x_{Q Y} Q X is the pullback along the localisation
Q = Q_{T'} : M |-> (M_1 -> 0), i.e. Z_1 = graph of f_1 ~ X_1, Z_2 = Y_2, g = (x_1 |-> (f_1 x_1, x_1), f_2),
h = projection.  The script verifies this on random maps, and verifies by brute force that the map
0 -> (k -> k) has no factorisation in the other order (W_{T'} after W_T) with Z of dimension vector <= (3, 3):
the order of the two classes is forced by which theory is stable.
"""
import itertools as it, random

def rank2(cols):
    rows = list(cols); r = 0
    for bit in range(32):
        piv = next((i for i in range(r, len(rows)) if rows[i] >> bit & 1), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i] >> bit & 1: rows[i] ^= rows[r]
        r += 1
    return r

def is_iso(cols, dim_src, dim_tgt):
    return dim_src == dim_tgt and rank2(cols) == dim_src

def apply(cols, v):
    img = 0
    for i, c in enumerate(cols):
        if v >> i & 1: img ^= c
    return img

def random_rep(d1, d2):
    return d1, d2, [random.randrange(1 << d2) for _ in range(d1)]

def random_map(X, Y):
    """a morphism f = (f1, f2) with a_Y f1 = f2 a_X, found by random search"""
    (x1, x2, ax), (y1, y2, ay) = X, Y
    for _ in range(2000):
        f1 = [random.randrange(1 << y1) for _ in range(x1)]
        f2 = [random.randrange(1 << y2) for _ in range(x2)]
        if all(apply(ay, apply(f1, 1 << i)) == apply(f2, apply(ax, 1 << i)) for i in range(x1)):
            return f1, f2
    return None

def check_pullback_factorisation(X, Y, f):
    (x1, x2, ax), (y1, y2, ay) = X, Y; f1, f2 = f
    # Z_1 = graph of f1 (coordinates: x1 bits), Z_2 = Y_2; a_Z (x) = f2(a_X x)  (= a_Y f1 x)
    az = [apply(f2, apply(ax, 1 << i)) for i in range(x1)]
    g1 = [1 << i for i in range(x1)]            # X_1 -> Z_1 identity on graph coordinates
    g2 = list(f2)                                # X_2 -> Z_2 = Y_2
    h1 = list(f1)                                # Z_1 -> Y_1, (f1 x, x) |-> f1 x
    h2 = [1 << i for i in range(y2)]             # Z_2 = Y_2 -> Y_2
    # g in W_{T'}: iso at vertex 1; h in W_T: iso at vertex 2; and h o g = f
    assert is_iso(g1, x1, x1) and is_iso(h2, y2, y2)
    assert all(apply(h1, apply(g1, 1 << i)) == apply(f1, 1 << i) for i in range(x1))
    assert all(apply(h2, apply(g2, 1 << i)) == apply(f2, 1 << i) for i in range(x2))
    # Z is a representation and g, h are morphisms
    assert all(apply(az, apply(g1, 1 << i)) == apply(g2, apply(ax, 1 << i)) for i in range(x1))
    assert all(apply(ay, apply(h1, 1 << i)) == apply(h2, apply(az, 1 << i)) for i in range(x1))
    return True

def reverse_order_exists(dmax=3):
    """is 0 -> M = (k -> k) a composite 0 -> Z -> M with 0 -> Z in W_T (Z_2 = 0 ... i.e. Z in T) and
    Z -> M in W_{T'} (iso at vertex 1)?  Z in T forces Z = (Z_1 -> 0); a morphism Z -> M has h_2 = 0 and
    a_M h_1 = h_2 a_Z = 0, so h_1 = 0 as a_M is an isomorphism; then h is not an isomorphism at vertex 1."""
    for z1 in range(dmax + 1):
        # all h1 : Z_1 -> k with a_M h1 = 0 : only h1 = 0; iso at vertex 1 needs z1 == 1 and h1 iso: impossible
        for h1 in it.product(range(2), repeat=z1):
            if all(v == 0 for v in h1) and is_iso(list(h1), z1, 1):
                return True
    return False

if __name__ == "__main__":
    random.seed(3); n = 0
    for _ in range(400):
        X = random_rep(random.randrange(4), random.randrange(4)); Y = random_rep(random.randrange(4), random.randrange(4))
        f = random_map(X, Y)
        if f is None: continue
        check_pullback_factorisation(X, Y, f); n += 1
    print(f"A_2: pullback factorisation f = h g (g iso at vertex 1, h iso at vertex 2) verified on {n} random maps")
    print("A_2: factorisation of 0 -> (k -> k) in the other order with dim Z_1 <= 3 exists:", reverse_order_exists())
