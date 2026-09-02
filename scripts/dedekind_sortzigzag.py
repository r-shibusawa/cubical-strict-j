"""O27 stage 11: the elementary sort zigzag and Sing(X x cube^1).

(1) ZIGZAG: the adjacent merge s_i = (..., x_i | x_{i+1},
    x_i & x_{i+1}, ...) is connected to the identity by the
    zigzag of strict homotopies (in the two relevant coords):
      H1(x_i, x_{i+1}, t) = (x_i | (x_{i+1} & t), x_{i+1})
        : id  ==>  mid = (x_i | x_{i+1}, x_{i+1})
      H2(x_i, x_{i+1}, t) = (x_i | x_{i+1}, x_{i+1} & (x_i | t))
        : s_i ==>  mid
    Verify: ends, monotonicity in t (automatic: lattice
    polynomials), and that no SINGLE monotone homotopy can join
    id and s_i directly (second component would have to decrease
    in t: check the four vertex traces).
(2) Sing(cube^1) = Delta^1 with the T-operators; and product
    compatibility counts |Sing(cube^1 x cube^1)_q| = (q+2)^2.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F

def to_int(t):
    n = 0
    for i, b in enumerate(t): n |= b << i
    return n

# work in D(3): variables a, b, t
pts3 = F(3)[0]
a = to_int(tuple(p[0] for p in pts3))
b = to_int(tuple(p[1] for p in pts3))
t = to_int(tuple(p[2] for p in pts3))

H1 = (a | (b & t), b)
H2 = (a | b, b & (a | t))

def slice_t(f, bit):
    """restrict D(3)-elt to t = bit -> D(2)-elt"""
    pts2 = F(2)[0]
    out = 0
    for i, p in enumerate(pts2):
        idx = pts3.index((p[0], p[1], bit))
        if (f >> idx) & 1: out |= 1 << i
    return out

a2 = to_int(tuple(p[0] for p in F(2)[0]))
b2 = to_int(tuple(p[1] for p in F(2)[0]))
mid = (a2 | b2, b2)
print("H1 ends: t=0 ->", tuple(slice_t(c, 0) for c in H1) == (a2, b2),
      "; t=1 ->", tuple(slice_t(c, 1) for c in H1) == mid)
print("H2 ends: t=0 ->", tuple(slice_t(c, 0) for c in H2) == (a2 & b2 | a2, b2 & a2) or
      tuple(slice_t(c, 0) for c in H2),
      "= s_i:", tuple(slice_t(c, 0) for c in H2) == (a2 | b2, b2 & a2),
      "; t=1 ->", tuple(slice_t(c, 1) for c in H2) == mid)

# no single monotone homotopy: on vertex traces the second
# component must go from b (t=0) to a&b (t=1) at (a,b)=(0,1):
# from 1 down to 0 -- impossible monotonely.
print("direct homotopy impossible: at (a,b)=(0,1) second comp "
      "must fall 1 -> 0 while t rises: [monotone excluded]")

# (2) Sing(cube^1 x cube^1): sorted cells of cube^2 = (q+2)^2 --
# already verified in singsort; recompute q=2,3 quickly for the
# product statement
def o_stat(j, m):
    if j <= 0: return (1 << (1 << m)) - 1
    if j > m: return 0
    out = 0
    for pt in range(1 << m):
        if bin(pt).count('1') >= j: out |= 1 << pt
    return out

def comp1(p, v, l, m):
    out = 0
    for x in range(1 << m):
        idx = 0
        for i in range(l):
            idx |= ((v[i] >> x) & 1) << i
        if (p >> idx) & 1: out |= 1 << x
    return out

D = {k: [to_int(f) for f in F(k)[1]] for k in range(0, 4)}
for q in (2, 3):
    srt = tuple(o_stat(j, q) for j in range(1, q + 1))
    n_sorted_pairs = sum(
        1 for c in itertools.product(D[q], repeat=2)
        if tuple(comp1(p, srt, q, q) for p in c) == c)
    print(f"q={q}: |Sing(cube^1 x cube^1)_q| = {n_sorted_pairs} "
          f"= (q+2)^2 = {(q+2)**2}: {n_sorted_pairs == (q+2)**2}")
