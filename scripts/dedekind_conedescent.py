"""O28 stage 6a: the cone-descent theorem -- verification.

THEOREM candidate: if every generating pair of a congruence K on
cube^k has constant-1-free components, then the wedge cone
descends to cube^k/K (key identity: (A o v) ^ d = A o (v ^ d)
componentwise, from z(sigma ^ t) = z(sigma) ^ t for 1-free z),
so cube^k/K is strictly contractible.  Split-epi components are
always constant-free (t o w = id forces t_i(0)=0, t_i(1)=1),
hence ALL split-pair fold quotients are strictly contractible.

Checks:
 (1) all 12 genuine (2,3) split pairs: components constant-free;
 (2) the cone cylinder (x1^x3, x2^x3) satisfies the descent
     condition on both M-fold quotients and has ends [const-0]
     and [id]  (direct witness, no search);
 (3) key identity (A o v) ^ d = A o (v^d) for random 1-free A, v, d;
 (4) negative control: on W = dunce hat the cone cylinder FAILS
     descent (B2 = (u,1) has a constant 1), matching the census.
"""
import sys, itertools, random
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, restrict, Quotient

def const_free(f, m):
    pts, _ = F(m)
    return f[0] == 0 and f[-1] == 1   # f(0...0)=0 and f(1...1)=1
def pmeet(a, b): return tuple(x & y for x, y in zip(a, b))

# (1) the twelve pairs
pts_k, _ = F(2)
gen = tuple(tuple(p[i] for p in pts_k) for i in range(2))
_, D3 = F(3); _, D2 = F(2)
def comp(t, w): return tuple(compose(tc, w, 3, 2) for tc in t)
from collections import defaultdict
sec_of = defaultdict(set)
for t in itertools.product(D3, repeat=2):
    for w in itertools.product(D2, repeat=3):
        if comp(t, w) == gen: sec_of[t].add(w)
def is_perm(u, n):
    pts, _ = F(n)
    projs = [tuple(p[i] for p in pts) for i in range(n)]
    return sorted(u) == sorted(projs)
split_cells = [t for t in sec_of if sec_of[t]]
ok1 = True
npairs = 0
for t in split_cells:
    for t2 in split_cells:
        if t2 <= t or not (sec_of[t] & sec_of[t2]): continue
        X = Quotient(2, [(3, t, t2)], 2)
        cls_gen = X.classes[2][gen]
        mem = [u for u, r in X.classes[2].items() if r == cls_gen]
        if not all(is_perm(u, 2) for u in mem): continue
        npairs += 1
        for c in t + t2:
            if not const_free(c, 3): ok1 = False
print(f"(1) {npairs} genuine pairs, all components constant-free: "
      f"{ok1}", flush=True)

# (3) key identity on random 1-free polys
random.seed(5)
ok3 = True
for _ in range(300):
    m = random.choice((2, 3)); j = random.choice((2, 3))
    _, Dm = F(m); _, Dj = F(j)
    # 1-free (no constant 1 in any expression) <=> A(0...0)=0:
    # a monotone p with p(0)=1 is identically 1; p(0)=0 has a
    # constant-free DNF (possibly p = 0)
    A = random.choice([f for f in Dj if f[0] == 0])
    v = tuple(random.choice(Dm) for _ in range(j))
    d = random.choice(Dm)
    lhs = pmeet(compose(A, v, j, m), d)
    vd = tuple(pmeet(vi, d) for vi in v)
    rhs = compose(A, vd, j, m)
    if lhs != rhs: ok3 = False
print(f"(3) (Aov)^d = Ao(v^d) for 1-free A (300 random): {ok3}",
      flush=True)

# (2) cone cylinder on the M-folds, direct descent check (K=4)
t1 = ((0,0,0,0,0,0,1,1), (0,0,0,0,0,1,0,1))
t2 = ((0,0,0,1,0,0,1,1), (0,0,0,1,0,1,0,1))
u1 = ((0,0,0,0,0,0,1,1), (0,0,0,1,0,0,0,1))
u2 = ((0,0,0,0,0,1,1,1), (0,0,0,1,0,1,0,1))
pts3, _ = F(3)
x1 = tuple(p[0] for p in pts3); x3 = tuple(p[2] for p in pts3)
x2 = tuple(p[1] for p in pts3)
CONE = (pmeet(x1, x3), pmeet(x2, x3))
for name, A, B in [("shape#0", t1, t2), ("shape#1", u1, u2)]:
    X = Quotient(2, [(3, A, B)], 4)
    pts4, _ = F(4)
    def lift(f3):
        return tuple(f3[p[0]*4 + p[1]*2 + p[2]] for p in pts4)
    x4 = tuple(p[3] for p in pts4)
    Aid = (lift(A[0]), lift(A[1]), x4)
    Bid = (lift(B[0]), lift(B[1]), x4)
    ha = X.cls(4, restrict(CONE, Aid, 2, 3, 4))
    hb = X.cls(4, restrict(CONE, Bid, 2, 3, 4))
    xx = tuple(p[0] for p in F(2)[0]); yy = tuple(p[1] for p in F(2)[0])
    c0 = tuple(0 for _ in F(2)[0]); c1 = tuple(1 for _ in F(2)[0])
    e0 = X.cls(2, restrict(CONE, (xx, yy, c0), 2, 3, 2))
    e1 = X.cls(2, restrict(CONE, (xx, yy, c1), 2, 3, 2))
    print(f"(2) {name}: cone descends: {ha == hb}; ends "
          f"[0-end]==[const]: {e0 == X.classes[2][(c0, c0)]}, "
          f"[1-end]==[id]: {e1 == X.classes[2][gen]}", flush=True)

# (4) negative control on W (K=3 cylinder-level check)
W = Quotient(2, [(1, ((0,0),(0,1)), ((0,1),(0,0))),
                 (1, ((0,1),(0,1)), ((0,1),(1,1)))], 3)
x1_2 = tuple(p[0] for p in F(2)[0]); x2_2 = tuple(p[1] for p in F(2)[0])
# descent for a W-cylinder: H.(A x id) = H.(B x id) at level 3
# for the level-1 generating pairs, A x id: [2] -> [2]... A: [1]->[2]:
# A x id: [2] -> [3]; CONE_W = (x1^x2-cyl?) cone cylinder level 3:
CONE_W = (pmeet(tuple(p[0] for p in F(3)[0]), x3),
          pmeet(tuple(p[1] for p in F(3)[0]), x3))
xv = tuple(p[0] for p in F(2)[0])
A2 = ((0,0,0,1) if False else None,)
# build A2 x id: A2 = (u,u): [1]->[2]: components in F(1); lift to
# [2] -> [3]: (a1(x1), a2(x1), x2)
def liftpair(Apair):
    a1, a2 = Apair
    f1 = tuple(a1[p[0]] for p in F(2)[0])
    f2 = tuple(a2[p[0]] for p in F(2)[0])
    return (f1, f2, x2_2)
A2p = ((0, 1), (0, 1))
B2p = ((0, 1), (1, 1))
ha = W.cls(2, restrict(CONE_W, liftpair(A2p), 2, 3, 2))
hb = W.cls(2, restrict(CONE_W, liftpair(B2p), 2, 3, 2))
print(f"(4) W dunce hat: cone descends along (u,u)~(u,1): "
      f"{ha == hb} (expect False)", flush=True)
