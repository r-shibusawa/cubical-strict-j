"""O28 stage 5e: STRICT contraction of the fold-quotient shapes,
with the descent condition (level 4).

For the two distinct (2,3) fold-quotient shapes Q = cube^2/(t~t'):
maps Q x cube^1 -> Q are the level-3 classes H whose level-4
restrictions satisfy H.(t x id) = H.(t' x id)
(lem:strictification).  BFS the strict-homotopy graph on
endomorphism classes from [id_Q] = [gen]: does it reach a
constant?  If yes, Q is strictly contractible -- type-
contractible outright, and the witness cylinders give formulas.
"""
import sys, itertools, time
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, restrict, Quotient
from collections import defaultdict, deque

K = 4
k, m = 2, 3
_, Dm = F(m); _, Dk = F(k)
pts_k, _ = F(k)
gen = tuple(tuple(p[i] for p in pts_k) for i in range(k))

t1 = ((0,0,0,0,0,0,1,1), (0,0,0,0,0,1,0,1))          # (x^y, x^z)
t2 = ((0,0,0,1,0,0,1,1), (0,0,0,1,0,1,0,1))          # v-shifted
u1 = ((0,0,0,0,0,0,1,1), (0,0,0,1,0,0,0,1))          # shape#1 rep
u2 = ((0,0,0,0,0,1,1,1), (0,0,0,1,0,1,0,1))

def analyze(name, A, B):
    t0 = time.time()
    X = Quotient(2, [(3, A, B)], K)
    print(f"{name}: quotient built ({time.time()-t0:.0f}s), "
          f"sizes {[len(X.level(q)) for q in range(K+1)]}",
          flush=True)
    # descent condition for cylinders: H in X(3) with
    # H.(A x id) = H.(B x id) in X(4).
    # (A x id): [4] -> [3]: components (A1, A2 as F(4)-lifted, x4)
    pts4, _ = F(4)
    def lift(f3):   # F(3) element -> F(4) ignoring last var
        return tuple(f3[sum(1 << (2 - i) for i in range(3)
                     if p[i]) if False else 0] for p in pts4) if False \
            else tuple(f3[p[0]*4 + p[1]*2 + p[2]] for p in pts4)
    x4 = tuple(p[3] for p in pts4)
    Aid = (lift(A[0]), lift(A[1]), x4)
    Bid = (lift(B[0]), lift(B[1]), x4)
    cyls = []
    for H in X.level(3):
        ha = X.cls(4, restrict(H, Aid, 2, 3, 4))
        hb = X.cls(4, restrict(H, Bid, 2, 3, 4))
        if ha == hb: cyls.append(H)
    print(f"  strict Q-cylinders: {len(cyls)} of "
          f"{len(X.level(3))}", flush=True)
    # endo classes: elements s in X(2) with kernel >= K:
    # s.(A) = s.(B) at level 3
    endos = []
    for s in X.level(2):
        if X.cls(3, restrict(s, A, 2, 2, 3)) == \
           X.cls(3, restrict(s, B, 2, 2, 3)):
            endos.append(s)
    print(f"  strict endos of Q: {len(endos)} of "
          f"{len(X.level(2))}", flush=True)
    # homotopy graph
    xx = tuple(p[0] for p in F(2)[0]); yy = tuple(p[1] for p in F(2)[0])
    c0 = tuple(0 for _ in F(2)[0]); c1 = tuple(1 for _ in F(2)[0])
    ends = defaultdict(set)
    for H in cyls:
        h0 = X.cls(2, restrict(H, (xx, yy, c0), 2, 3, 2))
        h1 = X.cls(2, restrict(H, (xx, yy, c1), 2, 3, 2))
        ends[h0].add(h1); ends[h1].add(h0)
    start = X.classes[2][gen]
    seen = {start}; dq = deque([start])
    parent = {start: None}
    while dq:
        c = dq.popleft()
        for d in ends[c]:
            if d not in seen:
                seen.add(d); parent[d] = c; dq.append(d)
    consts = {X.classes[2][(c0, c0)], X.classes[2][(c1, c1)],
              X.classes[2][(c0, c1)], X.classes[2][(c1, c0)]}
    hit = seen & consts
    print(f"  id_Q ~ const (with descent): {bool(hit)}; "
          f"reachable endo classes {len(seen)}", flush=True)
    if hit:
        # path length
        c = next(iter(hit)); n = 0
        while parent[c] is not None: c = parent[c]; n += 1
        print(f"  contraction in {n} strict steps", flush=True)

analyze("shape#0", t1, t2)
analyze("shape#1", u1, u2)
