"""O28: extract the explicit 2-step strict contractions of the
two M-fold quotients (witness formulas for the paper and for the
general (k,m) statement)."""
import sys, itertools, time
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, restrict, Quotient
from collections import defaultdict, deque

K = 4
pts_k, _ = F(2)
gen = tuple(tuple(p[i] for p in pts_k) for i in range(2))
t1 = ((0,0,0,0,0,0,1,1), (0,0,0,0,0,1,0,1))
t2 = ((0,0,0,1,0,0,1,1), (0,0,0,1,0,1,0,1))
u1 = ((0,0,0,0,0,0,1,1), (0,0,0,1,0,0,0,1))
u2 = ((0,0,0,0,0,1,1,1), (0,0,0,1,0,1,0,1))

NAMES3 = {}
def poly_name(f, m):
    """crude readable name for f in F(m)"""
    pts, _ = F(m)
    ones = [p for p, v in zip(pts, f) if v]
    if not ones: return "0"
    if len(ones) == len(pts): return "1"
    # minimal elements of the upset
    mins = [p for p in ones
            if not any(q != p and all(a <= b for a, b in zip(q, p))
                       for q in ones)]
    terms = []
    for p in mins:
        vs = [f"x{i+1}" for i, b in enumerate(p) if b]
        terms.append("^".join(vs) if vs else "1")
    return " v ".join(terms)

def analyze(name, A, B):
    t0 = time.time()
    X = Quotient(2, [(3, A, B)], K)
    print(f"{name}: built ({time.time()-t0:.0f}s)", flush=True)
    pts4, _ = F(4)
    def lift(f3):
        return tuple(f3[p[0]*4 + p[1]*2 + p[2]] for p in pts4)
    x4 = tuple(p[3] for p in pts4)
    Aid = (lift(A[0]), lift(A[1]), x4)
    Bid = (lift(B[0]), lift(B[1]), x4)
    cyls = [H for H in X.level(3)
            if X.cls(4, restrict(H, Aid, 2, 3, 4)) ==
               X.cls(4, restrict(H, Bid, 2, 3, 4))]
    xx = tuple(p[0] for p in F(2)[0]); yy = tuple(p[1] for p in F(2)[0])
    c0 = tuple(0 for _ in F(2)[0]); c1 = tuple(1 for _ in F(2)[0])
    edges = defaultdict(list)
    for H in cyls:
        h0 = X.cls(2, restrict(H, (xx, yy, c0), 2, 3, 2))
        h1 = X.cls(2, restrict(H, (xx, yy, c1), 2, 3, 2))
        edges[h0].append((h1, H)); edges[h1].append((h0, H))
    start = X.classes[2][gen]
    consts = {X.classes[2][(c0, c0)], X.classes[2][(c1, c1)],
              X.classes[2][(c0, c1)], X.classes[2][(c1, c0)]}
    seen = {start: (None, None)}
    dq = deque([start])
    goal = None
    while dq and goal is None:
        c = dq.popleft()
        for d, H in edges[c]:
            if d not in seen:
                seen[d] = (c, H); dq.append(d)
                if d in consts: goal = d; break
    path = []
    c = goal
    while seen[c][0] is not None:
        path.append((seen[c][1], c)); c = seen[c][0]
    path.reverse()
    print(f"  contraction path ({len(path)} cylinders):", flush=True)
    cur = start
    for H, nxt in path:
        e0 = X.cls(2, restrict(H, (xx, yy, c0), 2, 3, 2))
        e1 = X.cls(2, restrict(H, (xx, yy, c1), 2, 3, 2))
        print(f"    cylinder H = ({poly_name(H[0],3)} , "
              f"{poly_name(H[1],3)})", flush=True)
        print(f"      ends: ({poly_name(e0[0],2)},{poly_name(e0[1],2)})"
              f"  ->  ({poly_name(e1[0],2)},{poly_name(e1[1],2)})",
              flush=True)
        cur = nxt

analyze("shape#0 (m1,m2)~(m1vm3,m2vm3)", t1, t2)
analyze("shape#1 (m1,m3)~(m1vm2,m3vm2)", u1, u2)
