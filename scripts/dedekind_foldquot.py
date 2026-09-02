"""O28 stage 5d: the twelve fold-quotient shapes.

Q = cube^2/(t ~ t') for the twelve genuine fresh split pairs.
Compute: T-Betti and Sing-Betti (test data), the size profile,
whether the pairs are related by the Sigma_2 x (variable perm)
symmetries (how many distinct shapes), and a strict-contraction
probe (is [id] ~ const by substitution homotopies? -- census
stage-0 style).
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, restrict, Quotient
from dedekind_triangulate import coface as wall_coface, rank2

def o_stat_t(j, m):
    pts, _ = F(m)
    if j <= 0: return tuple(1 for _ in pts)
    if j > m: return tuple(0 for _ in pts)
    return tuple(1 if sum(p) >= j else 0 for p in pts)
def sort_sub(q): return tuple(o_stat_t(j, q) for j in range(1, q+1))
def coface_T(i, q):
    f = tuple(x if x < i else x + 1 for x in range(q))
    idx = []
    for ii in range(1, q + 1):
        ks = [kk for kk in range(q) if f[kk] >= ii]
        idx.append(min(ks) if ks else q)
    return tuple(o_stat_t(kk, q - 1) for kk in idx)
K = 3
def betti(X, n, sorted_only):
    reps = {}
    for q in range(K + 1):
        lv = X.level(q)
        if sorted_only:
            lv = [c for c in lv
                  if X.cls(q, restrict(c, sort_sub(q), n, q, q)) == c]
        reps[q] = lv
    ind = {q: {c: i for i, c in enumerate(reps[q])} for q in reps}
    cof = coface_T if sorted_only else wall_coface
    r = {}
    for q in range(1, K + 1):
        cols = []
        for cell in reps[q]:
            v = 0
            for i in range(q + 1):
                fc = X.cls(q-1, restrict(cell, cof(i,q), n, q, q-1))
                if fc not in ind[q-1]: return None
                v ^= 1 << ind[q-1][fc]
            cols.append(v)
        r[q] = rank2(cols)
    b = [len(reps[0]) - r[1]]
    for q in range(1, K):
        b.append(len(reps[q]) - r[q] - r[q+1])
    return b

def is_perm(u, n):
    pts, _ = F(n)
    projs = [tuple(p[i] for p in pts) for i in range(n)]
    return sorted(u) == sorted(projs)

# regenerate the 12 pairs
k, m = 2, 3
_, Dm = F(m); _, Dk = F(k)
pts_k, _ = F(k)
gen = tuple(tuple(p[i] for p in pts_k) for i in range(k))
cells_m = list(itertools.product(Dm, repeat=k))
secs = list(itertools.product(Dk, repeat=m))
def comp(t, w): return tuple(compose(tc, w, m, k) for tc in t)
from collections import defaultdict
sec_of = defaultdict(set)
for t in cells_m:
    for w in secs:
        if comp(t, w) == gen: sec_of[t].add(w)
split_cells = [t for t in cells_m if sec_of[t]]
pairs = []
for t in split_cells:
    for t2 in split_cells:
        if t2 <= t: continue
        if not (sec_of[t] & sec_of[t2]): continue
        X = Quotient(k, [(m, t, t2)], K)
        cls_gen = X.classes[k][gen]
        mem = [u for u, r in X.classes[k].items() if r == cls_gen]
        if all(is_perm(u, k) for u in mem):
            pairs.append((t, t2))
print(f"genuine pairs: {len(pairs)}", flush=True)

# dedup by symmetry: variable perms of [3]-level (precompose) and
# component swap (postcompose with swap of the pair coordinates)
def canon(pair):
    t, t2 = pair
    best = None
    for perm in itertools.permutations(range(3)):
        pv = tuple(tuple(p[i] for p in F(3)[0]) for i in perm)
        a = tuple(compose(c, pv, 3, 3) for c in t)
        b = tuple(compose(c, pv, 3, 3) for c in t2)
        for x, y in [(a, b), (b, a)]:
            for x2, y2 in [((x, y)), ((x[::-1], y[::-1]))]:
                cand = tuple(sorted([x2, y2]))
                if best is None or cand < best: best = cand
    return best
classes = {}
for p in pairs: classes.setdefault(canon(p), []).append(p)
print(f"distinct up to symmetry: {len(classes)}", flush=True)

for i, (cn, reps_) in enumerate(classes.items()):
    t, t2 = reps_[0]
    X = Quotient(2, [(3, t, t2)], K)
    bt = betti(X, 2, False); bs = betti(X, 2, True)
    sizes = [len(X.level(q)) for q in range(K + 1)]
    # stage-0 strict homotopy probe: is [gen] ~ constant via
    # one-step substitution homotopies? (census style, level 3)
    # cells H in X(3) with H.(x,y,0)=gen-ish? quick reachability:
    # strict cylinders = level-3 classes h with ends h0, h1 at
    # level 2 via (x,y,0),(x,y,1)
    xx = tuple(p[0] for p in F(2)[0]); yy = tuple(p[1] for p in F(2)[0])
    c0 = tuple(0 for _ in F(2)[0]); c1 = tuple(1 for _ in F(2)[0])
    ends = defaultdict(set)
    for h in X.level(3):
        h0 = X.cls(2, restrict(h, (xx, yy, c0), 2, 3, 2))
        h1 = X.cls(2, restrict(h, (xx, yy, c1), 2, 3, 2))
        ends[h0].add(h1); ends[h1].add(h0)
    # BFS from [gen]
    from collections import deque
    start = X.classes[2][gen]
    seen = {start}; dq = deque([start])
    while dq:
        c = dq.popleft()
        for d in ends[c]:
            if d not in seen: seen.add(d); dq.append(d)
    consts = {X.classes[2][(c0, c0)], X.classes[2][(c1, c1)],
              X.classes[2][(c0, c1)], X.classes[2][(c1, c0)]}
    reach = bool(seen & consts)
    print(f"shape#{i}: sizes {sizes}, T {bt}, Sing {bs}, "
          f"[gen]~const strictly: {reach}", flush=True)
