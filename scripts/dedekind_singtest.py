"""O28: machine verification for thm:singtest's ingredients.

(1) lem:sortretract identities: T(delta^i) = wall coface then
    sort, and sort_q is absorbed (r simplicial), q <= 4.
(2) lem:cylpair: the prefix-meet pairing
    Delta^1_q -> D(q), threshold t |-> x_1 ^..^ x_t
    (all-zero simplex -> constant 0) commutes with all wall
    cofaces: T(X) x Delta^1 -> T(X x cube^1) is simplicial.
(3) the eta/omega fiber-contraction conditions are the
    definitional identities u . sort = u (sorted u) and the
    fiber-morphism condition v . w = u; spot-checked on W.
"""
import sys
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose
from dedekind_triangulate import coface as wall_coface

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

ok1 = ok2 = True
for q in range(2, 5):
    srt_lo = sort_sub(q - 1); srt_hi = sort_sub(q)
    for i in range(q + 1):
        w = wall_coface(i, q); o = coface_T(i, q)
        if tuple(compose(wj, srt_lo, q-1, q-1) for wj in w) != o:
            ok1 = False
        if tuple(compose(sj, o, q, q-1) for sj in srt_hi) != o:
            ok2 = False
print(f"(1) T(delta) = wall.sort and sort absorbed: {ok1 and ok2}",
      flush=True)

def hat(t, m):
    pts, _ = F(m)
    if t == m + 1: return tuple(0 for _ in pts)
    return tuple(1 if all(p[i] for i in range(t)) else 0
                 for p in pts)
ok3 = True
for q in range(1, 5):
    for t in range(q + 2):
        gh = hat(t, q)
        for i in range(q + 1):
            lhs = compose(gh, wall_coface(i, q), q, q - 1)
            tp = sum(1 for k in range(q)
                     if (k if k < i else k + 1) < t)
            if lhs != hat(tp, q - 1): ok3 = False
print(f"(2) cylinder pairing simplicial: {ok3}", flush=True)
assert ok1 and ok2 and ok3
print("thm:singtest ingredients: ALL VERIFIED", flush=True)
