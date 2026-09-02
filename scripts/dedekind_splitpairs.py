"""O28 stage 5c: can a FRESH SPLIT-EPI pair survive minimality?

Potential gap in the extension theorem: a K-pair (t, t') whose
members are split epis (common section w, so their atoms are the
whole cube) cannot be trackified.  Claim: at a MINIMAL
presentation such pairs cannot occur -- the congruence generated
by (t, t') forces a non-invertible self-stabilizer of the
generic cell (gen ~ gen . e), contradicting minimality.

Search: for (k, m) in {(1,2), (1,3), (2,3)}: all pairs t != t'
of level-m cells of cube^k admitting a COMMON section w
(t o w = t' o w = id), generate the congruence of cube^k by
(t, t') (instance closure, levels <= K), and check whether the
class of the generic cell at level k contains a non-invertible
element (minimality violated) -- or the pair collapses into the
prescribed/H world some other way.  Report any pair that leaves
the generic class trivial (a genuine fresh split pair).
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, restrict, Quotient

def is_perm(u, n):
    pts, _ = F(n)
    projs = [tuple(p[i] for p in pts) for i in range(n)]
    return sorted(u) == sorted(projs)

K = 3
def search(k, m):
    _, Dm = F(m); _, Dk = F(k)
    pts_k, _ = F(k)
    projs_k = tuple(tuple(p[i] for p in pts_k) for i in range(k))
    gen = projs_k
    # level-m cells of cube^k = k-tuples over F(m); sections w =
    # m-tuples over F(k) with t o w = id
    cells_m = list(itertools.product(Dm, repeat=k))
    secs = list(itertools.product(Dk, repeat=m))
    # index: for each t, set of its sections
    def comp(t, w):
        return tuple(compose(tc, w, m, k) for tc in t)
    from collections import defaultdict
    sec_of = defaultdict(set)
    for t in cells_m:
        for w in secs:
            if comp(t, w) == gen:
                sec_of[t].add(w)
    split_cells = [t for t in cells_m if sec_of[t]]
    print(f"(k,m)=({k},{m}): split-epi cells {len(split_cells)} "
          f"of {len(cells_m)}", flush=True)
    genuine = 0; tested = 0
    for i, t in enumerate(split_cells):
        for t2 in split_cells:
            if t2 <= t: continue
            common = sec_of[t] & sec_of[t2]
            if not common: continue
            tested += 1
            X = Quotient(k, [(m, t, t2)], K)
            cls_gen = X.classes[k][gen]
            members = [u for u, r in X.classes[k].items()
                       if r == cls_gen]
            noninv = [u for u in members if not is_perm(u, k)]
            if not noninv:
                genuine += 1
                if genuine <= 5:
                    print(f"  GENUINE fresh split pair: t={t} "
                          f"t'={t2}", flush=True)
    print(f"(k,m)=({k},{m}): {tested} common-section pairs, "
          f"{genuine} keep minimality (GENUINE)", flush=True)
    return genuine

tot = 0
tot += search(1, 2)
tot += search(1, 3)
tot += search(2, 3)
print(f"TOTAL genuine fresh split pairs: {tot}", flush=True)
