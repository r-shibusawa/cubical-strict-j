"""Forensics (O22): why is the identity of cand-05 homotopy-
isolated?  Enumerate all stage-1-universe level-3 cells H whose
t=0 slice is the identity node, and classify WHERE the homotopy-
descent fails: which level k, which congruence group, W-vs-fresh
mismatch, etc.  Goal: extract the invariant law."""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, cube_cells, all_maps, restrict, Quotient
from dedekind_stage1 import Stage1, const_f, var_f
from collections import Counter

K = 3
c00 = const_f(1,0); x1 = var_f(1,0); c11 = const_f(1,1)
idents = [(1, (c00, x1), (x1, c00)), (1, (x1, x1), (x1, c11))]
W = Quotient(2, idents, K)
S = Stage1(W)
idnode = ('w', W.cls(2, (var_f(2,0), var_f(2,1))))

lvl3 = S.level(3)
stats = Counter(); examples = {}
n_with_id0 = 0
for H in lvl3:
    s0 = S.restrict_cell(H, (var_f(2,0), var_f(2,1), const_f(2,0)),
                         3, 2)
    if s0 != idnode: continue
    n_with_id0 += 1
    # find first failing descent condition
    fail = None
    for k in range(0, 3):
        groups = {}
        for u in all_maps(2, k):
            groups.setdefault(W.cls(k, u), []).append(u)
        for gid, g in enumerate(groups.values()):
            if len(g) < 2: continue
            exts = []
            for u in g:
                ptsk1 = F(k+1)[0]; ptsk = F(k)[0]
                idxk = {q: t for t, q in enumerate(ptsk)}
                lift = tuple(tuple(comp[idxk[q[:-1]]] for q in ptsk1)
                             for comp in u)
                tvar = tuple(q[-1] for q in ptsk1)
                exts.append(S.restrict_cell(H, lift + (tvar,),
                                            3, k+1))
            if any(e != exts[0] for e in exts[1:]):
                kinds = tuple(sorted({e[0] for e in exts}))
                fail = (k, kinds)
                break
        if fail: break
    if fail is None:
        s1 = S.restrict_cell(H, (var_f(2,0), var_f(2,1),
                                 const_f(2,1)), 3, 2)
        stats[('VALID', s1[0])] += 1
        examples.setdefault('VALID', H)
    else:
        stats[fail] += 1
        examples.setdefault(fail, H)
print(f"H-cells with slice0 = id: {n_with_id0}")
for key, cnt in sorted(stats.items(), key=lambda kv: -kv[1]):
    print(f"  {key}: {cnt}")
# for the most common failure, show a concrete example's data
if stats:
    key = max((k for k in stats if k[0] != 'VALID'),
              key=lambda k: stats[k], default=None)
    if key:
        H = examples[key]
        print("example failing H kind:", H[0],
              ("(box %d)" % H[1]) if H[0]=='n' else "")
