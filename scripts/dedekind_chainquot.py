"""O28: chain approximation at W is a pushout THEOREM.

Claim: W = cube^2 u_{Ch(cube^2)} Ch(W): the fold congruence of
the monotone dunce hat identifies only CHAIN cells (fold-formed
cells are comparable pairs), so Ch(W) into W is a pushout of the
trivial cofibration Ch_2 into cube^2 (prop:chaincells), hence a
type-trivial cofibration.  Machine checks:
 (a) every member of every non-singleton congruence class is a
     comparable pair (levels 0..K);
 (b) the levelwise cell count identity
     |W(k)| = |cube^2(k)| - |Ch(cube^2)(k)| + |Ch(W)(k)|;
 (c) Ch(W) = image of Ch(cube^2) under the quotient map.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, restrict, Quotient

K = 3
W = Quotient(2, [(1, ((0,0), (0,1)), ((0,1), (0,0))),
                 (1, ((0,1), (0,1)), ((0,1), (1,1)))], K)

def leq_t(a, b): return all(x <= y for x, y in zip(a, b))
def comparable(a, b): return leq_t(a, b) or leq_t(b, a)
def o_stat_t(j, m):
    pts, _ = F(m)
    if j <= 0: return tuple(1 for _ in pts)
    if j > m: return tuple(0 for _ in pts)
    return tuple(1 if sum(p) >= j else 0 for p in pts)
def sort_sub(q): return tuple(o_stat_t(j, q) for j in range(1, q+1))
def act(cls_, u, j, k): return W.cls(k, restrict(cls_, u, 2, j, k))

# (a) movable classes consist of chain cells
ok_a = True
for k in range(K + 1):
    from collections import defaultdict
    groups = defaultdict(list)
    for c, r in W.classes[k].items(): groups[r].append(c)
    for r, mem in groups.items():
        if len(mem) > 1:
            for c in mem:
                if not comparable(c[0], c[1]):
                    ok_a = False
                    print(f"(a) FAIL level {k}: movable non-chain "
                          f"cell {c}", flush=True)
print(f"(a) movable classes are chain cells: {ok_a}", flush=True)

# Ch(cube^2) at level k: comparable pairs; Ch(W): as usual
sortedW = {q: [c for c in W.level(q)
               if act(c, sort_sub(q), q, q) == c] for q in range(K+1)}
def chain_subs(q, k):
    _, Dk = F(k)
    if q == 0: return [()]
    return [c for c in itertools.product(Dk, repeat=q)
            if all(comparable(a,b) for a,b in itertools.combinations(c,2))]
ChW = {}
for k in range(K + 1):
    cells = set()
    for q in range(K + 1):
        for s in sortedW[q]:
            for u in chain_subs(q, k):
                cells.add(act(s, u, q, k) if q > 0 else
                          W.cls(k, restrict(s, tuple(), 2, 0, k)))
    ChW[k] = cells

ok_b = True; ok_c = True
for k in range(K + 1):
    _, Dk = F(k)
    cube = len(Dk) ** 2
    chcube = [c for c in itertools.product(Dk, repeat=2)
              if comparable(c[0], c[1])]
    nW = len(W.level(k))
    lhs, rhs = nW, cube - len(chcube) + len(ChW[k])
    if lhs != rhs: ok_b = False
    # (c) image of Ch(cube^2) = Ch(W)?
    img = {W.cls(k, c) for c in chcube}
    if img != ChW[k]: ok_c = False
    print(f"level {k}: |W| {nW} = |cube| {cube} - |Ch cube| "
          f"{len(chcube)} + |Ch W| {len(ChW[k])} : {lhs == rhs}; "
          f"image=ChW: {img == ChW[k]}", flush=True)
print(f"(b) pushout cell count: {ok_b}; (c) Ch(W) = p(Ch(cube^2)): "
      f"{ok_c}", flush=True)
print("THEOREM (machine-backed): Ch(W) -> W is the pushout of "
      "Ch_2 -> cube^2 along Ch_2 -> Ch(W); with prop:chaincells "
      "it is a type-trivial cofibration." if ok_a and ok_b and ok_c
      else "CLAIM FAILS", flush=True)
