"""O28 stage 7b: hunt the infinite-descent mechanism.

An infinite strictly descending chain of atoms must drop cell
sets at unboundedly high levels while stabilizing every fixed
level.  The enabling mechanism: strict containments A > A' with
IDENTICAL cells at low levels.  Hunt in cube^3: pairs with equal
level<=2 cell sets, A generated at level 3, A' at level 4,
A' <= A strict.  Also test level<=3 equality for found pairs.
"""
import sys, itertools, random, time
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose

def rest(cell, u, j, k):
    return tuple(compose(c, u, j, k) for c in cell)
def atom_cells(z, m, n, k):
    _, Dk = F(k)
    return frozenset(rest(z, u, m, k)
                     for u in itertools.product(Dk, repeat=m))

n = 3
random.seed(23)
t0 = time.time()
# level-3-generated atoms (sampled), fingerprint level <= 2
_, D3 = F(3)
gens3 = random.sample(list(itertools.product(D3, repeat=3)), 1500)
atoms3 = {}
for z in gens3:
    fp = (atom_cells(z, 3, n, 1), atom_cells(z, 3, n, 2))
    atoms3.setdefault(fp, z)
print(f"level-3 atoms sampled: {len(atoms3)} distinct fingerprints "
      f"({time.time()-t0:.0f}s)", flush=True)

# for each level-3 atom A: its level-4 cells; pick instances z' in
# A(4); z' generates A' <= A; strict iff z (gen of A) not in A'(3);
# flat iff fingerprints equal
flat_strict = 0; tested = 0; examples = []
_, D4 = F(4)
for fp, z in list(atoms3.items())[:120]:
    A4 = {rest(z, tuple(random.choice(D4) for _ in range(3)), 3, 4)
          for _ in range(60)}
    for z2 in A4:
        tested += 1
        fp2 = (atom_cells(z2, 4, n, 1), atom_cells(z2, 4, n, 2))
        if fp2 != fp: continue
        # strictness: z in <z2>(3)? early-exit search over subs
        _, Dk3 = F(3)
        strict = True
        for u in itertools.product(Dk3, repeat=4):
            if rest(z2, u, 4, 3) == z:
                strict = False; break
        if strict:
            flat_strict += 1
            if len(examples) < 3: examples.append((z, z2))
    if time.time() - t0 > 480: break
print(f"tested {tested} level-4 instances; FLAT STRICT pairs "
      f"(equal <=2 fingerprint, strict drop): {flat_strict}",
      flush=True)
for z, z2 in examples:
    eq3 = atom_cells(z2, 4, n, 3) == atom_cells(z, 3, n, 3)
    print(f"  example: level-3 sets equal too: {eq3}", flush=True)
