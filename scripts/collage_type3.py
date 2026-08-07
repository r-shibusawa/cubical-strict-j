"""(T-C) part 3: feasibility census for the double-diagonal cut.

Candidate fundamental domain: the "bottom triangle" cell
  b = (u, v & u & ~u)  in  cube^2([2]),
with K-translates  swb = sw.b, tb = nb.b, rb = g.b.
Census at levels 1 and 2 of the four generated subpresheaves
  B(m) = { b∘f : f in DM(m)^2 } etc.:
  - sizes, pairwise intersections (the gluing loci),
  - whether the union covers cube^2 (it does not: generic cell),
  - the K-stabilizer pattern on the union's cells.
"""
from collage_type_lib import build, monotone_masks, NOT, gen

for n in (1, 2):
    N, leq, rho = build(n)
    dm = monotone_masks(N, leq)
    notf = {m: NOT(m, N, rho) for m in dm}
    def tri(phi, psi):          # (u,v) |-> (u, v&u&~u) applied to (phi,psi)
        return (phi, psi & phi & notf[phi])
    cells = set()
    for phi in dm:
        for psi in dm:
            cells.add(tri(phi, psi))
    B = cells
    SW = {(y, x) for (x, y) in B}
    TB = {(notf[x], notf[y]) for (x, y) in B}
    RB = {(y, x) for (x, y) in TB}
    ALL = set((x, y) for x in dm for y in dm)
    U = B | SW | TB | RB
    print(f"level {n}: |cells|={len(ALL)}, |B|={len(B)}, |union|={len(U)}, "
          f"covers: {U == ALL}")
    print(f"  B∩SW={len(B & SW)}, B∩TB={len(B & TB)}, B∩RB={len(B & RB)}, "
          f"SW∩TB={len(SW & TB)}, SW∩RB={len(SW & RB)}, TB∩RB={len(TB & RB)}, "
          f"4-fold={len(B & SW & TB & RB)}")
    # stabilizer pattern on union cells
    fixed_sw = sum(1 for (x, y) in U if (y, x) == (x, y))
    fixed_g  = sum(1 for (x, y) in U if (notf[y], notf[x]) == (x, y))
    fixed_nb = sum(1 for (x, y) in U if (notf[x], notf[y]) == (x, y))
    print(f"  union cells fixed by sw: {fixed_sw}, by g: {fixed_g}, by nb: {fixed_nb}")
    # is the generic cell (x,y) covered?
    X, Y = gen(0, n, N), gen(1, n, N) if n >= 2 else (None, None)
    if n == 2:
        print("  generic (x,y) in union:", (X, Y) in U)
