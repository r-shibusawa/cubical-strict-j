"""CLOSED-FORM separation criterion for cube^n/H (O18, section 75).

    R(H) := { h in H : h fixes a cell }
          = { h != 1 : every cycle of h has even sign-sum }
          = { h != 1 : h fixes a vertex of {0,1}^n }.

R(H) is stable under H-conjugation (conjugation preserves cycle type and
cycle sign-sums), so  D(H) := <R(H)>  is NORMAL in H and equals the
normal closure of the reflections; the reflection-derived series
therefore stabilises after ONE step.  The criterion is

  ***  cube^n / H  SEPARATES   <=>   the reflections of H have no
       common fixed vertex   (equivalently: D(H) is mixed).  ***

Checks performed here, for n <= 4 (all 2 / 10 / 98 / 1659 subgroups):
  (0) fixes-a-cell <=> fixes-a-vertex <=> all cycles even (C1);
  (1) R(H) conjugation-stable, D(H) normal, D(D(H)) = D(H);
  (2) the criterion agrees with the reflection-derived-series form;
  (3) n = 3 reproduces the complete De Morgan classification of paper 14
      (78 AGREE / 20 SEP, separating orders 4^3 8^9 12 16^3 24^3 48);
  (4) consistency with every previously proved mechanism:
      free / fixed / product / median-block / character tower / P'';
  (5) census for n = 4.
"""
import itertools
from collections import deque, Counter

def build(n):
    ELEMS = [(p, s) for p in itertools.permutations(range(n))
             for s in itertools.product((0, 1), repeat=n)]
    idx = {e: i for i, e in enumerate(ELEMS)}
    NE = len(ELEMS); ID = idx[(tuple(range(n)), (0,)*n)]
    def mmr(e1, e2):
        (p1, s1), (p2, s2) = e1, e2
        return (tuple(p2[p1[i]] for i in range(n)),
                tuple(s1[i] ^ s2[p1[i]] for i in range(n)))
    MUL = [[idx[mmr(ELEMS[a], ELEMS[b])] for b in range(NE)] for a in range(NE)]
    INV = [next(b for b in range(NE) if MUL[a][b] == ID) for a in range(NE)]
    def cyc(e):
        p, s = e; seen = [False]*n; out = []
        for i in range(n):
            if seen[i]: continue
            sg = s[i]; j = p[i]; seen[i] = True; L = 1
            while j != i:
                seen[j] = True; sg ^= s[j]; j = p[j]; L += 1
            out.append((L, sg & 1))
        return out
    REFL = [a != ID and all(g == 0 for _, g in cyc(ELEMS[a])) for a in range(NE)]
    ACT = []
    for a in range(NE):
        p, s = ELEMS[a]
        ACT.append([sum(((((v >> p[i]) & 1) ^ s[i]) << i) for i in range(n))
                    for v in range(1 << n)])
    return ELEMS, idx, ID, NE, MUL, INV, REFL, ACT, cyc

def all_subgroups(NE, ID, MUL):
    def close(gens):
        S = {ID}; dq = deque([ID])
        while dq:
            x = dq.popleft()
            for g in gens:
                y = MUL[x][g]
                if y not in S: S.add(y); dq.append(y)
        return frozenset(S)
    subs = {frozenset([ID]): []}
    frontier = list(subs.items())
    while frontier:
        new = []
        for H, gens in frontier:
            for g in range(NE):
                if g in H: continue
                H2 = close(gens + [g])
                if H2 not in subs:
                    subs[H2] = gens + [g]; new.append((H2, gens + [g]))
        frontier = new
    return subs, close

def run(n):
    ELEMS, idx, ID, NE, MUL, INV, REFL, ACT, cyc = build(n)
    subs, close = all_subgroups(NE, ID, MUL)

    # ---- (0) fixes a cell <=> fixes a vertex <=> all cycles even ----
    # a cell is a tuple of n Boolean functions; h.c = c forces, on each
    # cycle, the sign-sum to vanish (else c = ~c); conversely propagate a
    # constant along each cycle => a FIXED VERTEX.
    for a in range(NE):
        vfix = any(ACT[a][v] == v for v in range(1 << n))
        assert vfix == (a == ID or REFL[a]), "C1 fails"

    def fixv(S):
        return [v for v in range(1 << n) if all(ACT[a][v] == v for a in S)]
    def D(H):
        R = [a for a in H if REFL[a]]
        return close(R) if R else frozenset([ID]), R

    # ---- (1) conjugation stability, normality, one-step stabilisation ----
    for H in subs:
        R = set(a for a in H if REFL[a])
        for g in H:
            assert {MUL[MUL[g][a]][INV[g]] for a in R} == R, "R not stable"
        Dh, _ = D(H)
        for g in H:
            assert {MUL[MUL[g][a]][INV[g]] for a in Dh} == set(Dh), "D not normal"
        assert D(Dh)[0] == Dh, "series not stable in one step"

    # ---- (2)(3) the criterion ----
    def kind(H):
        if len(H) == 1: return 'trivial'
        if not any(REFL[a] for a in H): return 'free'
        return 'fixed' if fixv(H) else 'mixed'
    fate = {}
    for H in subs:
        Dh, R = D(H)
        crit = 'SEP' if (R and not fixv(R)) else 'AGREE'
        assert crit == ('SEP' if kind(Dh) == 'mixed' else 'AGREE')
        fate[H] = crit
    sep = [H for H in subs if fate[H] == 'SEP']
    print(f"n={n}: subgroups={len(subs)}  "
          f"AGREE={len(subs)-len(sep)}  SEP={len(sep)}")
    print(f"      SEP orders: {dict(sorted(Counter(len(H) for H in sep).items()))}")
    print(f"      taxonomy:   {dict(sorted(Counter(kind(H) for H in subs).items()))}")
    if n == 3:
        assert len(sep) == 20 and len(subs) - len(sep) == 78, "paper 14 mismatch"
        assert dict(sorted(Counter(len(H) for H in sep).items())) == \
            {4: 3, 8: 9, 12: 1, 16: 3, 24: 3, 48: 1}, "order distribution"
        print("      == paper 14 De Morgan classification reproduced ==")

    # ---- (4) consistency with the previously proved mechanisms ----
    def orbits(H):
        par = list(range(n))
        def f(i):
            while par[i] != i: par[i] = par[par[i]]; i = par[i]
            return i
        for a in H:
            p, _ = ELEMS[a]
            for i in range(n):
                ra, rb = f(i), f(p[i])
                if ra != rb: par[ra] = rb
        gr = {}
        for i in range(n): gr.setdefault(f(i), []).append(i)
        return sorted(tuple(v) for v in gr.values())
    def restrict(a, B):
        p, s = ELEMS[a]
        q = list(range(n)); t = [0]*n
        for i in B: q[i] = p[i]; t[i] = s[i]
        return idx[(tuple(q), tuple(t))]
    nprod = nmed = ntow = ncert = ndeg = 0
    for H in subs:
        if len(H) == 1: continue
        f0 = fate[H]
        # free / fixed
        if kind(H) in ('free', 'fixed'): assert f0 == 'AGREE'
        # product: SEP <=> some factor SEP  (factors read inside B_n)
        orb = orbits(H)
        for r in range(1, len(orb)):
            for sel in itertools.combinations(range(len(orb)), r):
                A = [i for k in sel for i in orb[k]]
                if all(restrict(a, A) in H for a in H):
                    HA = frozenset(restrict(a, A) for a in H)
                    B = [i for i in range(n) if i not in A]
                    HB = frozenset(restrict(a, B) for a in H)
                    assert (f0 == 'SEP') == (fate[HA] == 'SEP' or
                                             fate[HB] == 'SEP'), "product rule"
                    nprod += 1
        # character tower: any subgroup M containing all reflections has
        # the same fate (in particular kernels of slot-orbit characters)
        Dh, R = D(H)
        for M in subs:
            if M <= H and Dh <= M:
                assert fate[M] == f0, "tower/descent invariance"
                if M != H: ntow += 1
        # P'': reflection-generated mixed <=> certified => SEP
        if Dh == H and kind(H) == 'mixed':
            ncert += 1; assert f0 == 'SEP'
        if kind(H) == 'mixed' and Dh != H and kind(Dh) == 'fixed':
            ndeg += 1; assert f0 == 'AGREE'
    print(f"      cross-checks: product splits {nprod}, "
          f"reflection-full subgroups {ntow}, reflection-generated mixed "
          f"{ncert}, degenerate mixed {ndeg}  -- all consistent")
    return fate

for n in (1, 2, 3, 4):
    run(n)


# ============================================================
# (6) polynomial-time form + (7) spot checks against the named
#     groups of sections 43, 48, 72, 73, 74
# ============================================================
print()
print("(6) parity union-find form:  SEP(H)  <=>  the F2-system")
print("        v_i + v_{p_r(i)} = s_r(i)   (r a reflection of H)")
print("    is INCONSISTENT.  (linear in |R| n, no 2^n search)")

def uf_inconsistent(R, n):
    par = list(range(n)); pr = [0]*n
    def find(i):
        acc = 0
        while par[i] != i: acc ^= pr[i]; i = par[i]
        return i, acc
    for (p, s) in R:
        for i in range(n):
            (ra, pa), (rb, pb) = find(i), find(p[i])
            if ra == rb:
                if (pa ^ pb) != s[i]: return True
            else:
                par[ra] = rb; pr[ra] = pa ^ pb ^ s[i]
    return False

for n in (2, 3, 4):
    ELEMS, idx, ID, NE, MUL, INV, REFL, ACT, cyc = build(n)
    subs, close = all_subgroups(NE, ID, MUL)
    bad = 0
    for H in subs:
        R = [a for a in H if REFL[a]]
        brute = bool(R) and not any(all(ACT[a][v] == v for a in R)
                                    for v in range(1 << n))
        if brute != (bool(R) and uf_inconsistent([ELEMS[a] for a in R], n)):
            bad += 1
    print(f"    n={n}: union-find form agrees with the vertex test on all "
          f"{len(subs)} subgroups ({bad} mismatches)")

print()
print("(7) named groups")
n = 4
ELEMS, idx, ID, NE, MUL, INV, REFL, ACT, cyc = build(4)
_, close4 = all_subgroups(0, ID, MUL) if False else (None, None)
def close_g(gens):
    S = {ID}; dq = deque([ID]); gi = [idx[g] for g in gens]
    while dq:
        x = dq.popleft()
        for g in gi:
            y = MUL[x][g]
            if y not in S: S.add(y); dq.append(y)
    return frozenset(S)
Veven = [(tuple(range(4)), s) for s in itertools.product((0, 1), repeat=4)
         if sum(s) % 2 == 0 and any(s)]
c4 = ((1, 2, 3, 0), (0, 0, 0, 0)); dt1 = ((1, 0, 3, 2), (0, 0, 0, 0))
dt2 = ((2, 3, 0, 1), (0, 0, 0, 0)); sw13 = ((0, 3, 2, 1), (0, 0, 0, 0))
rot3 = ((1, 2, 0, 3), (0, 0, 0, 0)); sw01 = ((1, 0, 2, 3), (0, 0, 0, 0))
named = [
    ("V_even4 : C4  (primitive, certified)", Veven + [c4]),
    ("V_even4 : K4  (primitive, certified)", Veven + [dt1, dt2]),
    ("V_even4 : D4  (primitive, certified)", Veven + [c4, sw13]),
    ("V_even4 : A4  (primitive, certified)", Veven + [dt1, rot3]),
    ("V_even4 : S4  (primitive, certified)", Veven + [c4, sw01]),
    ("V_even4 : S3 x 1 (uncertified, tower)", Veven + [rot3, sw01]),
    ("B_4 (full)", [c4, sw01, ((0, 1, 2, 3), (1, 0, 0, 0))]),
]
for name, gens in named:
    H = close_g(gens)
    R = [ELEMS[a] for a in H if REFL[a]]
    v = uf_inconsistent(R, 4) if R else False
    D = close_g([ELEMS[a] for a in H if REFL[a]]) if R else frozenset([ID])
    print(f"    {name:42s} |H|={len(H):4d} |<R>|={len(D):4d} "
          f"#R={len(R):4d} -> {'SEP' if v else 'AGREE'}"
          f"{'  (reflection-generated)' if D == H else ''}")


# ============================================================
# (8) the terms behind the AGREE mechanisms (site-uniform: all are
#     De Morgan / Kleene / Boolean terms in AND, OR, NOT)
# ============================================================
print()
def F(d, a, t):            # self-dual multiplexer
    return (d & ~t & 1) | (a & t) | (d & a)
ok = all(F(d, a, 0) == d and F(d, a, 1) == a and
         (1 - F(d, a, t)) == F(1-d, 1-a, t)
         for d in (0, 1) for a in (0, 1) for t in (0, 1))
print(f"(8) mux F(d,a,t)=(d&~t)|(a&t)|(d&a): F(.,.,0)=d, F(.,.,1)=a, "
      f"~F(d,a,t)=F(~d,~a,t)  -> {ok}")
def maj(bits):
    return 1 if sum(bits) * 2 > len(bits) else 0
ok2 = True
for m in (1, 3, 5):
    for bits in itertools.product((0, 1), repeat=m):
        if maj([1-b for b in bits]) != 1 - maj(bits): ok2 = False
        for p in itertools.permutations(range(m)):
            if maj([bits[p[i]] for i in range(m)]) != maj(bits): ok2 = False
print(f"    majority on odd blocks: self-dual and symmetric (m=1,3,5) "
      f"-> {ok2}")
print("    => MEDIAN BLOCK REDUCTION: for an H-invariant partition P of "
      "the slots\n       with all blocks odd and every sign vector "
      "constant on blocks,\n       mu = blockwise majority and the "
      "diagonal d are H-equivariant,\n       mu.d = id and "
      "F(x_i, maj_{b(i)}(x), t) is an H-equivariant homotopy\n"
      "       d.mu ~ id, so cube^n/H = cube^|P|/Hbar.")
