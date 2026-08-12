"""Mayer-Vietoris rank tables for el(cube^3/B3), el(W_H8), el(W_H24).

Reproduces the F2-cohomology dimensions quoted in the classification
paper (Theorem on H^k(el(cube^3/B3)) = 1,1,2 and the last-two-classes
theorem: H8 -> 1,1,2 / H24 -> 1,2,4), including the degree-3 step for
B3 via the pullback of the full 3-cocycle space Z^3(S4^rot).

Conventions: full inhomogeneous bar cochains over F2; cocycle and
coboundary spaces by exact Gaussian elimination (int bitsets); cup
products of characters by the standard formulas.  Requires only NumPy
(and only for coho_lib's small-vector variant; this driver uses pure
Python ints).
"""
import itertools, collections

n = 3
ELEMS = []
for _perm in itertools.permutations(range(n)):
    for _signs in itertools.product((0, 1), repeat=n):
        ELEMS.append((_perm, _signs))
ID = (tuple(range(n)), (0,)*n)
def mm(e1, e2):
    (p1, s1), (p2, s2) = e1, e2
    return (tuple(p2[p1[i]] for i in range(n)),
            tuple(s1[i] ^ s2[p1[i]] for i in range(n)))
G_all = sorted(ELEMS)
N = len(G_all)
gi = {h: i for i, h in enumerate(G_all)}
MUL = [[gi[mm(a, b)] for b in G_all] for a in G_all]
IDi = gi[ID]


# ---------- generic F2 cochain machinery on a subgroup (int bitsets) ----

def sub_mul(sub):
    pos = {x: i for i, x in enumerate(sub)}
    return pos, [[pos[MUL[a][b]] for b in sub] for a in sub]

def cocycle_basis(mul, m, d):
    """basis of Z^d as ints over m^d bit positions"""
    piv = {}
    def red(v):
        while v:
            l = v.bit_length() - 1
            if l in piv: v ^= piv[l]
            else: return l, v
        return None
    if d == 1:
        nv = m
        for g in range(m):
            for h in range(m):
                v = (1 << g) ^ (1 << h) ^ (1 << mul[g][h])
                if v:
                    r = red(v)
                    if r: piv[r[0]] = r[1]
    elif d == 2:
        nv = m * m
        for g in range(m):
            for h in range(m):
                for k in range(m):
                    v = (1 << (h*m+k)) ^ (1 << (mul[g][h]*m+k)) ^ \
                        (1 << (g*m+mul[h][k])) ^ (1 << (g*m+h))
                    if v:
                        r = red(v)
                        if r: piv[r[0]] = r[1]
    else:
        nv = m ** 3
        for g in range(m):
            for h in range(m):
                gh = mul[g][h]
                for k in range(m):
                    hk = mul[h][k]
                    for l in range(m):
                        kl = mul[k][l]
                        v = (1 << ((h*m+k)*m+l)) ^ (1 << ((gh*m+k)*m+l)) ^ \
                            (1 << ((g*m+hk)*m+l)) ^ (1 << ((g*m+h)*m+kl)) ^ \
                            (1 << ((g*m+h)*m+k))
                        if v:
                            r = red(v)
                            if r: piv[r[0]] = r[1]
    leads = sorted(piv.keys())
    rows = dict(piv)
    for l in leads:
        vv = rows[l]; ch = True
        while ch:
            ch = False
            for b in leads:
                if b >= l: break
                if (vv >> b) & 1: vv ^= rows[b]; ch = True
        rows[l] = vv
    free = [i for i in range(nv) if i not in rows]
    out = []
    for f in free:
        v = 1 << f
        for l in leads:
            rest = rows[l] ^ (1 << l)
            if bin(rest & v).count('1') & 1: v |= 1 << l
        out.append(v)
    return out

def coboundary_gens(mul, m, d):
    out = []
    if d == 2:
        for j in range(m):
            v = 0
            for g in range(m):
                for h in range(m):
                    val = (1 if h == j else 0) ^ (1 if mul[g][h] == j else 0) ^ \
                          (1 if g == j else 0)
                    if val: v ^= 1 << (g*m+h)
            out.append(v)
    elif d == 3:
        for a in range(m):
            for b in range(m):
                v = 0
                for g in range(m):
                    for h in range(m):
                        for k in range(m):
                            val = (1 if (h == a and k == b) else 0) ^ \
                                  (1 if (mul[g][h] == a and k == b) else 0) ^ \
                                  (1 if (g == a and mul[h][k] == b) else 0) ^ \
                                  (1 if (g == a and h == b) else 0)
                            if val: v ^= 1 << ((g*m+h)*m+k)
                out.append(v)
    return out

def pull(v, d, phi, mT, mS):
    """pullback of a d-cochain on target (size mT) along phi: S -> T"""
    out = 0
    if d == 1:
        for g in range(mS):
            if (v >> phi[g]) & 1: out |= 1 << g
    elif d == 2:
        for g in range(mS):
            for h in range(mS):
                if (v >> (phi[g]*mT+phi[h])) & 1: out ^= 1 << (g*mS+h)
    else:
        for g in range(mS):
            for h in range(mS):
                for k in range(mS):
                    if (v >> ((phi[g]*mT+phi[h])*mT+phi[k])) & 1:
                        out ^= 1 << ((g*mS+h)*mS+k)
    return out

class Span:
    def __init__(self): self.piv = {}
    def add(self, v):
        while v:
            l = v.bit_length() - 1
            if l in self.piv: v ^= self.piv[l]
            else:
                self.piv[l] = v; return True
        return False

def mv_table(S_sub, C_sub, U_sub, fSC, fCU, name):
    """S <- C -> U (element lists in G_all indices; fSC,fCU: index maps
    C-element -> S/U-element).  Print dims and ranks, return dims of H^d(elW)."""
    posS, mulS = sub_mul(S_sub); mS = len(S_sub)
    posC, mulC = sub_mul(C_sub); mC = len(C_sub)
    posU, mulU = sub_mul(U_sub); mU = len(U_sub)
    phiS = [posS[fSC(c)] for c in C_sub]
    phiU = [posU[fCU(c)] for c in C_sub]
    print(name)
    prev_rank = None; prev_hC = None
    for d in (1, 2, 3):
        ZS = cocycle_basis(mulS, mS, d); BS = coboundary_gens(mulS, mS, d)
        ZC = cocycle_basis(mulC, mC, d); BC = coboundary_gens(mulC, mC, d)
        ZU = cocycle_basis(mulU, mU, d); BU = coboundary_gens(mulU, mU, d)
        def hdim(Z, B):
            sp = Span()
            for v in B: sp.add(v)
            return sum(1 for v in Z if sp.add(v))
        hS, hC, hU = hdim(ZS, BS), hdim(ZC, BC), hdim(ZU, BU)
        sp = Span()
        for v in BC: sp.add(v)
        rank = 0
        for v in ZS:
            if sp.add(pull(v, d, phiS, mS, mC)): rank += 1
        for v in ZU:
            if sp.add(pull(v, d, phiU, mU, mC)): rank += 1
        ker = hS + hU - rank
        cok = (prev_hC - prev_rank) if prev_hC is not None else 0
        print(f"  d={d}: dims(S,C,U)=({hS},{hC},{hU}) rank={rank} "
              f"dim H^{d}(elW) = {ker}+{cok} = {ker+cok}")
        prev_rank, prev_hC = rank, hC


def chiS(h):
    p = h[0]; s = 0
    for i in range(3):
        for j in range(i+1, 3):
            if p[i] > p[j]: s ^= 1
    return s
def chiN(h): return h[1][0] ^ h[1][1] ^ h[1][2]


def closure_idx(gens_i):
    S = {IDi} | set(gens_i)
    dq = collections.deque(S)
    while dq:
        x = dq.popleft()
        for g in list(S):
            for y in (MUL[x][g], MUL[g][x]):
                if y not in S: S.add(y); dq.append(y)
    return sorted(S)


# ---------- W_H8 and W_H24 -------------------------------------------

sw  = gi[((1, 0, 2), (0, 0, 0))]
nb  = gi[((0, 1, 2), (1, 1, 0))]
n011 = gi[((0, 1, 2), (0, 1, 1))]
rot = gi[((1, 2, 0), (0, 0, 0))]
nx = gi[((0, 1, 2), (1, 0, 0))]
ny = gi[((0, 1, 2), (0, 1, 0))]
nz = gi[((0, 1, 2), (0, 0, 1))]
v_tot = gi[((0, 1, 2), (1, 1, 1))]

H8 = closure_idx([sw, n011])
K  = closure_idx([sw, nb])
mv_table([IDi, nb], K, H8,
         lambda c: IDi if c in (IDi, sw) else nb,
         lambda c: c,
         "el(W_H8) ~ hocolim( B(K/<sw>) <- BK -> BD4 ):")

H24 = closure_idx([nx, ny, nz, rot])
Z6 = closure_idx([rot, v_tot])
mv_table([IDi, v_tot], Z6, H24,
         lambda c: IDi if chiN(G_all[c]) == 0 else v_tot,
         lambda c: c,
         "el(W_H24) ~ hocolim( BZ/2 <- BZ/6 -> BH24 ):")


# ---------- el(cube^3/B3): degrees 1,2 and the degree-3 step ----------

# subgroups: G_P = <tau, n1, n2>, G_l = S3 x <z>, G_e = <tau, z>
tau = ((1, 0, 2), (0, 0, 0)); n1e = ((0, 1, 2), (1, 1, 0))
n2e = ((0, 1, 2), (0, 0, 1)); ze = ((0, 1, 2), (1, 1, 1))
GP = closure_idx([gi[tau], gi[n1e], gi[n2e]])
Gl = closure_idx([gi[(p, (0, 0, 0))] for p in itertools.permutations(range(3))]
                 + [gi[ze]])
Ge = closure_idx([gi[tau], gi[ze]])
posP, mulP = sub_mul(GP); mP = len(GP)
posL, mulL = sub_mul(Gl); mL = len(Gl)

def gp_coords(h):
    for a in (0, 1):
        for b in (0, 1):
            for c in (0, 1):
                e = ID
                if a: e = mm(e, tau)
                if b: e = mm(e, n1e)
                if c: e = mm(e, n2e)
                if e == h: return (a, b, c)
    raise RuntimeError

def cup11(c1, c2, m):
    v = 0
    for g in range(m):
        if not c1[g]: continue
        for h in range(m):
            if c2[h]: v ^= 1 << (g*m+h)
    return v
def cup111(a, b, c, m):
    v = 0
    for g in range(m):
        if not a[g]: continue
        for h in range(m):
            if not b[h]: continue
            for k in range(m):
                if c[k]: v ^= 1 << ((g*m+h)*m+k)
    return v
def cup12(al, f2get, m):
    v = 0
    for g in range(m):
        if not al[g]: continue
        for h in range(m):
            for k in range(m):
                if f2get(h, k): v ^= 1 << ((g*m+h)*m+k)
    return v

print("el(cube^3/B3), two-level collage:")

# H^2(B3) representatives via full-group cocycles
mulB = MUL
ZB2 = cocycle_basis(mulB, N, 2)
BB2 = coboundary_gens(mulB, N, 2)
sp = Span()
for v in BB2: sp.add(v)
repsB2 = [v for v in ZB2 if sp.add(v)]
assert len(repsB2) == 4, len(repsB2)

cl_z = [chiN(G_all[x]) for x in Gl]
cl_s = [chiS(G_all[x]) for x in Gl]
cp = [gp_coords(G_all[x]) for x in GP]
cp_t = [c[0] for c in cp]; cp_1 = [c[1] for c in cp]; cp_2 = [c[2] for c in cp]

def restr2get(v, sub):
    return lambda a, b: (v >> (sub[a]*N + sub[b])) & 1

# degree 2: rank of Phi_2 in H^2(Gl) + H^2(GP) modulo coboundaries
nv2L = mL*mL
def comb2(vL, vP): return vL | (vP << nv2L)
sp2 = Span()
for v in coboundary_gens(mulL, mL, 2): sp2.add(comb2(v, 0))
for v in coboundary_gens(mulP, mP, 2): sp2.add(comb2(0, v))
zz = cup11(cl_z, cl_z, mL)
def r2(v, sub, m):
    out = 0
    for a in range(m):
        for b in range(m):
            if (v >> (sub[a]*N + sub[b])) & 1: out ^= 1 << (a*m+b)
    return out
rank2 = 0
for combo in ((cp_1, cp_1), (cp_1, cp_2), (cp_2, cp_2)):
    if sp2.add(comb2(zz, cup11(combo[0], combo[1], mP))): rank2 += 1
for w in repsB2:
    if sp2.add(comb2(r2(w, Gl, mL), r2(w, GP, mP))): rank2 += 1
print(f"  d=2: dims(S,U)=(3,4), target H^2(C)=6, rank Phi_2 = {rank2}, "
      f"dim H^2 = {3+4-rank2}")

# degree 3: decomposables + strata cubes, then pull back Z^3(S4^rot)
nv3L = mL**3
def comb3(vL, vP): return vL | (vP << nv3L)
sp3 = Span()
for v in coboundary_gens(mulL, mL, 3): sp3.add(comb3(v, 0))
for v in coboundary_gens(mulP, mP, 3): sp3.add(comb3(0, v))
rank3 = 0
for i in range(4):
    combos = [cp_1]*(3-i) + [cp_2]*i
    v = comb3(cup111(cl_z, cl_z, cl_z, mL),
              cup111(combos[0], combos[1], combos[2], mP))
    if sp3.add(v): rank3 += 1
for w in repsB2:
    for cL, cP in ((cl_s, cp_t), (cl_z, cp_2)):
        v = comb3(cup12(cL, restr2get(w, Gl), mL),
                  cup12(cP, restr2get(w, GP), mP))
        if sp3.add(v): rank3 += 1
print(f"  d=3: decomposable+strata span rank = {rank3}")

# Z^3(S4^rot): rotation subgroup, kernel by ascending back-substitution
ROT = [x for x in range(N) if chiS(G_all[x]) == chiN(G_all[x])]
posR = {x: i for i, x in enumerate(ROT)}
mR = 24
mulR = [[posR[MUL[a][b]] for b in ROT] for a in ROT]
piv = {}
def redR(v):
    while v:
        l = v.bit_length() - 1
        if l in piv: v ^= piv[l]
        else: return l, v
    return None
for g in range(mR):
    for h in range(mR):
        gh = mulR[g][h]
        for k in range(mR):
            hk = mulR[h][k]
            for l in range(mR):
                kl = mulR[k][l]
                v = (1 << ((h*mR+k)*mR+l)) ^ (1 << ((gh*mR+k)*mR+l)) ^ \
                    (1 << ((g*mR+hk)*mR+l)) ^ (1 << ((g*mR+h)*mR+kl)) ^ \
                    (1 << ((g*mR+h)*mR+k))
                if v:
                    r = redR(v)
                    if r: piv[r[0]] = r[1]
nv3R = mR**3
freeR = [i for i in range(nv3R) if i not in piv]
print(f"  Z^3(S4) dim = {len(freeR)} (= 551 + 3)")
lead_rows = [(l, piv[l] ^ (1 << l)) for l in sorted(piv.keys())]
def solveR(fb):
    v = fb
    for l, rest in lead_rows:
        if bin(rest & v).count('1') & 1: v |= 1 << l
    return v
def rotpart(x):
    return posR[x] if chiS(G_all[x]) == chiN(G_all[x]) else posR[MUL[v_tot][x]]
phiL3 = [rotpart(x) for x in Gl]
phiP3 = [rotpart(x) for x in GP]
def pull3(v, phi, m):
    out = 0
    for g in range(m):
        for h in range(m):
            for k in range(m):
                if (v >> ((phi[g]*mR+phi[h])*mR+phi[k])) & 1:
                    out ^= 1 << ((g*m+h)*m+k)
    return out
extra = 0
for f in freeR:
    z = solveR(1 << f)
    if sp3.add(comb3(pull3(z, phiL3, mL), pull3(z, phiP3, mP))): extra += 1
print(f"  extra rank from Z^3(S4) pullback = {extra}  "
      f"=> rank Phi_3 = {rank3+extra}, dim H^3 = {4+7-(rank3+extra)}")
print("  (expected: rank 9, dims H^1,H^2,H^3 = 1,1,2)")
