"""el(cube^3/nested-24) via the master collage formula (O20).

Pieces (from isotropy_poset.py): 6 planes (one orbit, setwise
stabilizer S_P = K-block x 1, residual = reversal on one plane
coordinate), 4 lines (one orbit, setwise stabilizer S_L = S_3,
trivial residual), 12 incidences (one orbit, stabilizer
S_E = <sw_01> acting trivially on the line).  Hence:

  el(Sigma/N)  ~  pushout( B Z/2  <-  *  ->  * )  ~  B Z/2
  comma        =  pushout( B S_P  <-  B S_E  ->  B S_L )
                  (graph of groups on the incidence graph)
  el           =  pushout( el(Sigma/N)  <-  comma  ->  B N )

Non-domination: el(Sigma/N) ~ B Z/2 has one-dimensional F2-cohomology
in every degree, so dim H^k(el) >= 2 for some k <= 3 proves that el
is not a homotopy retract of el(Sigma/N).
"""
import sys, itertools as it, collections
sys.path.insert(0, 'scripts')
import el_betti as eb

n = 3
ELEMS = []
for p in it.permutations(range(n)):
    for s in it.product((0, 1), repeat=n):
        ELEMS.append((p, s))
ID = (tuple(range(n)), (0,) * n)
def mm(a, b):
    (p1, s1), (p2, s2) = a, b
    return (tuple(p2[p1[i]] for i in range(n)),
            tuple(s1[i] ^ s2[p1[i]] for i in range(n)))
def close(g):
    S = {ID} | set(g)
    dq = collections.deque(S)
    while dq:
        x = dq.popleft()
        for y in list(S):
            for z in (mm(x, y), mm(y, x)):
                if z not in S:
                    S.add(z); dq.append(z)
    return S

nb = ((0, 1, 2), (1, 1, 0)); n011 = ((0, 1, 2), (0, 1, 1))
rot = ((1, 2, 0), (0, 0, 0)); sw = ((1, 0, 2), (0, 0, 0))
N24 = sorted(close([nb, n011, rot, sw]))
assert len(N24) == 24

# subgroups: plane = locus of sw (cells (x,x,z)); line = (x,x,x)
n01 = ((0, 1, 2), (1, 1, 0))          # n0 n1
SP = sorted(close([sw, n01]))          # K-block x 1, order 4
SL = sorted(close([sw, rot]))          # S3, order 6
SE = sorted(close([sw]))               # order 2
assert len(SP) == 4 and len(SL) == 6 and len(SE) == 2
# sanity: SP stabilizes the plane setwise; SL the line; SE both
Z2 = [0, 1]; mul2 = {(a, b): a ^ b for a in range(2) for b in range(2)}

def group_data(G):
    gi = {h: i for i, h in enumerate(G)}
    mul = {(gi[a], gi[b]): gi[mm(a, b)] for a in G for b in G}
    return gi, mul, list(range(len(G)))

giN, mulN, GN = group_data(N24)
giP, mulP, GP = group_data(SP)
giL, mulL, GL = group_data(SL)
giE, mulE, GE = group_data(SE)

D = 4
print(f"building bar complexes (D={D})...", flush=True)
barN = eb.bar_complex(GN, mulN, D)
barP = eb.bar_complex(GP, mulP, D)
barL = eb.bar_complex(GL, mulL, D)
barE = eb.bar_complex(GE, mulE, D)
bar2 = eb.bar_complex(Z2, mul2, D)
print("H^*(B S_P):", barP[0].betti()[:D], flush=True)
print("H^*(B S_L):", barL[0].betti()[:D], flush=True)
print("H^*(B N24):", barN[0].betti()[:D], flush=True)

# ---- comma = pushout( B S_P <- B S_E -> B S_L ) ----
incPE = {giE[h]: giP[h] for h in SE}
incLE = {giE[h]: giL[h] for h in SE}
fPE = eb.induced_map(GE, mulE, GP, mulP, incPE, barE, barP, D)
fLE = eb.induced_map(GE, mulE, GL, mulL, incLE, barE, barL, D)
comma = eb.pushout_cx(barP[0], barL[0], barE[0], fPE, fLE)
print("H^*(comma = graph of groups):", comma.betti()[:D], flush=True)

# ---- sieve = B Z/2 ; cochain map C^*(sieve) -> C^*(comma) ----
# on B S_P: pull back along the residual character S_P -> Z/2
# (kill sw, send n0n1 -> 1); on B S_L: trivial map; homotopy comp = 0
resP = {giP[h]: (0 if h in (ID, sw) else 1) for h in SP}
chi = eb.induced_map(GP, mulP, Z2, mul2, resP, barP, bar2, D)
trivL = eb.induced_map(GL, mulL, Z2, mul2,
                       {giL[h]: 0 for h in SL}, barL, bar2, D)
fcols = []
for k in range(D + 1):
    oP1 = barP[0].dims[k]
    c = []
    for j in range(bar2[0].dims[k]):
        v = chi.cols[k][j]
        v |= (trivL.cols[k][j] << barP[0].dims[k])
        # comma^k = P^k + L^k + E^{k-1}: no E-component
        c.append(v)
    fcols.append(c)
fS = eb.Map(fcols)

# ---- map C^*(B N) -> C^*(comma): inclusions, 0 homotopy ----
incNP = {giP[h]: giN[h] for h in SP}
incNL = {giL[h]: giN[h] for h in SL}
rNP = eb.induced_map(GP, mulP, GN, mulN, incNP, barP, barN, D)
rNL = eb.induced_map(GL, mulL, GN, mulN, incNL, barL, barN, D)
gcols = []
for k in range(D + 1):
    c = []
    for j in range(barN[0].dims[k]):
        v = rNP.cols[k][j]
        v |= (rNL.cols[k][j] << barP[0].dims[k])
        c.append(v)
    gcols.append(c)
gN = eb.Map(gcols)

# ---- final pushout ----
print("assembling el(cube^3/nested-24)...", flush=True)
X = eb.pushout_cx(bar2[0], barN[0], comma, fS, gN)
print("H^*(el(cube^3/nested-24); F2) [deg 0..3 reliable]:",
      X.betti()[:D], flush=True)
print("el(Sigma/N) ~ BZ/2 dims: [1,1,1,1]; non-domination iff some "
      "dim >= 2 below degree", D, flush=True)
