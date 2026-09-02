"""THE TENT CONTRACTION OF Q* (O25b -- final).

Q* = square/((0,u) ~ (u,u) ~ (u,1)) (left = diag = top), the
unique small quotient resisting strict homotopy and all
single-shell moves, is TYPE-CONTRACTIBLE: two shells with
literally equal fresh-end data compose through their common
fresh apex ("tent").

Shell 1 (eps = 0, tracks {left, diag, top}, end square n0):
  G1        = ((u&v)|(v&w), v)
  P1[left]  = (z&w,       z|(w&r))
  P1[diag]  = (z&w&r,     z|(w&r))
  P1[top]   = (z&w&r,     z|w)
  C1_0      = ((u&r)|(u&v), v)        -- old end at r=1: (u,v) = id
Shell 2 (same shape):
  G2        = (0,         v&w)
  P2[left]  = (z&w,       (z&w)|(w&r))
  P2[diag]  = (z&w&r,     (z&w)|(w&r))
  P2[top]   = (z&w&r,     w)
  C2_0      = (0, 0)                  -- old end: the constant v00
The two fresh ends at w = 1 have equal based data (the G-slices
(v,v) and (0,v) are identified by the left=diag fold; the three
track-prism slices agree on the nose), hence are the SAME cell
of the uniform replacement: id ~ apex ~ const.  For context, the
strict component of the identity in Q* is recomputed and does
not contain a constant: the tent is essential.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, cube_cells, all_maps, restrict, Quotient, compose

K = 3
def proj(k, i):
    pts, _ = F(k)
    return tuple(p[i] for p in pts)
def const(k, e):
    return tuple(e for _ in F(k)[0])
def meet(*xs):
    out = xs[0]
    for x in xs[1:]: out = tuple(a & b for a, b in zip(out, x))
    return out
def join(*xs):
    out = xs[0]
    for x in xs[1:]: out = tuple(a | b for a, b in zip(out, x))
    return out

u1 = proj(1,0); c01 = const(1,0); c11 = const(1,1)
A_l = (c01, u1); A_d = (u1, u1); A_t = (u1, c11)
idents = [(1, A_l, A_d), (1, A_l, A_t)]
W = Quotient(2, idents, K)
u2, w2 = proj(2,0), proj(2,1)
c02, c12 = const(2,0), const(2,1)
u3, v3, w3 = proj(3,0), proj(3,1), proj(3,2)
iota = W.cls(2, (u2, w2))
constc = W.cls(2, (c02, c02))

ok = True
def check(name, cond):
    global ok
    print(("  OK " if cond else "  FAIL "), name)
    if not cond: ok = False

# the data (coords: G in (u,v,w); P in (z,w,r); C in (u,v,r))
S1 = dict(
    G=(join(meet(u3,v3), meet(v3,w3)), v3),
    Pl=(meet(u3,v3), join(u3, meet(v3,w3))),
    Pd=(meet(u3,v3,w3), join(u3, meet(v3,w3))),
    Pt=(meet(u3,v3,w3), join(u3,v3)),
    C0=(join(meet(u3,w3), meet(u3,v3)), v3))
S2 = dict(
    G=(const(3,0), meet(v3,w3)),
    Pl=(meet(u3,v3), join(meet(u3,v3), meet(v3,w3))),
    Pd=(meet(u3,v3,w3), join(meet(u3,v3), meet(v3,w3))),
    Pt=(meet(u3,v3,w3), v3),
    C0=(const(3,0), const(3,0)))
# NOTE on coords: components written in the generic variables
# (x1,x2,x3) of [3]; the roles (u,v,w)/(z,w,r)/(u,v,r) are fixed
# by the restriction maps below.

TR = {'l': A_l, 'd': A_d, 't': A_t}
def lift1(T):
    return (compose(T[0], (u2,), 1, 2), compose(T[1], (u2,), 1, 2))
def r32(cell, mp):
    return W.cls(2, tuple(compose(c, mp, 3, 2) for c in cell))
r0m = (u2, w2, c02); r1m = (u2, w2, c12)      # third-coord slices
w0m = (u2, c02, w2); w1m = (u2, c12, w2)      # second-coord slices
def gtrack(T):
    T1, T2 = lift1(T); return (T1, T2, w2)

for tag, S in (("shell1", S1), ("shell2", S2)):
    # (a) base compatibilities at r=0
    for k, T in TR.items():
        check(f"{tag}: P[{k}].r0 = G o track[{k}]",
              r32(S['P'+k], r0m) == r32(S['G'], gtrack(T)))
    check(f"{tag}: C0.r0 = G.w0",
          r32(S['C0'], r0m) == r32(S['G'], (u2, w2, c02)))
    # (b) end-square edges: C0 o T-edge = P.w0
    for k, T in TR.items():
        check(f"{tag}: C0 edge[{k}] = P[{k}].w0",
              r32(S['C0'], gtrack(T)) == r32(S['P'+k], w0m))
    # (c) vertex gluings among P's (shared vertex cylinders)
    vs = []
    keys = list(TR)
    for a in range(len(keys)):
        for b in range(a+1, len(keys)):
            Ta, Tb = TR[keys[a]], TR[keys[b]]
            for ea in (0,1):
                for eb in (0,1):
                    if (Ta[0][ea], Ta[1][ea]) == (Tb[0][eb], Tb[1][eb]):
                        vs.append((keys[a], ea, keys[b], eb))
    for (ka, ea, kb, eb) in vs:
        ma = (c02 if ea == 0 else c12, u2, w2)
        mb = (c02 if eb == 0 else c12, u2, w2)
        check(f"{tag}: vertex glue {ka}({ea})={kb}({eb})",
              r32(S['P'+ka], ma) == r32(S['P'+kb], mb))
    # (d) fold conditions at the graph slice r=1
    check(f"{tag}: fold left=diag at r1",
          r32(S['Pl'], r1m) == r32(S['Pd'], r1m))
    check(f"{tag}: fold left=top at r1",
          r32(S['Pl'], r1m) == r32(S['Pt'], r1m))

# (e) old ends
check("shell1 old end = identity", r32(S1['C0'], r1m) == iota)
check("shell2 old end = constant", r32(S2['C0'], r1m) == constc)

# (f) fresh-end based data agree (the tent apex)
check("apex: G-slices at w=1 agree in Q*",
      r32(S1['G'], (u2, w2, c12)) == r32(S2['G'], (u2, w2, c12)))
for k in TR:
    check(f"apex: P[{k}].w1 slices agree",
          r32(S1['P'+k], w1m) == r32(S2['P'+k], w1m))

# (g) context: strict isolation of the identity in Q*
from collections import deque
a1m3 = tuple(gtrack(T) for T in (A_l, A_d, A_t))
n0m3 = (u2, w2, c02); n1m3 = (u2, w2, c12)
def is_fold2(h):
    return (W.cls(1, tuple(compose(c, A_l, 2, 1) for c in h)) ==
            W.cls(1, tuple(compose(c, A_d, 2, 1) for c in h)) ==
            W.cls(1, tuple(compose(c, A_t, 2, 1) for c in h)))
# strict endos via full descent (as in the census) -- use the
# simpler generator condition here for the context check
from dedekind_shellreach import census, reach
endo_cls, adj, shell_adj, idc, consts = census(W, idents)
check("strict component of id contains no constant",
      not reach([adj], idc, consts))
check("basic shell moves do not contract Q*",
      not reach([adj, shell_adj], idc, consts))

print()
print("=> TENT CONTRACTION VERIFIED: Q* is type-contractible."
      if ok else "=> CERTIFICATE FAILED")
