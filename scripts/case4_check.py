"""Case-4 machine check (O22): non-generic fresh H over 3-box
fillers with an iota-end.

An iota-end forces c's end face to be EXACTLY the id-slot
embedding (singleton class); enumerate all monotone extensions c
of that face (both end orientations, all choices of t-axis a and
id-slot position), and evaluate the two generator conditions:

  each side of a condition is a cube-level-2 cell; classify:
    interior (no constant component)  -> fresh
    face-factoring                    -> attaches to asg(face)o(rest)
  condition verdicts:
    interior vs interior : need exact equality of cube cells
    interior vs face     : IMPOSSIBLE (provenance mismatch)
    face vs face         : constraint on the assembly
                           (OPTIMISTICALLY satisfiable)
  Under the optimistic reading, count surviving c and report the
  slice at the other end (fresh interior / face slot).  Zero
  survivors with a non-iota other end = case 4 closed at m=3.
"""
import itertools

def monotone(k):
    pts = list(itertools.product((0,1), repeat=k))
    out = []
    for bits in itertools.product((0,1), repeat=len(pts)):
        f = dict(zip(pts, bits))
        if all(f[p] <= f[q] for p in pts for q in pts
               if all(a <= b for a, b in zip(p, q))):
            out.append(tuple(bits))
    return pts, out

P3, F3 = monotone(3)
P2, F2 = monotone(2)
IDX3 = {p: i for i, p in enumerate(P3)}
IDX2 = {p: i for i, p in enumerate(P2)}

def extensions(bottom, eps):
    """monotone phi on {0,1}^3 with phi(x,y,eps) = bottom(x,y)"""
    out = []
    for other in F2:
        lo, hi = (bottom, other) if eps == 0 else (other, bottom)
        if all(lo[i] <= hi[i] for i in range(4)):
            phi = [0]*8
            for p in P3:
                phi[IDX3[p]] = (lo if p[2] == 0 else hi)[IDX2[p[:2]]]
            out.append(tuple(phi))
    return out

def restrict2(c, sub):
    """c = 3-tuple over F(3) (cell of box-cube at level 3);
    sub = 3-tuple over F(2): the substitution; result: 3-tuple
    over F(2)."""
    out = []
    for comp in c:
        vals = []
        for p in P2:
            arg = tuple(sub[i][IDX2[p]] for i in range(3))
            vals.append(comp[IDX3[arg]])
        out.append(tuple(vals))
    return tuple(out)

def classify(cell2):
    """cell2 = 3-tuple over F(2): interior or which faces"""
    faces = []
    for i in range(3):
        for e in (0, 1):
            if all(v == e for v in cell2[i]):
                faces.append((i, e))
    return faces   # empty = interior

xf = tuple(p[0] for p in P2); yf = tuple(p[1] for p in P2)
c0f = tuple(0 for _ in P2); c1f = tuple(1 for _ in P2)
# generator substitutions in W-coordinates (u, v, t):
GEN = {
 'swapL': (c0f, xf, yf),   # (0, s, t)  [A1 x id]
 'swapR': (xf, c0f, yf),   # (s, 0, t)  [B1 x id]
 'diagL': (xf, xf, yf),    # (s, s, t)  [A2 x id]
 'diagR': (xf, c1f, yf),   # (s, 1, t)  [B2 x id]
}

total = survivors = 0
moves = []
for a_t in range(3):            # box axis serving as t
    others = [i for i in range(3) if i != a_t]
    for end in (0, 1):          # iota sits at (a_t, end)
        # slot embedding: c(.,.,end) with components:
        # axis others[0] = x, others[1] = y, axis a_t = end
        bottoms = {}
        bottoms[others[0]] = xf
        bottoms[others[1]] = yf
        bottoms[a_t] = c0f if end == 0 else c1f
        exts = {i: extensions(bottoms[i], end) for i in range(3)}
        for cx in exts[0]:
            for cy in exts[1]:
                for ct in exts[2]:
                    c = (cx, cy, ct)
                    total += 1
                    # W-substitutions -> box coords: W-vars (u,v,t):
                    # u,v at others, t at a_t; build box-sub from
                    # W-sub (su, sv, st): box component others[0]
                    # gets su etc.
                    ok = True; constrained = False
                    verdicts = {}
                    for (L, R) in (('swapL','swapR'),
                                   ('diagL','diagR')):
                        def box_sub(wsub):
                            su, sv, st = wsub
                            bs = [None]*3
                            bs[others[0]] = su; bs[others[1]] = sv
                            bs[a_t] = st
                            return tuple(bs)
                        rl = restrict2(c, box_sub(GEN[L]))
                        rr = restrict2(c, box_sub(GEN[R]))
                        fl, fr = classify(rl), classify(rr)
                        if not fl and not fr:
                            if rl != rr: ok = False; break
                        elif fl and fr:
                            constrained = True
                        else:
                            ok = False; break
                    if not ok: continue
                    # other end slice
                    oe = 1 - end
                    sl = restrict2(c, box_sub(
                        (xf, yf, c0f if oe == 0 else c1f)))
                    fs = classify(sl)
                    survivors += 1
                    moves.append((a_t, end, constrained,
                                  'interior' if not fs else
                                  ('faces', tuple(fs))))
print(f"candidates: {total}, survivors (optimistic): {survivors}")
from collections import Counter
print(Counter((m[2], m[3]) for m in moves))
