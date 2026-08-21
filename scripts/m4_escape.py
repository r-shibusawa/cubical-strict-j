"""The m=4 escape experiment (O22).  Can a 4-box, using an
earlier 3-cell with an iota-slice as a face, host a fresh
cylinder H that moves iota?

Enumeration:
 1. iota-carriers: pairs (A, rho), A in W(3)-classes,
    rho in F(2)^3, with A o rho = (x,y) exactly.
 2. For each carrier and each placement (f0-axis position among
    the 4 box axes, epsilon-end, t-axis identification), the end
    condition pins c(.,.,eps) componentwise; enumerate monotone
    extensions.
 3. Conditions (S),(D): per generator, classify both sides:
    factoring through the f0-face -> attach via A (DECIDABLE);
    factoring through another face -> optimistic constraint;
    interior -> fresh (exact equality needed if both interior,
    mismatch fails).
 4. Report survivors and their other-end targets.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from cand05_independent import FF, pre, congruence

P2, F2 = FF(2); P3, F3 = FF(3)
IDX2 = {p: i for i, p in enumerate(P2)}
IDX3 = {p: i for i, p in enumerate(P3)}
xf = tuple(p[0] for p in P2); yf = tuple(p[1] for p in P2)
c0f = tuple(0 for _ in P2); c1f = tuple(1 for _ in P2)

CL = congruence(3)
reps3 = sorted(set(CL[3].values()))
gen2 = (tuple(p[0] for p in P2), tuple(p[1] for p in P2))

# 1. carriers
carriers = []
for A in reps3:
    for rho in itertools.product(F2, repeat=3):
        img = tuple(
            tuple(comp[IDX3[tuple(r[IDX2[p]] for r in rho)]]
                  for p in P2) for comp in A)
        if img == gen2:
            carriers.append((A, rho))
print(f"iota-carriers: {len(carriers)} (A,rho) pairs over "
      f"{len(reps3)} classes; distinct A: "
      f"{len({a for a,_ in carriers})}", flush=True)

def monotone_ext(bottom, eps):
    out = []
    for other in F2:
        lo, hi = (bottom, other) if eps == 0 else (other, bottom)
        if all(lo[i] <= hi[i] for i in range(4)):
            phi = [0]*8
            for p in P3:
                phi[IDX3[p]] = (lo if p[2] == 0 else hi)[IDX2[p[:2]]]
            out.append(tuple(phi))
    return out

def restrict34(c4, sub):
    """c4 = 4-tuple over F(3); sub = 3-tuple over F(2) (the W-sub
    (u,v,t) -> box via c4 later)... here: restrict c4 along sub:
    result 4-tuple over F(2)."""
    out = []
    for comp in c4:
        vals = []
        for p in P2:
            arg = tuple(sub[i][IDX2[p]] for i in range(3))
            vals.append(comp[IDX3[arg]])
        out.append(tuple(vals))
    return tuple(out)

def classify4(cell):
    faces = []
    for i in range(4):
        for e in (0, 1):
            if all(v == e for v in cell[i]): faces.append((i, e))
    return faces

GEN = {
 'swapL': (c0f, xf, yf), 'swapR': (xf, c0f, yf),
 'diagL': (xf, xf, yf),  'diagR': (xf, c1f, yf),
}
from collections import Counter
res = Counter(); movers = []
tried = 0
for (A, rho) in carriers:
    # place f0 at box axis 3 WLOG?? no -- the t-direction matters;
    # W-coords (u,v,t) -> box: c's components; end at t=eps.
    # f0-axis: one of the 4 box axes; f0's own 3 axes carry rho.
    for f0axis in range(4):
        for f0eps in (0, 1):
            for eps in (0, 1):
                # bottom values: at box axis f0axis: const f0eps;
                # at the other three axes: rho components in order
                others4 = [i for i in range(4) if i != f0axis]
                bottoms = {}
                for t3, ax in enumerate(others4):
                    bottoms[ax] = rho[t3]
                bottoms[f0axis] = c0f if f0eps == 0 else c1f
                exts = {ax: monotone_ext(bottoms[ax], eps)
                        for ax in range(4)}
                total = 1
                for ax in range(4): total *= len(exts[ax])
                if total > 300000: continue
                for combo in itertools.product(
                        *[exts[ax] for ax in range(4)]):
                    c4 = tuple(combo)
                    tried += 1
                    # freshness: c4 must not factor through <=1 face
                    ff = classify4(c4)
                    if len(ff) >= 2: continue
                    if ff and ff[0] == (f0axis, f0eps): continue
                    ok = True; constrained = False
                    for (L, R) in (('swapL','swapR'),
                                   ('diagL','diagR')):
                        rl = restrict34(c4, GEN[L])
                        rr = restrict34(c4, GEN[R])
                        fl = [f for f in classify4(rl)
                              if not ff or f != ff[0]]
                        fr = [f for f in classify4(rr)
                              if not ff or f != ff[0]]
                        if not fl and not fr:
                            if rl != rr: ok = False; break
                        elif fl and fr:
                            # decidable if both route ONLY through f0
                            if (fl[0] == (f0axis, f0eps) ==
                                fr[0] and len(fl)==1==len(fr)):
                                # attach via A: compare A o (rem)
                                def att(cell):
                                    rem = [j for j in range(4)
                                           if j != f0axis]
                                    sub3 = tuple(cell[j]
                                                 for j in rem)
                                    return CL[2][tuple(
                                      tuple(comp[IDX3[tuple(
                                        s[IDX2[p]] for s in sub3)]]
                                        for p in P2) for comp in A)]
                                if att(rl) != att(rr):
                                    ok = False; break
                            else:
                                constrained = True
                        else:
                            ok = False; break
                    if not ok: continue
                    oe = 1 - eps
                    sl = restrict34(c4, (xf, yf,
                                         c0f if oe==0 else c1f))
                    fs = [f for f in classify4(sl)
                          if not ff or f != ff[0]]
                    tgt = 'interior' if not fs else 'face'
                    res[(constrained, tgt)] += 1
                    if not constrained:
                        movers.append((A, rho, f0axis, f0eps,
                                       eps, c4, tgt))
print(f"tried: {tried}")
print("survivors:", dict(res))
print("unconstrained movers:", len(movers))
for m in movers[:5]:
    print("  mover: f0axis", m[2], "f0eps", m[3], "end", m[4],
          "target", m[6])
