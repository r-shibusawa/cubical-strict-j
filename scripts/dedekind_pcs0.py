"""Stage-zero base case of the prism-coherent-system program (O23).

A PCS-lite over W: data (eps, s, G; per-fold status; per-end
status; prisms) with
  - fold i EXACT: G.a_i = G.b_i and s.a_i = s.b_i (from the
    box-equality of a fresh fold), no prisms;
  - fold i PRISMATIC: per track t in {a_i, b_i}: if s.t == eps
    (const) the contributed cell is G.t (end-exit), else a
    prism D_t with eps-slice G.t contributes its s.t-section;
    the two contributed cells must be equal;
  - end eps' PLAIN: e-hat = G.n_eps' (end-exit old end, or
    fresh end's ground);
  - end eps' T-END (only when s_eps' != const eps): a prism
    C_eps' with eps-slice G.n_eps'; e-hat = its s_eps'-section;
  - all present prisms agree on the shared edge-prisms
    (three track-track edges E00, E11, E01; four end-track
    edges per end prism).

Claim (PCS_0): in every such system, e-hat_0 = iota iff
e-hat_1 = iota.  (The W-cluster of iota is the singleton
{iota}; the other six fold cells, including both constants,
form the second cluster -- so this is exactly gamma-hat
invariance at stage zero.)

This script sweeps all configurations exhaustively and reports
violations.
"""
import itertools, sys
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, cube_cells, Quotient

def proj(k, i):
    pts, _ = F(k)
    return tuple(p[i] for p in pts)
def const(k, e):
    pts, _ = F(k)
    return tuple(e for _ in pts)

A1c, B1c = (const(1,0), proj(1,0)), (proj(1,0), const(1,0))
A2c, B2c = (proj(1,0), proj(1,0)), (proj(1,0), const(1,1))
W = Quotient(2, [(1, A1c, B1c), (1, A2c, B2c)], 3)
iota = W.cls(2, (proj(2,0), proj(2,1)))
X, Y = proj(2,0), proj(2,1)
c0, c1 = const(2,0), const(2,1)

# squares as maps [2]->[3] (source coords (p,q))
SQ = {'a2': (X, X, Y), 'b2': (X, c1, Y),
      'a1': (c0, X, Y), 'b1': (X, c0, Y),
      'n0': (X, Y, c0), 'n1': (X, Y, c1)}

reps3 = []
seen = set()
for D in cube_cells(2, 3):
    c = W.cls(3, D)
    if c in seen: continue
    seen.add(c); reps3.append(D)
reps3_idx = {i: D for i, D in enumerate(reps3)}

RCACHE = {}
def rc(i, m):
    key = (i, m)
    if key not in RCACHE:
        D = reps3_idx[i]
        RCACHE[key] = W.cls(2, tuple(compose(c, m, 3, 2) for c in D))
    return RCACHE[key]

def gsq(i, name):     # G restricted to square `name`
    return rc(i, SQ[name])

# prism-internal restriction maps (prism coords (p,q,r)):
def slice_map(eps): return (X, Y, const(2, eps))
E_p0 = (c0, X, Y); E_p1 = (c1, X, Y)
E_q0 = (X, c0, Y); E_q1 = (X, c1, Y)
DIAG = (X, X, Y)   # (p,p,r) edge of an end prism

def sect_map(sigma): return (X, Y, sigma)

# track-track shared-edge constraints (maps into each prism):
TT_EDGES = [
    (('a2', E_p0), ('a1', E_p0)), (('a2', E_p0), ('b1', E_p0)),
    (('a1', E_p0), ('b1', E_p0)),
    (('a2', E_p1), ('b2', E_p1)),
    (('b2', E_p0), ('a1', E_p1)),
]
# end-prism vs track-prism edges: for end eps', track t:
# (map into C, map into D_t) with q-edge at eps' on the track:
def et_edges(epsp):
    Eq = E_q0 if epsp == 0 else E_q1
    return [('a2', DIAG, Eq), ('b2', E_q1, Eq),
            ('a1', E_p0, Eq), ('b1', E_q0, Eq)]

_, F3 = F(3)
u3, v3, w3 = proj(3,0), proj(3,1), proj(3,2)

def s_on(s, name):
    return compose(s, SQ[name], 3, 2)

viol = 0; nconf = 0; nsys = 0
TRACKS = {1: ('a1', 'b1'), 2: ('a2', 'b2')}

for eps in (0, 1):
    ce = const(3, eps)
    slice_m = slice_map(eps)
    # prism candidates by slice class
    by_slice = {}
    for i in range(len(reps3)):
        by_slice.setdefault(rc(i, slice_m), []).append(i)
    for s in F3:
        if s == ce: continue
        sON = {n: s_on(s, n) for n in SQ}
        for st1 in ('X', 'P'):
            if st1 == 'X' and sON['a1'] != sON['b1']: continue
            for st2 in ('X', 'P'):
                if st2 == 'X' and sON['a2'] != sON['b2']: continue
                for e0 in ('PL', 'TE'):
                    if e0 == 'TE' and sON['n0'] == const(2, eps): continue
                    for e1 in ('PL', 'TE'):
                        if e1 == 'TE' and sON['n1'] == const(2, eps): continue
                        if st1 == 'X' and st2 == 'X' and \
                           e0 == 'PL' and e1 == 'PL': continue
                        nconf += 1
                        # which track prisms are present?
                        present = []
                        for i_f, st in ((1, st1), (2, st2)):
                            if st == 'P':
                                for t in TRACKS[i_f]:
                                    if sON[t] != const(2, eps):
                                        present.append(t)
                        for orient in (0, 1):
                            en_i = ('n0', 'n1') if orient == 0 else ('n1', 'n0')
                            es_i = (e0, e1) if orient == 0 else (e1, e0)
                            # iterate G
                            for iG in range(len(reps3)):
                                if st1 == 'X' and gsq(iG,'a1') != gsq(iG,'b1'): continue
                                if st2 == 'X' and gsq(iG,'a2') != gsq(iG,'b2'): continue
                                if es_i[0] == 'PL' and gsq(iG, en_i[0]) != iota: continue
                                # assign track prisms with constraints
                                slots = {}
                                def cell_of(t):
                                    if sON[t] == const(2, eps): return gsq(iG, t)
                                    return rc(slots[t], sect_map(sON[t]))
                                def edges_ok():
                                    for (t1, m1), (t2, m2) in TT_EDGES:
                                        if t1 in slots and t2 in slots:
                                            if rc(slots[t1], m1) != rc(slots[t2], m2):
                                                return False
                                    return True
                                def folds_ok():
                                    for i_f, st in ((1, st1), (2, st2)):
                                        if st == 'P':
                                            ta, tb = TRACKS[i_f]
                                            if cell_of(ta) != cell_of(tb):
                                                return False
                                    return True
                                found_viol = False
                                def try_ends():
                                    # returns True if violating assignment
                                    # e-hat_0' (the iota end, orientation en_i[0])
                                    # already: PL requires G-slice iota (filtered);
                                    # TE requires a C with section iota.
                                    def c_candidates(nm, need_iota, avoid_iota):
                                        base = by_slice.get(gsq(iG, nm), [])
                                        out = []
                                        for iC in base:
                                            sec = rc(iC, sect_map(sON[nm]))
                                            if need_iota and sec != iota: continue
                                            if avoid_iota and sec == iota: continue
                                            ok = True
                                            for t, mC, mD in et_edges(0 if nm=='n0' else 1):
                                                if t in slots and rc(iC, mC) != rc(slots[t], mD):
                                                    ok = False; break
                                            if ok: out.append(iC)
                                        return out
                                    # end 0' (iota side)
                                    if es_i[0] == 'TE':
                                        C0s = c_candidates(en_i[0], True, False)
                                        if not C0s: return False
                                    # end 1' (must be != iota for violation)
                                    if es_i[1] == 'PL':
                                        return gsq(iG, en_i[1]) != iota
                                    else:
                                        C1s = c_candidates(en_i[1], False, True)
                                        return bool(C1s)
                                # nested prism assignment
                                def assign(k):
                                    global nsys
                                    if k == len(present):
                                        if not folds_ok(): return False
                                        nsys += 1
                                        return try_ends()
                                    t = present[k]
                                    for iD in by_slice.get(gsq(iG, t), []):
                                        slots[t] = iD
                                        if edges_ok():
                                            if assign(k + 1):
                                                del slots[t]; return True
                                        if t in slots: del slots[t]
                                    return False
                                if assign(0):
                                    viol += 1
                                    print("VIOLATION:", eps, s, st1, st2,
                                          e0, e1, "orient", orient)
print("configs:", nconf, "; systems reaching end-check:", nsys,
      "; violations:", viol)
print("=> (PCS_0)", "HOLDS" if viol == 0 else "FAILS")
