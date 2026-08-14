"""Boundary-constrained monotone CSP for level-3 cells of W_K.

Decides existence of a K-invariant element H = [(A,B)] of W_K([3])
(A, B monotone on L_3 = {0,1}^6, variables u, v, w; K acts on u, v by
sw: u<->v and nb: negate both; w is the homotopy parameter) with
prescribed w-faces: classes e0 (w=0) and e1 (w=1) in W_K([2]).

Such an H is exactly a strict homotopy between the strict endomorphism
classes e0, e1 of W_K.  Method: branch over the face representatives
and the invariance twists (4*4*4*4 = 256 branches); each branch gives
a system of signed equalities (union-find with parity over the 128
value slots, using the De Morgan negation (¬A)(p) = 1 - A(rho p)) plus
fixed face values, plus monotonicity implications (2-SAT).
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from collage_type_lib import build, monotone_masks, NOT, gen

# ---------- L3 machinery ----------
N3 = 64
def rho3(p):
    c = [(p >> i) & 1 for i in range(6)]
    d = []
    for i in range(3):
        d += [1 - c[2*i+1], 1 - c[2*i]]
    return sum(b << i for i, b in enumerate(d))
def sw3(p):
    # substitution u<->v: swap literal pairs 0 and 1 (slots u,v; w fixed)
    c = [(p >> i) & 1 for i in range(6)]
    d = [c[2], c[3], c[0], c[1], c[4], c[5]]
    return sum(b << i for i, b in enumerate(d))
def nb3(p):
    # substitution u:=~u, v:=~v: swap within pairs 0 and 1
    c = [(p >> i) & 1 for i in range(6)]
    d = [c[1], c[0], c[3], c[2], c[4], c[5]]
    return sum(b << i for i, b in enumerate(d))
LEQ3 = [(p, q) for p in range(N3) for q in range(N3)
        if p != q and all(((p >> i) & 1) <= ((q >> i) & 1) for i in range(6))]

# level-2 data
N2, leq2, rho2 = build(2)
dm2 = monotone_masks(N2, leq2)
not2 = {m: NOT(m, N2, rho2) for m in dm2}
def orb2(c):
    A, B = c
    return [(A, B), (B, A), (not2[A], not2[B]), (not2[B], not2[A])]
def n2c(c): return min(orb2(c))

def face_point(p2, e):
    """embed an L2 point (u,v literals) into L3 with w-pair = (e, 1-e)"""
    return (p2 & 0b1111) | (e << 4) | ((1 - e) << 5)

# K-action options on a pair-valued cell: index 0..3
#   0: (A,B); 1: (B,A); 2: (~A,~B); 3: (~B,~A)
def act_slot(k, comp, p):
    """value of (k.(A,B))_comp at point p, as (component, point, signflip)"""
    if k == 0: return (comp, p, 0)
    if k == 1: return (1 - comp, p, 0)
    if k == 2: return (comp, rho3(p), 1)
    return (1 - comp, rho3(p), 1)

class ParityUF:
    def __init__(self, n):
        self.parent = list(range(n)); self.par = [0]*n
        self.fixed = {}   # root -> value (after parity)
        self.ok = True
    def find(self, i):
        r = i; acc = 0
        while self.parent[r] != r:
            acc ^= self.par[r]; r = self.parent[r]
        # path compress
        while self.parent[i] != r:
            nxt = self.parent[i]; np_ = self.par[i]
            self.parent[i] = r; self.par[i] = acc
            acc ^= np_; i = nxt
        return r, self.par[i] if i != r else 0
    def find2(self, i):
        r = i; acc = 0
        while self.parent[r] != r:
            acc ^= self.par[r]; r = self.parent[r]
        return r, acc
    def union(self, i, j, parity):
        (ri, pi) = self.find2(i); (rj, pj) = self.find2(j)
        if ri == rj:
            if (pi ^ pj) != parity: self.ok = False
            return
        self.parent[ri] = rj; self.par[ri] = pi ^ pj ^ parity
        if ri in self.fixed:
            v = self.fixed.pop(ri) ^ self.par[ri]
            if rj in self.fixed:
                if self.fixed[rj] != v: self.ok = False
            else:
                self.fixed[rj] = v
    def fix(self, i, val):
        (r, p) = self.find2(i)
        v = val ^ p
        if r in self.fixed:
            if self.fixed[r] != v: self.ok = False
        else:
            self.fixed[r] = v

def slot(comp, p): return comp * N3 + p

def homotopy_exists(e0, e1):
    """strict invariant homotopy between invariant classes e0, e1?"""
    reps0 = orb2(e0); reps1 = orb2(e1)
    for r0 in reps0:
        for r1 in reps1:
            for k1 in range(4):      # sw twist
                for k2 in range(4):  # nb twist
                    uf = ParityUF(2 * N3)
                    # invariance equations:
                    #  (A,B)(sw3 p) = (k1.(A,B))(p);  (A,B)(nb3 p) = (k2.(A,B))(p)
                    for comp in (0, 1):
                        for p in range(N3):
                            c2, p2, s2 = act_slot(k1, comp, p)
                            uf.union(slot(comp, sw3(p)), slot(c2, p2), s2)
                            c2, p2, s2 = act_slot(k2, comp, p)
                            uf.union(slot(comp, nb3(p)), slot(c2, p2), s2)
                            if not uf.ok: break
                        if not uf.ok: break
                    if not uf.ok: continue
                    # face fixing
                    for p2 in range(16):
                        for comp, m in ((0, r0[0]), (1, r0[1])):
                            uf.fix(slot(comp, face_point(p2, 0)), (m >> p2) & 1)
                        for comp, m in ((0, r1[0]), (1, r1[1])):
                            uf.fix(slot(comp, face_point(p2, 1)), (m >> p2) & 1)
                        if not uf.ok: break
                    if not uf.ok: continue
                    # monotonicity via 2-SAT on roots
                    # literals: (root, sign); implication for p<=q:
                    #   lit(p) -> lit(q)
                    # 2-SAT with fixed values folded in.
                    # build implication graph on 2*|roots| nodes lazily
                    import collections
                    adj = collections.defaultdict(list)
                    def lit(i):
                        r, p = uf.find2(i)
                        return (r, p)
                    contradiction = False
                    fixedv = dict(uf.fixed)
                    # propagate fixed through implications with a queue
                    imps = []
                    for comp in (0, 1):
                        for (p, q) in LEQ3:
                            (rp, sp) = lit(slot(comp, p))
                            (rq, sq) = lit(slot(comp, q))
                            if rp == rq:
                                if sp == sq: continue
                                # x^sp <= x^(1-sp): means x^sp=1 forces x^(1-sp)=1
                                # i.e. both orientations: x must satisfy
                                # (sp=0): x <= ~x -> x=0 ; record fix
                                fixv = 1 if sp else 0
                                # x^sp <= x^~sp: if sp=0: x<=~x => x=0
                                want = 0 if sp == 0 else 1
                                if rp in fixedv:
                                    if fixedv[rp] != want:
                                        contradiction = True; break
                                else:
                                    fixedv[rp] = want
                                continue
                            imps.append(((rp, sp), (rq, sq)))
                        if contradiction: break
                    if contradiction: continue
                    # now 2-SAT: variables = roots; clause: (x_rp ^ sp) -> (x_rq ^ sq)
                    # plus fixed values. Use simple propagation + free choice:
                    # monotone implications form a DAG-ish; just do constraint
                    # propagation to fixpoint, then greedy: unfixed roots: try
                    # to satisfy by 2-SAT SCC.
                    # Implication graph nodes: (root, val in {0,1}) meaning x_root = val
                    graph = collections.defaultdict(list)
                    for (rp, sp), (rq, sq) in imps:
                        # (x_rp = 1^sp... ) careful: literal value of slot =
                        # x_root ^ sign.  Implication: (x_rp^sp) -> (x_rq^sq)
                        # i.e. if x_rp = 1^sp... encode:
                        # x_rp == (1 xor sp)?? value of slot p = x_rp ^ sp.
                        # slotval_p <= slotval_q: slotval_p=1 -> slotval_q=1
                        # x_rp^sp=1 -> x_rq^sq=1: x_rp=1^sp -> x_rq=1^sq
                        graph[(rp, 1 ^ sp)].append((rq, 1 ^ sq))
                        # contrapositive: x_rq = sq -> x_rp = sp
                        graph[(rq, sq)].append((rp, sp))
                    # propagate fixed
                    from collections import deque
                    assign = dict(fixedv)
                    dq = deque(assign.items())
                    ok = True
                    while dq:
                        (r, v) = dq.popleft()
                        for (r2, v2) in graph[(r, v)]:
                            if r2 in assign:
                                if assign[r2] != v2: ok = False; break
                            else:
                                assign[r2] = v2; dq.append((r2, v2))
                        if not ok: break
                    if not ok: continue
                    # remaining free roots: 2-SAT satisfiable? implications among
                    # free roots only; do simple iterative assignment: pick a free
                    # root, try 0 then 1 with propagation (backtrack depth-first).
                    roots = set()
                    for i in range(2 * N3):
                        (r, _p) = uf.find2(i)
                        roots.add(r)
                    freeroots = [r for r in roots if r not in assign]
                    def try_assign(assign, freeroots):
                        if not freeroots: return True
                        r0_ = freeroots[0]
                        for v in (0, 1):
                            a2 = dict(assign)
                            a2[r0_] = v
                            dq = deque([(r0_, v)])
                            good = True
                            while dq:
                                (r, vv) = dq.popleft()
                                for (r2, v2) in graph[(r, vv)]:
                                    if r2 in a2:
                                        if a2[r2] != v2: good = False; break
                                    else:
                                        a2[r2] = v2; dq.append((r2, v2))
                                if not good: break
                            if good:
                                rest = [r for r in freeroots[1:] if r not in a2]
                                if try_assign(a2, rest): return True
                        return False
                    if try_assign(assign, freeroots):
                        return True
    return False


if __name__ == "__main__":
    # invariant level-2 classes
    def swsub2(m):
        r = 0
        for p in range(N2):
            vu, vnu, vv, vnv = p & 1, (p >> 1) & 1, (p >> 2) & 1, (p >> 3) & 1
            q = vv | (vnv << 1) | (vu << 2) | (vnu << 3)
            if (m >> q) & 1: r |= 1 << p
        return r
    def nbsub2(m):
        r = 0
        for p in range(N2):
            vu, vnu, vv, vnv = p & 1, (p >> 1) & 1, (p >> 2) & 1, (p >> 3) & 1
            q = vnu | (vu << 1) | (vnv << 2) | (vv << 3)
            if (m >> q) & 1: r |= 1 << p
        return r
    inv2 = []
    seen = set()
    for A in dm2:
        for B in dm2:
            k = n2c((A, B))
            if k in seen: continue
            seen.add(k)
            if n2c((swsub2(A), swsub2(B))) == k and \
               n2c((nbsub2(A), nbsub2(B))) == k:
                inv2.append(k)
    X2, Y2 = gen(0, 2, N2), gen(1, 2, N2)
    idc = n2c((X2, Y2))
    print(f"invariant classes: {len(inv2)}; computing homotopy graph...")
    import sys as _s
    # neighbors of id first, then closure
    comp = {idc}
    frontier = [idc]
    while frontier:
        e = frontier.pop()
        for e2 in inv2:
            if e2 in comp: continue
            if homotopy_exists(e, e2):
                comp.add(e2); frontier.append(e2)
                print(f"  id-component grew: {len(comp)}", flush=True)
    print(f"strict-homotopy component of id: {len(comp)} classes")
    constc = n2c((0, 0))
    const1 = n2c((0, (1 << N2) - 1))
    print("contains constant endo:", constc in comp or const1 in comp)
