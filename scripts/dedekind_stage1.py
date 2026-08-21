"""Stage-one filler probe (O22).

For a quotient W of cube^2, build W~ = W with fillers freely
adjoined for all open 2-boxes (3-boxes omitted -- noted), and
test whether [iota o id] ~ [iota o const] through strict
homotopy chains in maps(W, W~).  Since W -> W~ is anodyne
(a type-trivial cofibration), a YES rigorously certifies that
W is type-contractible.  A NO is inconclusive (add 3-boxes /
iterate).

Cells of W~ at level k:
  ('w', cls)              -- a W-class
  ('n', b, c)             -- fresh cell: box id b, c in F(k)^2 not
                             factoring through the open box's
                             three closed faces
Restriction: ('n', b, c).u = ('n', b, c o u) unless c o u factors
through a face, in which case it attaches into W.
"""
import sys, itertools
sys.path.insert(0, 'scripts')
from dedekind_site import F, compose, cube_cells, all_maps, restrict, Quotient
from collections import deque

n = 2; K = 3

def const_f(k, v):
    return tuple(v for _ in F(k)[0])
def var_f(k, j):
    return tuple(p[j] for p in F(k)[0])

def face_factor(c, k):
    """c = (c1, c2) in F(k)^2: list of (face, remaining) it factors
    through: faces 'x0','x1','y0','y1'."""
    out = []
    if c[0] == const_f(k, 0): out.append(('x0', c[1]))
    if c[0] == const_f(k, 1): out.append(('x1', c[1]))
    if c[1] == const_f(k, 0): out.append(('y0', c[0]))
    if c[1] == const_f(k, 1): out.append(('y1', c[0]))
    return out

class Stage1:
    def __init__(s, W):
        s.W = W
        # enumerate open 2-boxes: missing face m in
        # {'x0','x1','y0','y1'}; the three present faces get
        # W(1)-classes with corner compatibility.
        # corners of an edge class e: e.delta0, e.delta1 in W(0)
        lv1 = W.level(1)
        def ends(e):
            # e is a level-1 cell (2-tuple over F(1)); endpoints:
            pts1 = F(1)[0]
            i0 = pts1.index((0,)); i1 = pts1.index((1,))
            v0 = tuple(comp[i0] for comp in e)
            v1 = tuple(comp[i1] for comp in e)
            c0 = tuple(const_f(0, x) for x in v0)
            c1 = tuple(const_f(0, x) for x in v1)
            return W.cls(0, c0), W.cls(0, c1)
        E = {e: ends(e) for e in lv1}
        s.boxes = []
        FACES = ['x0', 'x1', 'y0', 'y1']
        for m in FACES:
            present = [f for f in FACES if f != m]
            # assign classes to present faces; corner conditions:
            # corner (x=a, y=b) shared between face x_a (at param b)
            # and face y_b (at param a)
            for combo in itertools.product(lv1, repeat=3):
                asg = dict(zip(present, combo))
                ok = True
                for a in (0,1):
                    for b in (0,1):
                        fx = 'x%d' % a; fy = 'y%d' % b
                        if fx in asg and fy in asg:
                            if E[asg[fx]][b] != E[asg[fy]][a]:
                                ok = False; break
                    if not ok: break
                if ok:
                    s.boxes.append((m, tuple(sorted(asg.items()))))
        # dedupe boxes with identical data
        s.boxes = sorted(set(s.boxes))
    def attach(s, b, c, k):
        """c factors through a closed face of box b: W-cell."""
        m, asg = s.boxes[b]; asg = dict(asg)
        for (face, rem) in face_factor(c, k):
            if face == m: continue
            e = asg[face]
            # e composed with rem: restrict e along 1-tuple (rem)
            cell = restrict(e, (rem,), 2, 1, k)
            return ('w', s.W.cls(k, cell))
        return None
    def restrict_cell(s, cell, u, j, k):
        """restrict a W~ level-j cell along u: [k]->[j] site map
        (u = j... u is a j-tuple over F(k) for 2-variable cells;
        here all cube cells are 2-tuples so u is a 2-tuple over
        F(k) when j... we store c in F(j)^2 and restrict."""
        if cell[0] == 'w':
            # representative: any cell in the class; we must store
            # reps: W.classes maps cell->rep; pick rep = cls value
            rep = cell[1]  # class rep IS a cell tuple
            return ('w', s.W.cls(k, restrict(rep, u, 2, j, k)))
        _, b, c = cell
        cu = tuple(compose(ci, u, j, k) for ci in c)
        at = s.attach(b, cu, k)
        if at is not None: return at
        return ('n', b, cu)
    def level(s, k):
        out = [('w', c) for c in s.W.level(k)]
        for b in range(len(s.boxes)):
            for c in itertools.product(F(k)[1], repeat=2):
                if face_factor(c, k):
                    # factors through a closed face: either attaches
                    # (present face) or, if ONLY the missing face,
                    # it's a fresh boundary cell -- still fresh iff
                    # every factorization is through the missing face
                    m, asg = s.boxes[b]
                    if any(f != m for (f, _) in face_factor(c, k)):
                        continue
                out.append(('n', b, c))
        return out

def probe_stage1(name, idents):
    W = Quotient(2, idents, K)
    S = Stage1(W)
    nb = len(S.boxes)
    # nodes: maps W -> W~ = W~ level-2 cells with W-descent
    lvl2 = S.level(2)
    def descent_ok(cell, lev):
        for k in range(0, 3):
            groups = {}
            for u in all_maps(2, k):
                groups.setdefault(W.cls(k, u), []).append(u)
            for g in groups.values():
                if len(g) < 2: continue
                r0 = S.restrict_cell(cell, g[0], lev, k)
                if any(S.restrict_cell(cell, u, lev, k) != r0
                       for u in g[1:]):
                    return False
        return True
    nodes = [c for c in lvl2 if descent_ok(c, 2)]
    node_set = set(nodes)
    # id and const nodes
    idcell = ('w', W.cls(2, tuple(var_f(2, i) for i in range(2))))
    consts = set()
    for v in itertools.product((0,1), repeat=2):
        consts.add(('w', W.cls(2, tuple(const_f(2, v[i])
                                        for i in range(2)))))
    # edges: W~ level-3 cells H with homotopy descent + slices
    lvl3 = S.level(3)
    pts3 = F(3)[0]; pts2 = F(2)[0]
    adj = {c: set() for c in nodes}
    cnt = 0
    for H in lvl3:
        # homotopy descent: for k<=2, groups of u:[k]->[2] with
        # equal W-classes; lifted (u x id_t): [k+1]->[3]
        ok = True
        for k in range(0, 3):
            groups = {}
            for u in all_maps(2, k):
                groups.setdefault(W.cls(k, u), []).append(u)
            for g in groups.values():
                if len(g) < 2: continue
                exts = []
                for u in g:
                    ptsk1 = F(k+1)[0]; ptsk = F(k)[0]
                    idxk = {p: i for i, p in enumerate(ptsk)}
                    lift = tuple(tuple(comp[idxk[p[:-1]]]
                                       for p in ptsk1) for comp in u)
                    tvar = tuple(p[-1] for p in ptsk1)
                    exts.append(S.restrict_cell(H, lift + (tvar,),
                                                3, k+1))
                if any(e != exts[0] for e in exts[1:]):
                    ok = False; break
            if not ok: break
        if not ok: continue
        # slices: t = third variable
        idx3 = {p: i for i, p in enumerate(pts3)}
        sl = []
        for eps in (0, 1):
            u = (var_f(2,0), var_f(2,1))
            # restriction along (x, y, eps): 3-tuple over F(2)
            sub = (var_f(2,0), var_f(2,1), const_f(2, eps))
            sl.append(S.restrict_cell(H, sub, 3, 2))
        cnt += 1
        if sl[0] in node_set and sl[1] in node_set:
            adj[sl[0]].add(sl[1]); adj[sl[1]].add(sl[0])
    seen = {idcell}; dq = deque([idcell])
    while dq:
        x = dq.popleft()
        for y in adj.get(x, ()):
            if y not in seen: seen.add(y); dq.append(y)
    hit = bool(seen & consts)
    print(f"{name}: boxes={nb} nodes={len(nodes)} "
          f"H-cells={cnt} [id]~const (stage 1): {hit}", flush=True)
    return hit

# first two dunce candidates from sweep2:
c00, x1, c11 = const_f(1,0), var_f(1,0), const_f(1,1)
# candidate 1: (edge const-(0,0)) ~ (0, x)  AND  (x,1) ~ (1,x)
probe_stage1("dunce-1",
    [(1, (c00, c00), (c00, x1)), (1, (x1, c11), (c11, x1))])
# candidate 2: (0,0)-const ~ (x,0) AND (x,1) ~ (1,x)
probe_stage1("dunce-2",
    [(1, (c00, c00), (x1, c00)), (1, (x1, c11), (c11, x1))])
