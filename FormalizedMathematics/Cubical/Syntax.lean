import FormalizedMathematics.Cubical.Interval

/-!
# Core syntax of the cubical kernel

Core terms use de Bruijn *indices*; term variables and interval variables
share one context (the checker tracks which entries are which).

`papp` (path application) carries its endpoint annotations: the boundary
rules `p @ 0 ≡ lhs`, `p @ 1 ≡ rhs` must fire even when `p` is neutral, and
an untyped evaluator cannot recover the endpoints from `p` alone.  The type
checker *verifies* the annotations against the inferred `PathP` type, so
they cannot lie.

A small `Raw` surface syntax with named variables resolves to core terms.
-/

namespace Cubical

/-- Core terms (de Bruijn indices). Binders: `pi`/`sigma`/`lam`/`natrec`'s
motive bind a term variable; `pathP`/`plam`/`transp` bind an interval
variable in their first argument. -/
inductive Term where
  | var (idx : Nat)
  /-- The universe at level `lvl`: `univ n : univ (n+1)` (with subsumption
  `univ m ≤ univ n` for `m ≤ n` at the checking judgement). -/
  | univ (lvl : Nat)
  | pi (dom cod : Term)
  | lam (body : Term)
  | app (fn arg : Term)
  | sigma (dom cod : Term)
  | pair (a b : Term)
  | fst (p : Term)
  | snd (p : Term)
  | nat
  | zero
  | succ (n : Term)
  | natrec (motive z s n : Term)
  /-- The integers, `pos n` and `negsuc n` (= −(n+1)) over ℕ.  The earlier
  strictly-cancelling representation was removed: strict `suc`/`pred`
  cancellation plus an eliminator breaks substitution-stability of
  definitional equality (see HANDOFF §5). -/
  | int
  | ipos (n : Term)
  | inegsuc (n : Term)
  /-- Case split: `intcase (z. P) fpos fneg t` with
  `fpos : Π (n : ℕ), P (ipos n)` and `fneg : Π (n : ℕ), P (inegsuc n)`.
  Recursion on ℤ is case split plus `natrec` inside. -/
  | intcase (motive fpos fneg t : Term)
  /-- The unit type (no η; `isProp ⊤` is proven with `unitrec`). -/
  | unit
  | tt
  | unitrec (motive ptt t : Term)
  /-- The empty type. -/
  | empty
  | emptyrec (ty t : Term)
  /-- Binary sums. -/
  | sum (l r : Term)
  | inl (t : Term)
  | inr (t : Term)
  | sumcase (motive fl fr t : Term)
  /-- Suspension (a parameterized HIT). -/
  | susp (a : Term)
  | north
  | south
  | merid (a r : Term)
  | susprec (motive nc sc mc t : Term)
  /-- Pushouts (`ppush` carries `f`/`g` as annotations: its endpoints
  `pinl (f c)` / `pinr (g c)` are not recoverable from the cell alone). -/
  | pushout (a b c f g : Term)
  | pinl (t : Term)
  | pinr (t : Term)
  | ppush (f g c r : Term)
  | pushrec (motive lc rc pc t : Term)
  /-- A reference to an already-verified global definition: evaluation
  unfolds the term, but the checker *trusts* the annotation (the
  definition-environment mechanism — each library definition is verified
  once by its own build-time guard, in dependency order, and its uses are
  not re-checked). -/
  | defn (name : String) (tm ty : Term)
  /-- Eilenberg–MacLane space `K(G,1)` (`emcomp` carries the
  multiplication as an annotation). -/
  | em1 (car mul : Term)
  | embase
  | emloop (g r : Term)
  | emcomp (mul g h r s : Term)
  | emsquash (x y p q u v i1 i2 i3 : Term)
  | em1rec (bT gB b l c t : Term)
  | em1elim (motive gP b l c t : Term)
  /-- Classifying space of an internal groupoid `BGpd Ob Hom cmp`
  (`bcomp` carries the composition as an annotation, mirroring `emcomp`). -/
  | bgpd (ob hom cmp : Term)
  | bpt (t : Term)
  | barr (x y f r : Term)
  | bcomp (cmp x y z f g r s : Term)
  | bsquash (x y p q u v i1 i2 i3 : Term)
  | bgrec (bT gB pf pl pc t : Term)
  | bgelim (motive gP pb pl pc t : Term)
  /-- Lists (a parameterized recursive type). -/
  | list (a : Term)
  | lnil
  | lcons (h t : Term)
  | listrec (motive nc cc t : Term)
  /-- Set quotients. -/
  | quot (a r : Term)
  | qin (t : Term)
  | qeq (a b w r : Term)
  | qsquash (x y p q r s : Term)
  | qelim (motive mset f feq t : Term)
  /-- Propositional truncation (a HIT with a recursive path constructor). -/
  | trunc (a : Term)
  | tin (t : Term)
  | squash (x y r : Term)
  | truncrec (mB prp f t : Term)
  /-- The torus (a HIT with a 2-cell). -/
  | torus
  | tbase
  | tloopP (r : Term)
  | tloopQ (r : Term)
  | tsurf (r s : Term)
  | torusrec (motive bc pc qc sc t : Term)
  /-- The circle: a higher inductive type with a point and a loop. -/
  | s1
  | sbase
  /-- The loop constructor applied to an interval point; `sloop 0 ≡ sbase ≡ sloop 1`. -/
  | sloop (r : Term)
  /-- Eliminator: `s1elim (x. P) b l t` with `b : P base` and
  `l : PathP (λ i, P (sloop i)) b b`. -/
  | s1elim (motive b l t : Term)
  | i0
  | i1
  | imax (l r : Term)
  | imin (l r : Term)
  | ineg (r : Term)
  | pathP (fam lhs rhs : Term)
  | plam (body : Term)
  | papp (p lhs rhs r : Term)
  | transp (fam a : Term)
  /-- Homogeneous composition `hcomp {A} [φ₁ ↦ u₁, ...] u₀`.  Each branch is
  a face (a conjunction of `(x = ε)` constraints on *ambient* interval
  variables) together with a tube term binding the composition direction. -/
  | hcomp (ty : Term) (sys : List (List (Term × Bool) × Term)) (u₀ : Term)
  /-- `Glue [φₖ ↦ (Tₖ, eₖ)] A`: on the face `φₖ` the type is `Tₖ`, glued onto
  the base `A` along the equivalence `eₖ : Equiv Tₖ A`.  No binders. -/
  | glueTy (sys : List (List (Term × Bool) × Term × Term)) (base : Term)
  /-- Introduction `glue [φₖ ↦ tₖ] a`, annotated with its `Glue` type. -/
  | glueTm (gty : Term) (sys : List (List (Term × Bool) × Term)) (base : Term)
  /-- Elimination `unglue b : A`, annotated with the `Glue` type of `b`. -/
  | unglue (gty : Term) (b : Term)
  | ann (tm ty : Term)
  deriving Repr, BEq, Inhabited

/-- Does de Bruijn index `idx` occur free in `t`?  Used for the `transp`
constancy check. -/
partial def Term.dependsOn : Term → Nat → Bool
  | .var i, idx => i == idx
  | .univ _, _ | .nat, _ | .zero, _ | .i0, _ | .i1, _ => false
  | .int, _ | .unit, _ | .tt, _ | .empty, _ | .s1, _ | .sbase, _ => false
  | .ipos t, idx | .inegsuc t, idx | .sloop t, idx => t.dependsOn idx
  | .intcase m fp fn t, idx =>
    m.dependsOn (idx + 1) || fp.dependsOn idx || fn.dependsOn idx
      || t.dependsOn idx
  | .unitrec m pt t, idx =>
    m.dependsOn (idx + 1) || pt.dependsOn idx || t.dependsOn idx
  | .emptyrec ty t, idx => ty.dependsOn idx || t.dependsOn idx
  | .sum l r, idx => l.dependsOn idx || r.dependsOn idx
  | .inl t, idx | .inr t, idx => t.dependsOn idx
  | .sumcase m fl fr t, idx =>
    m.dependsOn (idx + 1) || fl.dependsOn idx || fr.dependsOn idx
      || t.dependsOn idx
  | .susp a, idx => a.dependsOn idx
  | .north, _ | .south, _ => false
  | .merid a r, idx => a.dependsOn idx || r.dependsOn idx
  | .susprec m nc sc mc t, idx =>
    m.dependsOn (idx + 1) || nc.dependsOn idx || sc.dependsOn idx
      || mc.dependsOn idx || t.dependsOn idx
  | .pushout a b c f g, idx =>
    a.dependsOn idx || b.dependsOn idx || c.dependsOn idx
      || f.dependsOn idx || g.dependsOn idx
  | .pinl t, idx | .pinr t, idx => t.dependsOn idx
  | .ppush f g c r, idx =>
    f.dependsOn idx || g.dependsOn idx || c.dependsOn idx || r.dependsOn idx
  | .pushrec m lc rc pc t, idx =>
    m.dependsOn (idx + 1) || lc.dependsOn idx || rc.dependsOn idx
      || pc.dependsOn idx || t.dependsOn idx
  | .defn _ tm ty, idx => tm.dependsOn idx || ty.dependsOn idx
  | .em1 car mul, idx => car.dependsOn idx || mul.dependsOn idx
  | .embase, _ => false
  | .emloop g r, idx => g.dependsOn idx || r.dependsOn idx
  | .emcomp mul g h r s, idx =>
    mul.dependsOn idx || g.dependsOn idx || h.dependsOn idx
      || r.dependsOn idx || s.dependsOn idx
  | .emsquash x y p q u v j1 j2 j3, idx =>
    x.dependsOn idx || y.dependsOn idx || p.dependsOn idx
      || q.dependsOn idx || u.dependsOn idx || v.dependsOn idx
      || j1.dependsOn idx || j2.dependsOn idx || j3.dependsOn idx
  | .em1rec bT gB b l c t, idx =>
    bT.dependsOn idx || gB.dependsOn idx || b.dependsOn idx
      || l.dependsOn idx || c.dependsOn idx || t.dependsOn idx
  | .bgpd ob hom cmp, idx =>
    ob.dependsOn idx || hom.dependsOn idx || cmp.dependsOn idx
  | .bpt t, idx => t.dependsOn idx
  | .barr x y f r, idx =>
    x.dependsOn idx || y.dependsOn idx || f.dependsOn idx || r.dependsOn idx
  | .bcomp cm x y z f g r s2, idx =>
    cm.dependsOn idx || x.dependsOn idx || y.dependsOn idx
      || z.dependsOn idx || f.dependsOn idx || g.dependsOn idx
      || r.dependsOn idx || s2.dependsOn idx
  | .bsquash x y p q u v j1 j2 j3, idx =>
    x.dependsOn idx || y.dependsOn idx || p.dependsOn idx
      || q.dependsOn idx || u.dependsOn idx || v.dependsOn idx
      || j1.dependsOn idx || j2.dependsOn idx || j3.dependsOn idx
  | .bgrec bT gB pf pl pc t, idx =>
    bT.dependsOn idx || gB.dependsOn idx || pf.dependsOn idx
      || pl.dependsOn idx || pc.dependsOn idx || t.dependsOn idx
  | .bgelim m gP pb pl pc t, idx =>
    m.dependsOn (idx + 1) || gP.dependsOn idx || pb.dependsOn idx
      || pl.dependsOn idx || pc.dependsOn idx || t.dependsOn idx
  | .em1elim m gP b l c t, idx =>
    m.dependsOn (idx + 1) || gP.dependsOn idx || b.dependsOn idx
      || l.dependsOn idx || c.dependsOn idx || t.dependsOn idx
  | .list a, idx => a.dependsOn idx
  | .lnil, _ => false
  | .lcons h t, idx => h.dependsOn idx || t.dependsOn idx
  | .listrec m nc cc t, idx =>
    m.dependsOn (idx + 1) || nc.dependsOn idx || cc.dependsOn idx
      || t.dependsOn idx
  | .quot a r, idx => a.dependsOn idx || r.dependsOn idx
  | .qin t, idx => t.dependsOn idx
  | .qeq a b w r, idx =>
    a.dependsOn idx || b.dependsOn idx || w.dependsOn idx || r.dependsOn idx
  | .qsquash x y p q r s2, idx =>
    x.dependsOn idx || y.dependsOn idx || p.dependsOn idx
      || q.dependsOn idx || r.dependsOn idx || s2.dependsOn idx
  | .qelim m mset f feq t, idx =>
    m.dependsOn (idx + 1) || mset.dependsOn idx || f.dependsOn idx
      || feq.dependsOn idx || t.dependsOn idx
  | .trunc a, idx => a.dependsOn idx
  | .tin t, idx => t.dependsOn idx
  | .squash x y r, idx =>
    x.dependsOn idx || y.dependsOn idx || r.dependsOn idx
  | .truncrec mB prp f t, idx =>
    mB.dependsOn idx || prp.dependsOn idx || f.dependsOn idx
      || t.dependsOn idx
  | .torus, _ | .tbase, _ => false
  | .tloopP r, idx | .tloopQ r, idx => r.dependsOn idx
  | .tsurf r s, idx => r.dependsOn idx || s.dependsOn idx
  | .torusrec m bc pc qc sc t, idx =>
    m.dependsOn (idx + 1) || bc.dependsOn idx || pc.dependsOn idx
      || qc.dependsOn idx || sc.dependsOn idx || t.dependsOn idx
  | .s1elim m b l t, idx =>
    m.dependsOn (idx + 1) || b.dependsOn idx || l.dependsOn idx || t.dependsOn idx
  | .pi d c, idx => d.dependsOn idx || c.dependsOn (idx + 1)
  | .lam b, idx => b.dependsOn (idx + 1)
  | .app f a, idx => f.dependsOn idx || a.dependsOn idx
  | .sigma d c, idx => d.dependsOn idx || c.dependsOn (idx + 1)
  | .pair a b, idx => a.dependsOn idx || b.dependsOn idx
  | .fst p, idx | .snd p, idx => p.dependsOn idx
  | .succ n, idx => n.dependsOn idx
  | .natrec m z s n, idx =>
    m.dependsOn (idx + 1) || z.dependsOn idx || s.dependsOn idx || n.dependsOn idx
  | .imax l r, idx | .imin l r, idx => l.dependsOn idx || r.dependsOn idx
  | .ineg r, idx => r.dependsOn idx
  | .pathP f l r, idx => f.dependsOn (idx + 1) || l.dependsOn idx || r.dependsOn idx
  | .plam b, idx => b.dependsOn (idx + 1)
  | .papp p l r s, idx =>
    p.dependsOn idx || l.dependsOn idx || r.dependsOn idx || s.dependsOn idx
  | .transp f a, idx => f.dependsOn (idx + 1) || a.dependsOn idx
  | .hcomp ty sys u₀, idx =>
    ty.dependsOn idx || u₀.dependsOn idx ||
      sys.any fun (cof, body) =>
        cof.any (fun (f, _) => f.dependsOn idx) || body.dependsOn (idx + 1)
  | .glueTy sys base, idx =>
    base.dependsOn idx ||
      sys.any fun (cof, T, e) =>
        cof.any (fun (f, _) => f.dependsOn idx) || T.dependsOn idx || e.dependsOn idx
  | .glueTm gty sys base, idx =>
    gty.dependsOn idx || base.dependsOn idx ||
      sys.any fun (cof, t) =>
        cof.any (fun (f, _) => f.dependsOn idx) || t.dependsOn idx
  | .unglue gty b, idx => gty.dependsOn idx || b.dependsOn idx
  | .ann t ty, idx => t.dependsOn idx || ty.dependsOn idx

/-- Shift free de Bruijn indices `≥ c` up by `d`. -/
partial def Term.shift (t : Term) (d : Nat) (c : Nat := 0) : Term :=
  match t with
  | .var i => if i < c then .var i else .var (i + d)
  | .univ _ | .nat | .zero | .i0 | .i1 | .int | .unit | .tt | .empty
  | .s1 | .sbase => t
  | .ipos n => .ipos (n.shift d c)
  | .inegsuc n => .inegsuc (n.shift d c)
  | .intcase m fp fn x =>
    .intcase (m.shift d (c + 1)) (fp.shift d c) (fn.shift d c) (x.shift d c)
  | .unitrec m pt x =>
    .unitrec (m.shift d (c + 1)) (pt.shift d c) (x.shift d c)
  | .emptyrec ty x => .emptyrec (ty.shift d c) (x.shift d c)
  | .sum l r => .sum (l.shift d c) (r.shift d c)
  | .inl x => .inl (x.shift d c)
  | .inr x => .inr (x.shift d c)
  | .sumcase m fl fr x =>
    .sumcase (m.shift d (c + 1)) (fl.shift d c) (fr.shift d c) (x.shift d c)
  | .susp a => .susp (a.shift d c)
  | .north => .north
  | .south => .south
  | .merid a r => .merid (a.shift d c) (r.shift d c)
  | .susprec m nc sc mc x =>
    .susprec (m.shift d (c + 1)) (nc.shift d c) (sc.shift d c)
      (mc.shift d c) (x.shift d c)
  | .pushout a b c2 f g =>
    .pushout (a.shift d c) (b.shift d c) (c2.shift d c)
      (f.shift d c) (g.shift d c)
  | .pinl t => .pinl (t.shift d c)
  | .pinr t => .pinr (t.shift d c)
  | .ppush f g c2 r =>
    .ppush (f.shift d c) (g.shift d c) (c2.shift d c) (r.shift d c)
  | .pushrec m lc rc pc t =>
    .pushrec (m.shift d (c + 1)) (lc.shift d c) (rc.shift d c)
      (pc.shift d c) (t.shift d c)
  | .defn n tm ty => .defn n (tm.shift d c) (ty.shift d c)
  | .em1 car mul => .em1 (car.shift d c) (mul.shift d c)
  | .embase => .embase
  | .emloop g r => .emloop (g.shift d c) (r.shift d c)
  | .emcomp mul g h r s2 =>
    .emcomp (mul.shift d c) (g.shift d c) (h.shift d c)
      (r.shift d c) (s2.shift d c)
  | .emsquash x y p q u v j1 j2 j3 =>
    .emsquash (x.shift d c) (y.shift d c) (p.shift d c) (q.shift d c)
      (u.shift d c) (v.shift d c) (j1.shift d c) (j2.shift d c)
      (j3.shift d c)
  | .em1rec bT gB b l c2 t =>
    .em1rec (bT.shift d c) (gB.shift d c) (b.shift d c) (l.shift d c)
      (c2.shift d c) (t.shift d c)
  | .bgpd ob hom cm =>
    .bgpd (ob.shift d c) (hom.shift d c) (cm.shift d c)
  | .bpt t => .bpt (t.shift d c)
  | .barr x y f r =>
    .barr (x.shift d c) (y.shift d c) (f.shift d c) (r.shift d c)
  | .bcomp cm x y z f g r s2 =>
    .bcomp (cm.shift d c) (x.shift d c) (y.shift d c) (z.shift d c)
      (f.shift d c) (g.shift d c) (r.shift d c) (s2.shift d c)
  | .bsquash x y p q u v j1 j2 j3 =>
    .bsquash (x.shift d c) (y.shift d c) (p.shift d c) (q.shift d c)
      (u.shift d c) (v.shift d c) (j1.shift d c) (j2.shift d c)
      (j3.shift d c)
  | .bgrec bT gB pf pl pc t =>
    .bgrec (bT.shift d c) (gB.shift d c) (pf.shift d c) (pl.shift d c)
      (pc.shift d c) (t.shift d c)
  | .bgelim m gP pb pl pc t =>
    .bgelim (m.shift d (c + 1)) (gP.shift d c) (pb.shift d c)
      (pl.shift d c) (pc.shift d c) (t.shift d c)
  | .em1elim m gP b l c2 t =>
    .em1elim (m.shift d (c + 1)) (gP.shift d c) (b.shift d c)
      (l.shift d c) (c2.shift d c) (t.shift d c)
  | .list a => .list (a.shift d c)
  | .lnil => .lnil
  | .lcons h t => .lcons (h.shift d c) (t.shift d c)
  | .listrec m nc cc t =>
    .listrec (m.shift d (c + 1)) (nc.shift d c) (cc.shift d c)
      (t.shift d c)
  | .quot a r => .quot (a.shift d c) (r.shift d c)
  | .qin t => .qin (t.shift d c)
  | .qeq a b w r =>
    .qeq (a.shift d c) (b.shift d c) (w.shift d c) (r.shift d c)
  | .qsquash x y p q r s2 =>
    .qsquash (x.shift d c) (y.shift d c) (p.shift d c) (q.shift d c)
      (r.shift d c) (s2.shift d c)
  | .qelim m mset f feq t =>
    .qelim (m.shift d (c + 1)) (mset.shift d c) (f.shift d c)
      (feq.shift d c) (t.shift d c)
  | .trunc a => .trunc (a.shift d c)
  | .tin t => .tin (t.shift d c)
  | .squash x y r => .squash (x.shift d c) (y.shift d c) (r.shift d c)
  | .truncrec mB prp f t =>
    .truncrec (mB.shift d c) (prp.shift d c) (f.shift d c) (t.shift d c)
  | .torus => .torus
  | .tbase => .tbase
  | .tloopP r => .tloopP (r.shift d c)
  | .tloopQ r => .tloopQ (r.shift d c)
  | .tsurf r s => .tsurf (r.shift d c) (s.shift d c)
  | .torusrec m bc pc qc sc x =>
    .torusrec (m.shift d (c + 1)) (bc.shift d c) (pc.shift d c)
      (qc.shift d c) (sc.shift d c) (x.shift d c)
  | .sloop r => .sloop (r.shift d c)
  | .s1elim m b l x =>
    .s1elim (m.shift d (c + 1)) (b.shift d c) (l.shift d c) (x.shift d c)
  | .pi dom cod => .pi (dom.shift d c) (cod.shift d (c + 1))
  | .lam b => .lam (b.shift d (c + 1))
  | .app f a => .app (f.shift d c) (a.shift d c)
  | .sigma dom cod => .sigma (dom.shift d c) (cod.shift d (c + 1))
  | .pair a b => .pair (a.shift d c) (b.shift d c)
  | .fst p => .fst (p.shift d c)
  | .snd p => .snd (p.shift d c)
  | .succ n => .succ (n.shift d c)
  | .natrec m z s n =>
    .natrec (m.shift d (c + 1)) (z.shift d c) (s.shift d c) (n.shift d c)
  | .imax l r => .imax (l.shift d c) (r.shift d c)
  | .imin l r => .imin (l.shift d c) (r.shift d c)
  | .ineg r => .ineg (r.shift d c)
  | .pathP f l r => .pathP (f.shift d (c + 1)) (l.shift d c) (r.shift d c)
  | .plam b => .plam (b.shift d (c + 1))
  | .papp p l r s => .papp (p.shift d c) (l.shift d c) (r.shift d c) (s.shift d c)
  | .transp f a => .transp (f.shift d (c + 1)) (a.shift d c)
  | .hcomp ty sys u₀ =>
    .hcomp (ty.shift d c)
      (sys.map fun (cof, b) =>
        (cof.map fun (f, ε) => (f.shift d c, ε), b.shift d (c + 1)))
      (u₀.shift d c)
  | .glueTy sys base =>
    .glueTy
      (sys.map fun (cof, T, e) =>
        (cof.map fun (f, ε) => (f.shift d c, ε), T.shift d c, e.shift d c))
      (base.shift d c)
  | .glueTm gty sys base =>
    .glueTm (gty.shift d c)
      (sys.map fun (cof, tm) =>
        (cof.map fun (f, ε) => (f.shift d c, ε), tm.shift d c))
      (base.shift d c)
  | .unglue gty b => .unglue (gty.shift d c) (b.shift d c)
  | .ann tm ty => .ann (tm.shift d c) (ty.shift d c)

/-! ## The type of equivalences, as an object-language term

`Equiv T A := Σ (f : T → A), Π (b : A), isContr (fiber f b)` with
`fiber f b := Σ (x : T), Path A b (f x)` and
`isContr C := Σ (c : C), Π (c' : C), Path C c c'`.
The kernel synthesizes this type when checking `Glue`; its Kan operations
for `Glue` lines extract the fiber-center components accordingly. -/

/-- `fiber f b`, with `T`, `A` already shifted to the current depth and
`f`, `b` given as de Bruijn indices at the current depth. -/
def fiberT (T A : Term) (f b : Nat) : Term :=
  .sigma T (.pathP (A.shift 2) (.var (b + 1)) (.app (.var (f + 1)) (.var 0)))

/-- The type `Equiv T A` (contractible-fibers formulation). -/
def equivT (T A : Term) : Term :=
  .sigma (.pi T (A.shift 1))                             -- f
    (.pi (A.shift 1)                                     -- b
      (.sigma (fiberT (T.shift 2) (A.shift 2) 1 0)       -- center
        (.pi (fiberT (T.shift 3) (A.shift 3) 2 1)        -- other
          (.pathP (fiberT (T.shift 5) (A.shift 5) 4 3)
            (.var 1) (.var 0)))))

/-! ## Surface syntax -/

/-- Named surface syntax; `resolve` turns it into core `Term`. -/
inductive Raw where
  | var (name : String)
  | univ
  | univN (n : Nat)
  | pi (x : String) (dom cod : Raw)
  | arr (dom cod : Raw)                 -- non-dependent `dom → cod`
  | lam (x : String) (body : Raw)
  | app (fn arg : Raw)
  | sigma (x : String) (dom cod : Raw)
  | pair (a b : Raw)
  | fst (p : Raw)
  | snd (p : Raw)
  | nat
  | zero
  | succ (n : Raw)
  | natrec (motiveVar : String) (motive z s n : Raw)
  | int
  | ipos (n : Raw)
  | inegsuc (n : Raw)
  | intcase (x : String) (motive fpos fneg t : Raw)
  | unit
  | tt
  | unitrec (x : String) (motive ptt t : Raw)
  | empty
  | emptyrec (ty t : Raw)
  | sum (l r : Raw)
  | inl (t : Raw)
  | inr (t : Raw)
  | sumcase (x : String) (motive fl fr t : Raw)
  | susp (a : Raw)
  | north
  | south
  | merid (a r : Raw)
  | susprec (x : String) (motive nc sc mc t : Raw)
  | pushout (a b c f g : Raw)
  | pinl (t : Raw)
  | pinr (t : Raw)
  | ppush (f g c r : Raw)
  | pushrec (x : String) (motive lc rc pc t : Raw)
  | defn (name : String) (tm ty : Raw)
  | em1 (car mul : Raw)
  | embase
  | emloop (g r : Raw)
  | emcomp (mul g h r s : Raw)
  | emsquash (x y p q u v i1 i2 i3 : Raw)
  | em1rec (bT gB b l c t : Raw)
  | em1elim (x : String) (motive gP b l c t : Raw)
  | bgpd (ob hom cmp : Raw)
  | bpt (t : Raw)
  | barr (x y f r : Raw)
  | bcomp (cmp x y z f g r s : Raw)
  | bsquash (x y p q u v i1 i2 i3 : Raw)
  | bgrec (bT gB pf pl pc t : Raw)
  | bgelim (x : String) (motive gP pb pl pc t : Raw)
  | list (a : Raw)
  | lnil
  | lcons (h t : Raw)
  | listrec (x : String) (motive nc cc t : Raw)
  | quot (a r : Raw)
  | qin (t : Raw)
  | qeq (a b w r : Raw)
  | qsquash (x y p q r s : Raw)
  | qelim (x : String) (motive mset f feq t : Raw)
  | trunc (a : Raw)
  | tin (t : Raw)
  | squash (x y r : Raw)
  | truncrec (mB prp f t : Raw)
  | torus
  | tbase
  | tloopP (r : Raw)
  | tloopQ (r : Raw)
  | tsurf (r s : Raw)
  | torusrec (x : String) (motive bc pc qc sc t : Raw)
  | s1
  | sbase
  | sloop (r : Raw)
  | s1elim (x : String) (motive b l t : Raw)
  | i0
  | i1
  | imax (l r : Raw)
  | imin (l r : Raw)
  | ineg (r : Raw)
  | pathP (i : String) (fam lhs rhs : Raw)
  | path (ty lhs rhs : Raw)             -- non-dependent path type
  | plam (i : String) (body : Raw)
  | papp (p lhs rhs r : Raw)
  | transp (i : String) (fam a : Raw)
  | hcomp (i : String) (ty : Raw) (sys : List (List (Raw × Bool) × Raw)) (u₀ : Raw)
  | glueTy (sys : List (List (Raw × Bool) × Raw × Raw)) (base : Raw)
  | glueTm (gty : Raw) (sys : List (List (Raw × Bool) × Raw)) (base : Raw)
  | unglue (gty : Raw) (b : Raw)
  | ann (tm ty : Raw)
  deriving Repr, Inhabited

namespace Raw

/-- Resolve names to de Bruijn indices.  Pushing a dummy name (`""`) weakens
under a binder that the surface syntax does not mention (`arr`, `path`). -/
partial def resolve (names : List String) : Raw → Except String Term
  | .var n =>
    match names.idxOf? n with
    | some i => .ok (.var i)
    | none => .error s!"unbound variable `{n}`"
  | .univ => .ok (.univ 0)
  | .univN n => .ok (.univ n)
  | .pi x d c => do .ok (.pi (← resolve names d) (← resolve (x :: names) c))
  | .arr d c => do .ok (.pi (← resolve names d) (← resolve ("" :: names) c))
  | .lam x b => do .ok (.lam (← resolve (x :: names) b))
  | .app f a => do .ok (.app (← resolve names f) (← resolve names a))
  | .sigma x d c => do .ok (.sigma (← resolve names d) (← resolve (x :: names) c))
  | .pair a b => do .ok (.pair (← resolve names a) (← resolve names b))
  | .fst p => do .ok (.fst (← resolve names p))
  | .snd p => do .ok (.snd (← resolve names p))
  | .nat => .ok .nat
  | .zero => .ok .zero
  | .succ n => do .ok (.succ (← resolve names n))
  | .natrec x m z s n => do
    .ok (.natrec (← resolve (x :: names) m) (← resolve names z)
      (← resolve names s) (← resolve names n))
  | .int => .ok .int
  | .ipos t => do .ok (.ipos (← resolve names t))
  | .inegsuc t => do .ok (.inegsuc (← resolve names t))
  | .intcase x m fp fn t => do
    .ok (.intcase (← resolve (x :: names) m) (← resolve names fp)
      (← resolve names fn) (← resolve names t))
  | .unit => .ok .unit
  | .tt => .ok .tt
  | .unitrec x m pt t => do
    .ok (.unitrec (← resolve (x :: names) m) (← resolve names pt)
      (← resolve names t))
  | .empty => .ok .empty
  | .emptyrec ty t => do
    .ok (.emptyrec (← resolve names ty) (← resolve names t))
  | .sum l r => do .ok (.sum (← resolve names l) (← resolve names r))
  | .inl t => do .ok (.inl (← resolve names t))
  | .inr t => do .ok (.inr (← resolve names t))
  | .sumcase x m fl fr t => do
    .ok (.sumcase (← resolve (x :: names) m) (← resolve names fl)
      (← resolve names fr) (← resolve names t))
  | .susp a => do .ok (.susp (← resolve names a))
  | .north => .ok .north
  | .south => .ok .south
  | .merid a r => do .ok (.merid (← resolve names a) (← resolve names r))
  | .susprec x m nc sc mc t => do
    .ok (.susprec (← resolve (x :: names) m) (← resolve names nc)
      (← resolve names sc) (← resolve names mc) (← resolve names t))
  | .pushout a b c f g => do
    .ok (.pushout (← resolve names a) (← resolve names b)
      (← resolve names c) (← resolve names f) (← resolve names g))
  | .pinl t => do .ok (.pinl (← resolve names t))
  | .pinr t => do .ok (.pinr (← resolve names t))
  | .ppush f g c r => do
    .ok (.ppush (← resolve names f) (← resolve names g)
      (← resolve names c) (← resolve names r))
  | .pushrec x m lc rc pc t => do
    .ok (.pushrec (← resolve (x :: names) m) (← resolve names lc)
      (← resolve names rc) (← resolve names pc) (← resolve names t))
  | .defn n tm ty => do
    -- If the definition is bound in the ambient environment (the fast
    -- checking mode preloads all library definitions as variables), the
    -- reference resolves to that variable — giving one shared value per
    -- definition; otherwise it stays a `defn` node.
    match names.idxOf? ("#" ++ n) with
    | some i => .ok (.var i)
    | none => .ok (.defn n (← resolve names tm) (← resolve names ty))
  | .em1 car mul => do
    .ok (.em1 (← resolve names car) (← resolve names mul))
  | .embase => .ok .embase
  | .emloop g r => do
    .ok (.emloop (← resolve names g) (← resolve names r))
  | .emcomp mul g h r s2 => do
    .ok (.emcomp (← resolve names mul) (← resolve names g)
      (← resolve names h) (← resolve names r) (← resolve names s2))
  | .emsquash x y p q u v j1 j2 j3 => do
    .ok (.emsquash (← resolve names x) (← resolve names y)
      (← resolve names p) (← resolve names q) (← resolve names u)
      (← resolve names v) (← resolve names j1) (← resolve names j2)
      (← resolve names j3))
  | .em1rec bT gB b l c t => do
    .ok (.em1rec (← resolve names bT) (← resolve names gB)
      (← resolve names b) (← resolve names l) (← resolve names c)
      (← resolve names t))
  | .bgpd ob hom cm => do
    .ok (.bgpd (← resolve names ob) (← resolve names hom)
      (← resolve names cm))
  | .bpt t => do
    .ok (.bpt (← resolve names t))
  | .barr x y f r => do
    .ok (.barr (← resolve names x) (← resolve names y)
      (← resolve names f) (← resolve names r))
  | .bcomp cm x y z f g r s2 => do
    .ok (.bcomp (← resolve names cm) (← resolve names x)
      (← resolve names y) (← resolve names z) (← resolve names f)
      (← resolve names g) (← resolve names r) (← resolve names s2))
  | .bsquash x y p q u v j1 j2 j3 => do
    .ok (.bsquash (← resolve names x) (← resolve names y)
      (← resolve names p) (← resolve names q) (← resolve names u)
      (← resolve names v) (← resolve names j1) (← resolve names j2)
      (← resolve names j3))
  | .bgrec bT gB pf pl pc t => do
    .ok (.bgrec (← resolve names bT) (← resolve names gB)
      (← resolve names pf) (← resolve names pl) (← resolve names pc)
      (← resolve names t))
  | .bgelim x m gP pb pl pc t => do
    .ok (.bgelim (← resolve (x :: names) m) (← resolve names gP)
      (← resolve names pb) (← resolve names pl) (← resolve names pc)
      (← resolve names t))
  | .em1elim x m gP b l c t => do
    .ok (.em1elim (← resolve (x :: names) m) (← resolve names gP)
      (← resolve names b) (← resolve names l) (← resolve names c)
      (← resolve names t))
  | .list a => do .ok (.list (← resolve names a))
  | .lnil => .ok .lnil
  | .lcons h t => do .ok (.lcons (← resolve names h) (← resolve names t))
  | .listrec x m nc cc t => do
    .ok (.listrec (← resolve (x :: names) m) (← resolve names nc)
      (← resolve names cc) (← resolve names t))
  | .quot a r => do .ok (.quot (← resolve names a) (← resolve names r))
  | .qin t => do .ok (.qin (← resolve names t))
  | .qeq a b w r => do
    .ok (.qeq (← resolve names a) (← resolve names b) (← resolve names w)
      (← resolve names r))
  | .qsquash x y p q r s2 => do
    .ok (.qsquash (← resolve names x) (← resolve names y)
      (← resolve names p) (← resolve names q) (← resolve names r)
      (← resolve names s2))
  | .qelim x m mset f feq t => do
    .ok (.qelim (← resolve (x :: names) m) (← resolve names mset)
      (← resolve names f) (← resolve names feq) (← resolve names t))
  | .trunc a => do .ok (.trunc (← resolve names a))
  | .tin t => do .ok (.tin (← resolve names t))
  | .squash x y r => do
    .ok (.squash (← resolve names x) (← resolve names y) (← resolve names r))
  | .truncrec mB prp f t => do
    .ok (.truncrec (← resolve names mB) (← resolve names prp)
      (← resolve names f) (← resolve names t))
  | .torus => .ok .torus
  | .tbase => .ok .tbase
  | .tloopP r => do .ok (.tloopP (← resolve names r))
  | .tloopQ r => do .ok (.tloopQ (← resolve names r))
  | .tsurf r s2 => do
    .ok (.tsurf (← resolve names r) (← resolve names s2))
  | .torusrec x m bc pc qc sc t => do
    .ok (.torusrec (← resolve (x :: names) m) (← resolve names bc)
      (← resolve names pc) (← resolve names qc) (← resolve names sc)
      (← resolve names t))
  | .s1 => .ok .s1
  | .sbase => .ok .sbase
  | .sloop r => do .ok (.sloop (← resolve names r))
  | .s1elim x m b l t => do
    .ok (.s1elim (← resolve (x :: names) m) (← resolve names b)
      (← resolve names l) (← resolve names t))
  | .i0 => .ok .i0
  | .i1 => .ok .i1
  | .imax l r => do .ok (.imax (← resolve names l) (← resolve names r))
  | .imin l r => do .ok (.imin (← resolve names l) (← resolve names r))
  | .ineg r => do .ok (.ineg (← resolve names r))
  | .pathP i f l r => do
    .ok (.pathP (← resolve (i :: names) f) (← resolve names l) (← resolve names r))
  | .path ty l r => do
    .ok (.pathP (← resolve ("" :: names) ty) (← resolve names l) (← resolve names r))
  | .plam i b => do .ok (.plam (← resolve (i :: names) b))
  | .papp p l r s => do
    .ok (.papp (← resolve names p) (← resolve names l) (← resolve names r)
      (← resolve names s))
  | .transp i f a => do
    .ok (.transp (← resolve (i :: names) f) (← resolve names a))
  | .hcomp i ty sys u₀ => do
    let tyT ← resolve names ty
    let sysT ← sys.mapM fun (cof, body) => do
      let cofT ← cof.mapM fun (f, b) => do .ok ((← resolve names f), b)
      let bodyT ← resolve (i :: names) body
      .ok (cofT, bodyT)
    .ok (.hcomp tyT sysT (← resolve names u₀))
  | .glueTy sys base => do
    let sysT ← sys.mapM fun (cof, T, e) => do
      let cofT ← cof.mapM fun (f, b) => do .ok ((← resolve names f), b)
      .ok (cofT, (← resolve names T), (← resolve names e))
    .ok (.glueTy sysT (← resolve names base))
  | .glueTm gty sys base => do
    let gtyT ← resolve names gty
    let sysT ← sys.mapM fun (cof, t) => do
      let cofT ← cof.mapM fun (f, b) => do .ok ((← resolve names f), b)
      .ok (cofT, (← resolve names t))
    .ok (.glueTm gtyT sysT (← resolve names base))
  | .unglue gty b => do
    .ok (.unglue (← resolve names gty) (← resolve names b))
  | .ann t ty => do .ok (.ann (← resolve names t) (← resolve names ty))

end Raw

end Cubical
