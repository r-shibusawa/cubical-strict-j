import Std.Data.HashMap
import FormalizedMathematics.Cubical.Syntax

/-!
# Semantics: normalization by evaluation

Values use de Bruijn *levels*.  Closures are defunctionalized: besides the
ordinary `(env, term)` closure, dedicated constructors implement the
computation rules of `transp` (Kan transport) and `hcomp` (homogeneous
composition).

## Kan structure implemented (CCHM style, De Morgan fills)

`transp` along a line of types `A : I → U` (with `a : A 0`):

* constant family (normalize-and-occurs check): `transp A a = a`
* `A i = Π (x : B i), C i x`:
  `transp A f = λ x₁, transp (λ i, C i (w x₁ i)) (f (w x₁ 0))`
  with backward fill `w x₁ i = transp (λ j, B (i ∨ ¬j)) x₁ : B i`.
* `A i = Σ (x : B i), C i x`: componentwise via the forward fill.
* `A i = PathP (B i) (a i) (b i)` (phase 2a):
  `transp A p = ⟨j⟩ comp (λ i, B i j) [(j=0) ↦ a, (j=1) ↦ b] (p @ j)`.
* `A i = ℕ`, `A i = U`: identity.

`hcomp {A} [φₖ ↦ uₖ] u₀` where each `φₖ` is a conjunction of atomic
constraints `(r = ε)`:

* some `φₖ` is true: `hcomp = uₖ 1`
* `A = Π/Σ/PathP`: structural (Σ uses the filler `hfill` and heterogeneous
  `comp = hcomp ∘ transp`; `PathP` extends the system with the endpoints)
* `A = ℕ`: recursion on `u₀` and the tube (`zero`/`suc` commute with `hcomp`)
* `A = U`: stuck — computing this needs `Glue` (phase 2b), where univalence
  will live.

The evaluator threads a fresh-level supply `fresh` (all levels in scope are
`< fresh`); `transp`/`hcomp` use it to inspect families and tubes at a
*generic* interval point, which is sound because evaluation commutes with
instantiation.
-/

namespace Cubical

/-- An evaluated face: a conjunction of atomic constraints `(r = ε)`,
`ε ∈ {0, 1}` (encoded by the `Bool`). -/
abbrev VCof := List (IVal × Bool)

inductive CofRes where
  | isTrue | isFalse | undet
  deriving BEq, Inhabited

/-- Decide a face using canonical DNFs: true iff every constraint holds
identically, false iff some constraint identically fails. -/
def cofStatus (c : VCof) : CofRes :=
  if c.any (fun (r, b) => if b then r.isZero else r.isOne) then .isFalse
  else if c.all (fun (r, b) => if b then r.isOne else r.isZero) then .isTrue
  else .undet

/-- The `∀` operation on faces: `cofForall l φ` is the face on which `φ`
holds for *every* value of the variable at level `l` (`none` = ⊥).
For a constraint whose expression is monotone or antitone in the variable
(single DNF polarity) this is exactly the conjunction of its two endpoint
instances; mixed-polarity constraints are conservatively sent to ⊥ (sound:
the Kan operations then under-compute but never mis-compute). -/
def cofForall (lvl : Nat) (cof : VCof) : Option VCof :=
  cof.foldl (init := some []) fun acc (r, b) =>
    match acc with
    | none => none
    | some cs =>
      let addConstraint (cs : VCof) (rr : IVal) : Option VCof :=
        if (if b then rr.isOne else rr.isZero) then some cs
        else if (if b then rr.isZero else rr.isOne) then none
        else some ((rr, b) :: cs)
      if !(r.mentions lvl) then addConstraint cs r
      else if r.mixedPolarity lvl then none
      else
        match addConstraint cs (r.substLvl lvl .zero) with
        | none => none
        | some cs' => addConstraint cs' (r.substLvl lvl .one)

/-! ## `lineEquiv`: transport along a line of types is an equivalence

A closed object-language program consumed by `hcomp` at the universe:
`lineEquiv X Y P : Equiv Y X` for `P : Path U X Y`, whose function is the
reversed transport `λ y, transp (λ j, P @ ¬j) y` and whose `isEquiv` proof
transports `idIsEquiv` along the line of functions
`fᵢ := transp (λ j, P @ ¬(i ∧ j)) : Y → P @ ¬i` — at `i = 0` the family is
constant, so `f₀` is *definitionally* the identity by the constancy rule,
and the identity's fibers are contracted by the usual connection trick. -/

def lineFibRaw : Raw :=
  .sigma "x" (.var "Y")
    (.path (.papp (.var "P") (.var "X") (.var "Y") (.ineg (.var "i")))
      (.var "y")
      (.transp "j"
        (.papp (.var "P") (.var "X") (.var "Y")
          (.ineg (.imin (.var "i") (.var "j"))))
        (.var "x")))

def lineEquivRaw : Raw :=
  .lam "X" (.lam "Y" (.lam "P"
    (.pair
      (.lam "y0" (.transp "j"
        (.papp (.var "P") (.var "X") (.var "Y") (.ineg (.var "j")))
        (.var "y0")))
      (.transp "i"
        (.pi "y" (.papp (.var "P") (.var "X") (.var "Y") (.ineg (.var "i")))
          (.sigma "ctr" lineFibRaw
            (.pi "other" lineFibRaw
              (.path lineFibRaw (.var "ctr") (.var "other")))))
        (.lam "y" (.pair
          (.pair (.var "y") (.plam "k" (.var "y")))
          (.lam "fib" (.plam "i2" (.pair
            (.papp (.snd (.var "fib")) (.var "y") (.fst (.var "fib")) (.var "i2"))
            (.plam "j2"
              (.papp (.snd (.var "fib")) (.var "y") (.fst (.var "fib"))
                (.imin (.var "i2") (.var "j2")))))))))))))

/-- The resolved core term of `lineEquiv`. -/
def lineEquivTm : Term :=
  match lineEquivRaw.resolve [] with
  | .ok t => t
  | .error e => panic! s!"lineEquiv failed to resolve: {e}"

/-- `isGroupoid` as a closed object-language predicate (shared by the
`em1rec`/`em1elim` typing rules and the `em1elimGCod` closure). -/
def em1IsGpdRaw : Raw :=
  .lam "B" (.pi "a" (.var "B") (.pi "b" (.var "B")
    (.pi "p" (.path (.var "B") (.var "a") (.var "b"))
    (.pi "q" (.path (.var "B") (.var "a") (.var "b"))
    (.pi "r" (.path (.path (.var "B") (.var "a") (.var "b"))
        (.var "p") (.var "q"))
    (.pi "s" (.path (.path (.var "B") (.var "a") (.var "b"))
        (.var "p") (.var "q"))
      (.path (.path (.path (.var "B") (.var "a") (.var "b"))
          (.var "p") (.var "q"))
        (.var "r") (.var "s"))))))))

def em1IsGpdTm : Term :=
  match em1IsGpdRaw.resolve [] with
  | .ok t => t
  | .error _ => .univ 0

mutual

inductive Val where
  | vuniv (lvl : Nat)
  | vnat
  | vzero
  | vsucc (lb : Nat) (n : Val)
  | vint
  | vipos (lb : Nat) (n : Val)
  | vinegsuc (lb : Nat) (n : Val)
  | vunit
  | vtt
  | vempty
  | vsum (lb : Nat) (l r : Val)
  | vinl (lb : Nat) (t : Val)
  | vinr (lb : Nat) (t : Val)
  | vsusp (lb : Nat) (a : Val)
  | vnorth
  | vsouth
  | vmerid (lb : Nat) (a : Val) (r : IVal)
  | vpushout (lb : Nat) (a b c f g : Val)
  | vpinl (lb : Nat) (t : Val)
  | vpinr (lb : Nat) (t : Val)
  | vppush (lb : Nat) (f g c : Val) (r : IVal)
  | vem1 (lb : Nat) (car mul : Val)
  | vembase
  | vemloop (lb : Nat) (g : Val) (r : IVal)
  | vemcomp (lb : Nat) (mul g h : Val) (rj ri : IVal)
  | vemsquash (lb : Nat) (x y p q u v : Val) (r1 r2 r3 : IVal)
  /-- Classifying space of an internal groupoid, and its cells. -/
  | vbgpd (lb : Nat) (ob hom cmp : Val)
  | vbpt (lb : Nat) (t : Val)
  | vbarr (lb : Nat) (x y f : Val) (r : IVal)
  | vbcomp (lb : Nat) (cmp x y z f g : Val) (rj ri : IVal)
  | vbsquash (lb : Nat) (x y p q u v : Val) (r1 r2 r3 : IVal)
  | vlist (lb : Nat) (a : Val)
  | vlnil
  | vlcons (lb : Nat) (h t : Val)
  | vquot (lb : Nat) (a r : Val)
  | vqin (lb : Nat) (t : Val)
  | vqeq (lb : Nat) (a b w : Val) (r : IVal)
  | vqsquash (lb : Nat) (x y p q : Val) (r s : IVal)
  | vtrunc (lb : Nat) (a : Val)
  | vtin (lb : Nat) (t : Val)
  | vsquash (lb : Nat) (x y : Val) (r : IVal)
  | vtorus
  | vtbase
  | vtloopP (r : IVal)
  | vtloopQ (r : IVal)
  | vtsurf (r s : IVal)
  | vs1
  | vsbase
  | vsloop (r : IVal)
  | vpi (lb : Nat) (dom : Val) (cod : Closure)
  | vlam (lb : Nat) (body : Closure)
  | vsigma (lb : Nat) (dom : Val) (cod : Closure)
  | vpair (lb : Nat) (a b : Val)
  | vpathP (lb : Nat) (fam : Closure) (lhs rhs : Val)
  | vplam (lb : Nat) (body : Closure)
  | vi (r : IVal)
  /-- `Glue [φₖ ↦ (Tₖ, eₖ)] A`.  Branches are kept *unfiltered and
  uncollapsed* so that positions are stable across instantiation; the
  face reductions happen lazily in `force`. -/
  | vglueTy (lb : Nat) (sys : List (VCof × Val × Val)) (base : Val)
  /-- `glue [φₖ ↦ tₖ] a`, tagged with its `Glue` type. -/
  | vglue (lb : Nat) (ty : Val) (sys : List (VCof × Val)) (base : Val)
  | vne (lb : Nat) (n : Neutral)

inductive Neutral where
  | var (lvl : Nat)
  | app (fn : Neutral) (arg : Val)
  | fst (p : Neutral)
  | snd (p : Neutral)
  | natrec (motive : Closure) (z s : Val) (n : Neutral)
  | papp (p : Neutral) (lhs rhs : Val) (r : IVal)
  | transp (fam : Closure) (a : Val)
  /-- Blocked composition (neutral type, neutral ℕ base, or type `U`). -/
  | hcomp (ty : Val) (sys : List (VCof × Closure)) (u₀ : Val)
  /-- Blocked `unglue` (tagged with the `Glue` type of `b`). -/
  | unglue (ty : Val) (b : Neutral)
  /-- Blocked circle elimination. -/
  | s1elim (motive : Closure) (b l : Val) (t : Neutral)
  /-- Blocked ℤ case split. -/
  | intcase (motive : Closure) (fpos fneg : Val) (t : Neutral)
  /-- Blocked unit elimination. -/
  | unitrec (motive : Closure) (ptt : Val) (t : Neutral)
  /-- Blocked empty elimination. -/
  | emptyrec (ty : Val) (t : Neutral)
  /-- Blocked sum case split. -/
  | sumcase (motive : Closure) (fl fr : Val) (t : Neutral)
  /-- Blocked suspension elimination. -/
  | susprec (motive : Closure) (nc sc mc : Val) (t : Neutral)
  /-- Blocked torus elimination. -/
  | torusrec (motive : Closure) (bc pc qc sc : Val) (t : Neutral)
  /-- Blocked truncation elimination. -/
  | truncrec (mB prp f : Val) (t : Neutral)
  /-- Blocked pushout elimination. -/
  | pushrec (motive : Closure) (lc rc pc : Val) (t : Neutral)
  /-- Blocked list elimination. -/
  | listrec (motive : Closure) (nc cc : Val) (t : Neutral)
  /-- Blocked EM₁ elimination; `emsquashCell` wraps a generic truncation
  cell kept neutral (sound: `force` collapses decided faces). -/
  | em1rec (B gB b l c : Val) (t : Neutral)
  | em1elim (motive : Closure) (gP b l c : Val) (t : Neutral)
  /-- Blocked groupoid-classifying-space recursion. -/
  | bgrec (bT gB pf pl pc : Val) (t : Neutral)
  | bgelim (motive : Closure) (gP pb pl pc : Val) (t : Neutral)
  | emsquashCell (x y p q u v : Val) (r1 r2 r3 : IVal)
  /-- Blocked quotient elimination.  Also used (with a `.qsquashCell`
  scrutinee wrapper) for the deliberately-stuck squash rule. -/
  | qelim (motive : Closure) (mset f feq : Val) (t : Neutral)
  /-- A generic squash cell, kept neutral under `qelim` (sound: the cell
  collapses in `force` whenever an interval argument is decided). -/
  | qsquashCell (x y p q : Val) (r s : IVal)

inductive Closure where
  | mk (lb : Nat) (env : List Val) (body : Term)
  /-- `reparam c f` is the line `λ j, c (f j)`. -/
  | reparam (c : Closure) (f : IVal → IVal)
  /-- Constant closure. -/
  | constV (v : Val)
  /-- Composition `λ x, outer (inner x)`. -/
  | comp (outer inner : Closure)
  /-- Domain line of a line of `Π`-types. -/
  | piDomOf (c : Closure)
  /-- Domain line of a line of `Σ`-types. -/
  | sigDomOf (c : Closure)
  /-- Body of `transp` on a `Π`-family. -/
  | transpPi (fam : Closure) (f : Val)
  /-- The family `λ i, C i (w x₁ i)` used by `transpPi`. -/
  | transpPiCod (fam : Closure) (x₁ : Val)
  /-- The family `λ i, C i (u i)` used by `transp` on a `Σ`-family. -/
  | transpSigSnd (fam : Closure) (u : Val)
  /-- Body (in `j`) of `transp` on a `PathP`-family. -/
  | transpPathP (fam : Closure) (p : Val)
  /-- The line `λ i, B i j` of a `PathP`-family, at a fixed `j`. -/
  | pathPLine (fam : Closure) (j : IVal)
  /-- The endpoint line `λ i, aᵢ` (resp. `bᵢ`) of a `PathP`-family. -/
  | pathPEnd (fam : Closure) (side : Bool)
  /-- Tube branch transformers for structural `hcomp`. -/
  | mapApp (br : Closure) (x : Val)
  | mapFst (br : Closure)
  | mapSnd (br : Closure)
  | mapPApp (br : Closure) (lhs rhs : Val) (j : IVal)
  | natPred (br : Closure)
  /-- Body of `hcomp` at a `Π`-type. -/
  | hcompPi (cod : Closure) (sys : List (VCof × Closure)) (u₀ : Val)
  /-- Body (in `j`) of `hcomp` at a `PathP`-type. -/
  | hcompPathP (fam : Closure) (lhs rhs : Val)
      (sys : List (VCof × Closure)) (u₀ : Val)
  /-- The filler line `λ i, hfill ty sys u₀ i`. -/
  | hfill (ty : Val) (sys : List (VCof × Closure)) (u₀ : Val)
  /-- Tube branch of heterogeneous `comp`: `λ i, transp (λ i', L (i ∨ i')) (br i)`. -/
  | compTube (line : Closure) (br : Closure)
  /-- Base line `λ i, A i` of a line of `Glue` types. -/
  | glueBase (fam : Closure)
  /-- The `k`-th branch type line `λ i, Tₖ i` of a line of `Glue` types. -/
  | glueBranchT (fam : Closure) (k : Nat)
  /-- The `k`-th branch equivalence line `λ i, wₖ i`. -/
  | glueBranchW (fam : Closure) (k : Nat)
  /-- δ-tube of Glue transport: `λ i, (wₖ i).fst (transpFill Tₖ u₀ i)`. -/
  | glueDeltaTube (fam : Closure) (k : Nat) (u₀ : Val)
  /-- Codomain of a fiber Σ-type: `λ x, Path A a (f x)`. -/
  | fiberCod (f : Val) (A a : Val)
  /-- The line `λ j, p @ j` for a path value `p` with the given endpoints. -/
  | pappLine (p : Val) (lhs rhs : Val)
  /-- The family `λ i, P (sloop i)` of a circle motive. -/
  | s1loopFam (motive : Closure)
  /-- Tube transformer `λ i, s1elim P b l (br i)`. -/
  | s1elimTube (motive : Closure) (b l : Val) (br : Closure)
  /-- Tube transformers unwrapping `ipos`/`inegsuc` for `hcomp` at ℤ. -/
  | iposArg (br : Closure)
  | inegsucArg (br : Closure)
  /-- Tube transformers unwrapping `inl`/`inr` for `hcomp` at sums. -/
  | inlArg (br : Closure)
  | inrArg (br : Closure)
  /-- Type of the `natrec` step: `λ k, Π (_ : P k), P (succ k)`. -/
  | natrecS (motive : Closure)
  | natrecS2 (motive : Closure) (k : Val)
  /-- Types of the `intcase` branches: `λ n, P (ipos n)` / `λ n, P (inegsuc n)`. -/
  | intcasePos (motive : Closure)
  | intcaseNeg (motive : Closure)
  /-- Types of the `sumcase` branches. -/
  | sumcaseL (motive : Closure)
  | sumcaseR (motive : Closure)
  /-- Component lines of a line of sum types. -/
  | sumLeftOf (c : Closure)
  | sumRightOf (c : Closure)
  /-- The codomain of the merid-case of `susprec`:
  `λ a, PathP (λ j, P (merid a j)) nc sc`. -/
  | suspMcCod (motive : Closure) (nc sc : Val)
  /-- The family `λ j, P (merid a j)`. -/
  | suspMeridFam (motive : Closure) (a : Val)
  /-- The parameter line of a line of suspensions. -/
  | suspLineOf (c : Closure)
  /-- Tube transformer `λ i, susprec P nc sc mc (br i)`. -/
  | susprecTube (motive : Closure) (nc sc mc : Val) (br : Closure)
  /-- Families `λ i, P (tloopP i)` / `λ i, P (tloopQ i)`. -/
  | torusLoopPFam (motive : Closure)
  | torusLoopQFam (motive : Closure)
  /-- Outer family of the 2-cell case:
  `λ i, PathP (λ j, P (tsurf i j)) (pc @ i) (pc @ i)`. -/
  | torusSurfFam (motive : Closure) (bc pc : Val)
  /-- Its inner family `λ j, P (tsurf ri j)` at a fixed `ri`. -/
  | torusSurfInner (motive : Closure) (ri : IVal)
  /-- Tube transformer for `torusrec` over hcomp cells. -/
  | torusrecTube (motive : Closure) (bc pc qc sc : Val) (br : Closure)
  /-- The codomains of the point-cases of `pushrec`. -/
  | pushLcCod (motive : Closure)
  | pushRcCod (motive : Closure)
  /-- The codomain of the path-case of `pushrec`:
  `λ c, PathP (λ i, P (ppush c i)) (lc (f c)) (rc (g c))`. -/
  | pushPcCod (motive : Closure) (lc rc f g : Val)
  /-- The family `λ i, P (ppush c i)`. -/
  | pushPcFam (motive : Closure) (f g c : Val)
  /-- Component lines of a line of pushouts. -/
  | pushAOf (c : Closure)
  | pushBOf (c : Closure)
  | pushCOf (c : Closure)
  /-- Tube transformer for `pushrec` over hcomp cells. -/
  | pushrecTube (motive : Closure) (lc rc pc : Val) (br : Closure)
  /-- The codomain tower of `em1rec`'s comp-case:
  `λ g, Π h. PathP (λ j, Path B b (l h @ j)) (l g) (l (g·h))`. -/
  | em1recCCod (B C mul l b : Val)
  | em1recCCod2 (B mul l b g : Val)
  | em1recCFam (B l b h : Val)
  /-- The case types of the dependent `em1elim`. -/
  | em1elimLCod (motive : Closure) (b : Val)
  | em1elimLFam (motive : Closure) (g : Val)
  | em1elimDCCod (motive : Closure) (C mul l b : Val)
  | em1elimDCCod2 (motive : Closure) (mul l b g : Val)
  | em1elimDCFam (motive : Closure) (mul l b g h : Val)
  | em1elimDCInner (motive : Closure) (mul g h : Val) (rj : IVal)
  | em1elimGCod (motive : Closure)
  /-- Tube transformer for `em1elim` over hcomp cells. -/
  | em1elimTube (motive : Closure) (gP b l c : Val) (br : Closure)
  /-- Parameter lines of a line of EM₁ types. -/
  | em1CarOf (c : Closure)
  /-- Tube transformer for `em1rec` over hcomp cells. -/
  | em1recTube (B gB b l c : Val) (br : Closure)
  | bgrecTube (bT gB pf pl pc : Val) (br : Closure)
  | bgelimTube (motive : Closure) (gP pb pl pc : Val) (br : Closure)
  /-- The codomain tower of `listrec`'s cons-case:
  `λ h, Π (t : list A). P t → P (cons h t)`. -/
  | listCcCod (motive : Closure) (A : Val)
  | listCcCod2 (motive : Closure) (h : Val)
  /-- The parameter line of a line of lists. -/
  | listArgOf (c : Closure)
  /-- Tube transformers unwrapping `cons` for `hcomp` at lists. -/
  | lheadArg (br : Closure)
  | ltailArg (br : Closure)
  /-- Tube transformer for `listrec` over hcomp cells. -/
  | listrecTube (motive : Closure) (nc cc : Val) (br : Closure)
  /-- The codomain of the point-case of `qelim`. -/
  | qelimInCod (motive : Closure)
  /-- The codomain of the path-case:
  `λ a, Π b. Π (w : R a b). PathP (λ i, P (qeq a b w i)) (f a) (f b)`. -/
  | qelimEqCod (motive : Closure) (A rel f : Val)
  | qelimEqCod2 (motive : Closure) (rel f a : Val)
  | qelimEqCod3 (motive : Closure) (f a b : Val)
  | qelimEqFam (motive : Closure) (a b w : Val)
  /-- The `isSet` requirement of `qelim`, and its Π-tower. -/
  | qelimSetCod (motive : Closure)
  | isSetOf1 (T : Val)
  | isSetOf2 (T u : Val)
  | isSetOf3 (T u v : Val)
  | isSetOf4 (T u v p : Val)
  /-- Component lines of a line of quotients. -/
  | quotAOf (c : Closure)
  /-- Tube transformer for `qelim` over hcomp cells. -/
  | qelimTube (motive : Closure) (mset f feq : Val) (br : Closure)
  /-- The argument line of a line of truncations. -/
  | truncArgOf (c : Closure)
  /-- Tube transformer for `truncrec` over hcomp cells. -/
  | truncrecTube (mB prp f : Val) (br : Closure)

end

instance : Inhabited Val := ⟨.vuniv 0⟩
instance : Inhabited Neutral := ⟨.var 0⟩
instance : Inhabited Closure := ⟨.mk 0 [] (.univ 0)⟩

/-- Extract an interval value (interval-typed entries are stored as `.vi`). -/
def Val.asIVal : Val → IVal
  | .vi r => r
  | _ => panic! "asIVal: not an interval value"

/-- Head tag, for diagnostics. -/
partial def Val.head : Val → String
  | .vuniv _ => "univ" | .vnat => "nat" | .vzero => "zero" | .vsucc _ _ => "succ"
  | .vint => "int" | .vipos _ _ => "ipos" | .vinegsuc _ _ => "inegsuc"
  | .vunit => "unit" | .vtt => "tt" | .vempty => "empty"
  | .vsum _ _ _ => "sum" | .vinl _ _ => "inl" | .vinr _ _ => "inr"
  | .vs1 => "s1" | .vsbase => "sbase" | .vsloop _ => "sloop"
  | .vsusp _ _ => "susp" | .vnorth => "north" | .vsouth => "south"
  | .vmerid _ _ _ => "merid"
  | .vpushout _ _ _ _ _ _ => "pushout" | .vpinl _ _ => "pinl"
  | .vpinr _ _ => "pinr" | .vppush _ _ _ _ _ => "ppush"
  | .vem1 _ _ _ => "em1" | .vembase => "embase" | .vemloop _ _ _ => "emloop"
  | .vemcomp _ _ _ _ _ _ => "emcomp" | .vemsquash _ _ _ _ _ _ _ _ _ _ => "emsquash"
  | .vbgpd _ _ _ _ => "bgpd" | .vbpt _ _ => "bpt" | .vbarr _ _ _ _ _ => "barr"
  | .vbcomp _ _ _ _ _ _ _ _ _ => "bcomp"
  | .vbsquash _ _ _ _ _ _ _ _ _ _ => "bsquash"
  | .vlist _ _ => "list" | .vlnil => "lnil" | .vlcons _ _ _ => "lcons"
  | .vquot _ _ _ => "quot" | .vqin _ _ => "qin" | .vqeq _ _ _ _ _ => "qeq"
  | .vqsquash _ _ _ _ _ _ _ => "qsquash"
  | .vtrunc _ _ => "trunc" | .vtin _ _ => "tin" | .vsquash _ _ _ _ => "squash"
  | .vtorus => "torus" | .vtbase => "tbase" | .vtloopP _ => "tloopP"
  | .vtloopQ _ => "tloopQ" | .vtsurf _ _ => "tsurf"
  | .vpi _ _ _ => "pi" | .vlam _ _ => "lam" | .vsigma _ _ _ => "sigma"
  | .vpair _ _ _ => "pair" | .vpathP _ _ _ _ => "pathP" | .vplam _ _ => "plam"
  | .vi _ => "interval" | .vglueTy _ _ _ => "glueTy" | .vglue _ _ _ _ => "glue"
  | .vne _ (.var _) => "ne.var" | .vne _ (.app _ _) => "ne.app"
  | .vne _ (.fst _) => "ne.fst" | .vne _ (.snd _) => "ne.snd"
  | .vne _ (.natrec _ _ _ _) => "ne.natrec" | .vne _ (.papp _ _ _ _) => "ne.papp"
  | .vne _ (.transp _ _) => "ne.transp" | .vne _ (.hcomp t _ _) => s!"ne.hcomp({t.head})"
  | .vne _ (.unglue _ _) => "ne.unglue" | .vne _ (.s1elim _ _ _ _) => "ne.s1elim"
  | .vne _ (.intcase _ _ _ _) => "ne.intcase"
  | .vne _ (.unitrec _ _ _) => "ne.unitrec" | .vne _ (.emptyrec _ _) => "ne.emptyrec"
  | .vne _ (.sumcase _ _ _ _) => "ne.sumcase"
  | .vne _ (.susprec _ _ _ _ _) => "ne.susprec"
  | .vne _ (.torusrec _ _ _ _ _ _) => "ne.torusrec"
  | .vne _ (.truncrec _ _ _ _) => "ne.truncrec"
  | .vne _ (.pushrec _ _ _ _ _) => "ne.pushrec"
  | .vne _ (.qelim _ _ _ _ _) => "ne.qelim"
  | .vne _ (.listrec _ _ _ _) => "ne.listrec"
  | .vne _ (.em1rec _ _ _ _ _ _) => "ne.em1rec"
  | .vne _ (.em1elim _ _ _ _ _ _) => "ne.em1elim"
  | .vne _ (.bgrec _ _ _ _ _ _) => "ne.bgrec"
  | .vne _ (.bgelim _ _ _ _ _ _) => "ne.bgelim"
  | .vne _ (.emsquashCell _ _ _ _ _ _ _ _ _) => "ne.emsquashCell"
  | .vne _ (.qsquashCell _ _ _ _ _ _) => "ne.qsquashCell"


/-- Evaluation cache for `defn` bodies (closed global definitions).
Keyed by the *pointer* of the term (LibDef terms are pointer-stable), so
every use of a definition shares one value — which in turn lets the
pointer-equality conversion short-circuits fire.  The pure model just
recomputes. -/
initialize defnEvalCache : IO.Ref (List (UInt64 × String × Val)) ←
  (IO.mkRef []).toIO

/-! ## Profiling instrumentation (returns `false`; the unsafe
implementation bumps a global counter — used to locate evaluator hot
paths; negligible when the interpreter is not running). -/
initialize profCounters : IO.Ref (Array Nat) ←
  (IO.mkRef (Array.replicate 8 0)).toIO

/-- Master switch for profiling ticks.  OFF by default so that ordinary
builds (whose `#guard` checks execute the precompiled evaluator, where
`implemented_by` overrides are live) pay only a ref-read per tick site.
Runners that want counters call `profEnable`. -/
initialize profEnabledRef : IO.Ref Bool ← (IO.mkRef false).toIO

/-- Master switch for the defn evaluation cache — same rationale. -/
initialize defnCacheEnabledRef : IO.Ref Bool ← (IO.mkRef false).toIO

/-- Switch for the value-retaining occurs-check / conversion memos.  Kept
OFF: retaining `Val`/`Neutral` graphs in an `initialize` ref triggers
`lean_mark_mt` walks over the stored subgraphs, which for the large
embedded witnesses dominates runtime — while the cheap scalar-only
`lvlClosedByCache` shortcut (defn values are pointer-shared and cut in
O(1)) already removes the exponential.  Gated separately from the defn
cache so the latter's `lvlClosedByCache` stays live. -/
initialize heavyMemoEnabledRef : IO.Ref Bool ← (IO.mkRef false).toIO

/-- Switch for the (shelved) `capp` memo table.  Kept OFF: storing values
into an `initialize` `IO.Ref` triggers `lean_mark_mt` walks over the whole
stored graph and defeats in-place `HashMap` updates (every insert copies
the backing array) — a Lean-runtime wall, not a design bug.  Re-enabling
requires an `@[extern]` C side table or threading state through the
evaluator. -/
initialize cappCacheEnabledRef : IO.Ref Bool ← (IO.mkRef false).toIO

unsafe def profTickUnsafe (tag : Nat) (dummy : Val) : Bool :=
  unsafeBaseIO do
    if (← profEnabledRef.get) then
      -- `dummy` must contribute to the arithmetic: otherwise the code
      -- generator drops the unused argument (`__redArg`), the remaining
      -- application is closed again, and once-cell extraction reduces
      -- the whole site to a single tick per program run.
      let inc := if ptrAddrUnsafe dummy == 0 then 2 else 1
      profCounters.modify (fun a => a.set! tag (a[tag]! + inc))
    pure false
/-- The `Val` argument keeps every call site a non-closed term, defeating
the code generator's once-cell extraction of closed applications (which
would otherwise evaluate the tick exactly once per site). -/
@[never_extract, implemented_by profTickUnsafe]
opaque profTick (_tag : Nat) (_dummy : Val) : Bool

def profRead : IO (Array Nat) := profCounters.get
def profReset : IO Unit := profCounters.set (Array.replicate 8 0)
def profEnable : IO Unit := profEnabledRef.set true
def defnCacheEnable : IO Unit := defnCacheEnabledRef.set true
def cappCacheEnable : IO Unit := cappCacheEnabledRef.set true
def heavyMemoEnable : IO Unit := heavyMemoEnabledRef.set true


/-- Evaluation of a global-definition reference.  The pure model just runs
the thunk (identical to pre-cache semantics — and it is what the
elaborator's interpreter executes, since the interpreter ignores
`implemented_by`); the native override memoizes one shared value per
definition name, making every use pointer-equal so that the `valPtrEq`
conversion short-circuits can fire.  Counter slot 6 records native cache
hits, slot 7 misses. -/
unsafe def evalDefnCachedUnsafe (name : String) (fresh : Nat)
    (compute : Unit → Val) : Val :=
  unsafeBaseIO do
    if !(← defnCacheEnabledRef.get) then
      pure (compute ())
    else
      -- Key by name only.  (A (name, fresh) key was tried defensively
      -- during the 2026-07-13 deadlock hunt; it multiplies entries by
      -- every binder depth and the linear scan became 79% of runtime —
      -- ALL native runners were quadratically stalled.  Closed defn
      -- values are fresh-independent in this NbE — witnessed by
      -- uaCompMul passing with 30M name-keyed hits — so one entry per
      -- name suffices.)
      let _ := fresh
      let h := name.hash
      let m ← defnEvalCache.get
      match m.find? (fun (h2, n2, _) => h2 == h && (ptrEq n2 name || n2 == name)) with
      | some (_, _, v) =>
        profCounters.modify (fun a => a.set! 6 (a[6]! + 1))
        pure v
      | none =>
        -- get/set, NOT modify: `unsafeBaseIO` presents this code to the
        -- compiler as pure, so `compute ()` may be floated inside a
        -- `modify` closure — which then runs nested defn evaluations
        -- (and their cache reads) while the ref is taken: self-deadlock
        -- (observed: `lean_st_ref_get` blocked in `__ulock_wait`).  With
        -- get/set the worst case is a lost update, which a cache
        -- tolerates.
        let v := compute ()
        let m2 ← defnEvalCache.get
        defnEvalCache.set ((h, name, v) :: m2)
        profCounters.modify (fun a => a.set! 7 (a[7]! + 1))
        pure v

@[never_extract, implemented_by evalDefnCachedUnsafe]
def evalDefnCached (_name : String) (_fresh : Nat) (compute : Unit → Val) :
    Val :=
  compute ()

/-- Pointer addresses of the values stored in `defnEvalCache`.  Those
values are *closed* (level-free), and the cache retains them, so their
addresses stay valid; membership certifies level-freeness in O(1).  The
set holds only scalars, so storing it in an `initialize` ref incurs no
`mark_mt` graph walks. -/
initialize defnClosedPtrs : IO.Ref (Std.HashSet UInt64) ←
  (IO.mkRef {}).toIO

/-- `usesLvl` shortcut: a value pointer-identical to a cached defn value
is closed, hence mentions no level.  Pure model: unknown (`false` =
"not certified", caller falls through to the structural walk). -/
unsafe def lvlClosedByCacheUnsafe (v : Val) : Bool :=
  unsafeBaseIO do
    if !(← defnCacheEnabledRef.get) then
      pure false
    else
      let ps ← defnClosedPtrs.get
      pure (ps.contains (ptrAddrUnsafe v).toUInt64)

@[never_extract, implemented_by lvlClosedByCacheUnsafe]
opaque lvlClosedByCache (_v : Val) : Bool

/-- Memo tables for the level occurs-check: value/neutral pointer × level
→ result.  Sub-value graphs are heavily shared, so memoization turns the
exponential instantiation-based walk into a linear one.  Entries retain
their keys (address validity).  Deadlock-safety: the result is *forced by
an `if` before* any `modify`, so `compute` can never be floated into a
closure that runs while a ref is taken. -/
initialize usesLvlMemoV :
    IO.Ref (Std.HashMap UInt64 (List (Val × Nat × Bool))) ←
  (IO.mkRef {}).toIO
initialize usesLvlMemoN :
    IO.Ref (Std.HashMap UInt64 (List (Neutral × Nat × Bool))) ←
  (IO.mkRef {}).toIO

unsafe def usesLvlMemoVUnsafe (l : Nat) (v : Val)
    (compute : Unit → Bool) : Bool :=
  unsafeBaseIO do
    if !(← heavyMemoEnabledRef.get) then
      pure (compute ())
    else
      let h := mixHash (ptrAddrUnsafe v).toUInt64 (UInt64.ofNat l)
      let hit ← do
        let m ← usesLvlMemoV.get
        pure ((m.getD h []).find? (fun (v2, l2, _) =>
          ptrAddrUnsafe v2 == ptrAddrUnsafe v && l2 == l))
      match hit with
      | some (_, _, r) => pure r
      | none =>
        let r := compute ()
        if r then
          usesLvlMemoV.modify (fun m2 =>
            if m2.size < 4000000 then
              m2.insert h ((v, l, true) :: m2.getD h []) else m2)
          pure true
        else
          usesLvlMemoV.modify (fun m2 =>
            if m2.size < 4000000 then
              m2.insert h ((v, l, false) :: m2.getD h []) else m2)
          pure false

@[never_extract, implemented_by usesLvlMemoVUnsafe]
def usesLvlMemoVHook (_l : Nat) (_v : Val) (compute : Unit → Bool) :
    Bool :=
  compute ()

unsafe def usesLvlMemoNUnsafe (l : Nat) (n : Neutral)
    (compute : Unit → Bool) : Bool :=
  unsafeBaseIO do
    if !(← heavyMemoEnabledRef.get) then
      pure (compute ())
    else
      let h := mixHash (ptrAddrUnsafe n).toUInt64 (UInt64.ofNat l)
      let hit ← do
        let m ← usesLvlMemoN.get
        pure ((m.getD h []).find? (fun (n2, l2, _) =>
          ptrAddrUnsafe n2 == ptrAddrUnsafe n && l2 == l))
      match hit with
      | some (_, _, r) => pure r
      | none =>
        let r := compute ()
        if r then
          usesLvlMemoN.modify (fun m2 =>
            if m2.size < 4000000 then
              m2.insert h ((n, l, true) :: m2.getD h []) else m2)
          pure true
        else
          usesLvlMemoN.modify (fun m2 =>
            if m2.size < 4000000 then
              m2.insert h ((n, l, false) :: m2.getD h []) else m2)
          pure false

@[never_extract, implemented_by usesLvlMemoNUnsafe]
def usesLvlMemoNHook (_l : Nat) (_n : Neutral) (compute : Unit → Bool) :
    Bool :=
  compute ()

/-- Pair-keyed conversion memo: `(ptr v, ptr w, depth) → Bool`.  The two
sides of a big conversion recur over shared substructure, so memoization
collapses the repeated witness walks that neither pointer-equality (the
sides come from separate evaluations) nor the defn cache (only leaf
values are shared) can catch.  Keys retained; results forced by `if`
before any `modify` (the deadlock-safe idiom). -/
initialize convMemo :
    IO.Ref (Std.HashMap UInt64 (List (Val × Val × Nat × Bool))) ←
  (IO.mkRef {}).toIO

unsafe def convMemoUnsafe (depth : Nat) (v w : Val)
    (compute : Unit → Bool) : Bool :=
  unsafeBaseIO do
    if !(← heavyMemoEnabledRef.get) then
      pure (compute ())
    else
      let h := mixHash (mixHash (ptrAddrUnsafe v).toUInt64
        (ptrAddrUnsafe w).toUInt64) (UInt64.ofNat depth)
      let hit ← do
        let m ← convMemo.get
        pure ((m.getD h []).find? (fun (v2, w2, d2, _) =>
          ptrAddrUnsafe v2 == ptrAddrUnsafe v
            && ptrAddrUnsafe w2 == ptrAddrUnsafe w && d2 == depth))
      match hit with
      | some (_, _, _, r) => pure r
      | none =>
        let r := compute ()
        if r then
          convMemo.modify (fun m2 =>
            if m2.size < 4000000 then
              m2.insert h ((v, w, depth, true) :: m2.getD h []) else m2)
          pure true
        else
          convMemo.modify (fun m2 =>
            if m2.size < 4000000 then
              m2.insert h ((v, w, depth, false) :: m2.getD h []) else m2)
          pure false

@[never_extract, implemented_by convMemoUnsafe]
def convMemoHook (_depth : Nat) (_v _w : Val) (compute : Unit → Bool) :
    Bool :=
  compute ()

/-- Memoization table for closure application: buckets keyed by a hash of
`(ptr c, ptr v, fresh)`; entries retain `c` and `v` (so their addresses
cannot be reused — an address match therefore implies object identity,
making pointer keys sound).  `capp` is a pure function of exactly these
three arguments, so caching is unconditionally sound. -/
initialize cappCache :
    IO.Ref (Std.HashMap UInt64 (List (Closure × Val × Nat × Val))) ←
  (IO.mkRef {}).toIO
/-- Scratch cell used to *force* a computed value through an IO primitive
before any cache-ref operation: the argument of `set` is evaluated with no
ref held, and IO ordering cannot be rearranged — this is the only reliable
barrier against the optimizer floating `compute ()` into a `modify`
closure (the self-deadlock pattern). -/
initialize cappScratch : IO.Ref (Option Val) ← (IO.mkRef none).toIO

unsafe def cappCachedUnsafe (c : Closure) (v : Val) (fresh : Nat)
    (compute : Unit → Val) : Val :=
  unsafeBaseIO do
    if !(← cappCacheEnabledRef.get) then
      pure (compute ())
    else
      let h := mixHash (mixHash (ptrAddrUnsafe c).toUInt64
        (ptrAddrUnsafe v).toUInt64) (UInt64.ofNat fresh)
      -- The map local must DIE before `compute` runs: any live reference
      -- pins the map shared, and every nested insert then copies the
      -- whole backing array (observed as a quadratic blow-up).
      let hit ← do
        let m ← cappCache.get
        pure ((m.getD h []).find? (fun (c2, v2, f2, _) =>
          ptrAddrUnsafe c2 == ptrAddrUnsafe c
            && ptrAddrUnsafe v2 == ptrAddrUnsafe v && f2 == fresh))
      match hit with
      | some (_, _, _, r) =>
        profCounters.modify (fun a => a.set! 2 (a[2]! + 1))
        pure r
      | none =>
        let r := compute ()
        -- Deadlock-safe: `r`'s head is forced by branching on a cheap
        -- pointer test BEFORE any `modify`, so `compute` cannot float
        -- into a closure that runs while a ref is taken.
        if ptrAddrUnsafe r == 0 then
          pure r
        else
          cappCache.modify (fun m2 =>
            if m2.size < 8000000 then
              m2.insert h ((c, v, fresh, r) :: m2.getD h [])
            else m2)
          pure r

@[never_extract, implemented_by cappCachedUnsafe]
def cappCached (_c : Closure) (_v : Val) (_fresh : Nat)
    (compute : Unit → Val) : Val :=
  compute ()

/-- Sentinel "unknown / possibly any level" bound (never lets the
occurs-check short-circuit fire): sound over-approximation. -/
def sentinelLb : Nat := 1000000000

mutual
/-- Upper bound on free de Bruijn levels of a value (`0` = closed).
Sound over-approximation: exact for simple constructors, `sentinelLb`
for any constructor carrying list/tuple/function fields. -/
partial def cofLb : VCof → Nat
  | [] => 0
  | (r, _) :: rest => Nat.max r.levelBound (cofLb rest)
partial def sysLb : List (VCof × Closure) → Nat
  | [] => 0
  | (co, br) :: rest =>
    Nat.max (Nat.max (cofLb co) (closureLb br)) (sysLb rest)
partial def glueTySysLb : List (VCof × Val × Val) → Nat
  | [] => 0
  | (co, T, e) :: rest =>
    Nat.max (Nat.max (cofLb co) (Nat.max (valLb T) (valLb e)))
      (glueTySysLb rest)
partial def glueSysLb : List (VCof × Val) → Nat
  | [] => 0
  | (co, t) :: rest =>
    Nat.max (Nat.max (cofLb co) (valLb t)) (glueSysLb rest)
partial def valLb : Val → Nat
  | v => if lvlClosedByCache v then 0 else valLbGo v
partial def valLbGo : Val → Nat
  | .vuniv _ => 0
  | .vnat => 0
  | .vzero => 0
  | .vsucc _ n => valLb n
  | .vint => 0
  | .vipos _ n => valLb n
  | .vinegsuc _ n => valLb n
  | .vunit => 0
  | .vtt => 0
  | .vempty => 0
  | .vsum _ l r => Nat.max (valLb l) (valLb r)
  | .vinl _ t => valLb t
  | .vinr _ t => valLb t
  | .vsusp _ a => valLb a
  | .vnorth => 0
  | .vsouth => 0
  | .vmerid _ a r => Nat.max (valLb a) (r.levelBound)
  | .vpushout _ a b c f g => Nat.max (Nat.max (Nat.max (Nat.max (valLb a) (valLb b)) (valLb c)) (valLb f)) (valLb g)
  | .vpinl _ t => valLb t
  | .vpinr _ t => valLb t
  | .vppush _ f g c r => Nat.max (Nat.max (Nat.max (valLb f) (valLb g)) (valLb c)) (r.levelBound)
  | .vem1 _ car mul => Nat.max (valLb car) (valLb mul)
  | .vembase => 0
  | .vemloop _ g r => Nat.max (valLb g) (r.levelBound)
  | .vemcomp _ mul g h rj ri => Nat.max (Nat.max (Nat.max (Nat.max (valLb mul) (valLb g)) (valLb h)) (rj.levelBound)) (ri.levelBound)
  | .vemsquash _ x y p q u v r1 r2 r3 => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (valLb x) (valLb y)) (valLb p)) (valLb q)) (valLb u)) (valLb v)) (r1.levelBound)) (r2.levelBound)) (r3.levelBound)
  | .vbgpd _ ob hom cm => Nat.max (Nat.max (valLb ob) (valLb hom)) (valLb cm)
  | .vbpt _ t => valLb t
  | .vbarr _ x y f r => Nat.max (Nat.max (Nat.max (valLb x) (valLb y)) (valLb f)) r.levelBound
  | .vbcomp _ cm x y z f g rj ri => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (valLb cm) (valLb x)) (valLb y)) (valLb z)) (Nat.max (valLb f) (valLb g))) rj.levelBound) ri.levelBound
  | .vbsquash _ x y p q u v r1 r2 r3 => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (valLb x) (valLb y)) (valLb p)) (valLb q)) (valLb u)) (valLb v)) (r1.levelBound)) (r2.levelBound)) (r3.levelBound)
  | .vlist _ a => valLb a
  | .vlnil => 0
  | .vlcons _ h t => Nat.max (valLb h) (valLb t)
  | .vquot _ a r => Nat.max (valLb a) (valLb r)
  | .vqin _ t => valLb t
  | .vqeq _ a b w r => Nat.max (Nat.max (Nat.max (valLb a) (valLb b)) (valLb w)) (r.levelBound)
  | .vqsquash _ x y p q r s => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (valLb x) (valLb y)) (valLb p)) (valLb q)) (r.levelBound)) (s.levelBound)
  | .vtrunc _ a => valLb a
  | .vtin _ t => valLb t
  | .vsquash _ x y r => Nat.max (Nat.max (valLb x) (valLb y)) (r.levelBound)
  | .vtorus => 0
  | .vtbase => 0
  | .vtloopP r => r.levelBound
  | .vtloopQ r => r.levelBound
  | .vtsurf r s => Nat.max (r.levelBound) (s.levelBound)
  | .vs1 => 0
  | .vsbase => 0
  | .vsloop r => r.levelBound
  | .vpi _ dom cod => Nat.max (valLb dom) (closureLb cod)
  | .vlam _ body => closureLb body
  | .vsigma _ dom cod => Nat.max (valLb dom) (closureLb cod)
  | .vpair _ a b => Nat.max (valLb a) (valLb b)
  | .vpathP _ fam lhs rhs => Nat.max (Nat.max (closureLb fam) (valLb lhs)) (valLb rhs)
  | .vplam _ body => closureLb body
  | .vi r => r.levelBound
  | .vglueTy _ sys base => Nat.max (glueTySysLb sys) (valLb base)
  | .vglue _ ty sys base => Nat.max (Nat.max (valLb ty) (glueSysLb sys)) (valLb base)
  | .vne lb _ => lb
partial def neLb : Neutral → Nat
  | .var l => l + 1
  | .app fn arg => Nat.max (neLb fn) (valLb arg)
  | .fst p => neLb p
  | .snd p => neLb p
  | .natrec motive z s n => Nat.max (Nat.max (Nat.max (closureLb motive) (valLb z)) (valLb s)) (neLb n)
  | .papp p lhs rhs r => Nat.max (Nat.max (Nat.max (neLb p) (valLb lhs)) (valLb rhs)) (r.levelBound)
  | .transp fam a => Nat.max (closureLb fam) (valLb a)
  | .hcomp ty sys u₀ => Nat.max (Nat.max (valLb ty) (sysLb sys)) (valLb u₀)
  | .unglue ty b => Nat.max (valLb ty) (neLb b)
  | .s1elim motive b l t => Nat.max (Nat.max (Nat.max (closureLb motive) (valLb b)) (valLb l)) (neLb t)
  | .intcase motive fpos fneg t => Nat.max (Nat.max (Nat.max (closureLb motive) (valLb fpos)) (valLb fneg)) (neLb t)
  | .unitrec motive ptt t => Nat.max (Nat.max (closureLb motive) (valLb ptt)) (neLb t)
  | .emptyrec ty t => Nat.max (valLb ty) (neLb t)
  | .sumcase motive fl fr t => Nat.max (Nat.max (Nat.max (closureLb motive) (valLb fl)) (valLb fr)) (neLb t)
  | .susprec motive nc sc mc t => Nat.max (Nat.max (Nat.max (Nat.max (closureLb motive) (valLb nc)) (valLb sc)) (valLb mc)) (neLb t)
  | .torusrec motive bc pc qc sc t => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (closureLb motive) (valLb bc)) (valLb pc)) (valLb qc)) (valLb sc)) (neLb t)
  | .truncrec mB prp f t => Nat.max (Nat.max (Nat.max (valLb mB) (valLb prp)) (valLb f)) (neLb t)
  | .pushrec motive lc rc pc t => Nat.max (Nat.max (Nat.max (Nat.max (closureLb motive) (valLb lc)) (valLb rc)) (valLb pc)) (neLb t)
  | .listrec motive nc cc t => Nat.max (Nat.max (Nat.max (closureLb motive) (valLb nc)) (valLb cc)) (neLb t)
  | .em1rec B gB b l c t => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (valLb B) (valLb gB)) (valLb b)) (valLb l)) (valLb c)) (neLb t)
  | .em1elim motive gP b l c t => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (closureLb motive) (valLb gP)) (valLb b)) (valLb l)) (valLb c)) (neLb t)
  | .bgrec bT gB pf pl pc t => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (valLb bT) (valLb gB)) (valLb pf)) (valLb pl)) (valLb pc)) (neLb t)
  | .bgelim m gP pb pl pc t => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (closureLb m) (valLb gP)) (valLb pb)) (valLb pl)) (valLb pc)) (neLb t)
  | .emsquashCell x y p q u v r1 r2 r3 => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (valLb x) (valLb y)) (valLb p)) (valLb q)) (valLb u)) (valLb v)) (r1.levelBound)) (r2.levelBound)) (r3.levelBound)
  | .qelim motive mset f feq t => Nat.max (Nat.max (Nat.max (Nat.max (closureLb motive) (valLb mset)) (valLb f)) (valLb feq)) (neLb t)
  | .qsquashCell x y p q r s => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (valLb x) (valLb y)) (valLb p)) (valLb q)) (r.levelBound)) (s.levelBound)
partial def envLb : List Val → Nat
  | [] => 0
  | v :: rest => Nat.max (valLb v) (envLb rest)
partial def closureLb : Closure → Nat
  | .mk _ env _ => envLb env
  | .reparam _ _ => sentinelLb
  | .constV v => valLb v
  | .comp outer inner => Nat.max (closureLb outer) (closureLb inner)
  | .piDomOf c => closureLb c
  | .sigDomOf c => closureLb c
  | .transpPi fam f => Nat.max (closureLb fam) (valLb f)
  | .transpPiCod fam x₁ => Nat.max (closureLb fam) (valLb x₁)
  | .transpSigSnd fam u => Nat.max (closureLb fam) (valLb u)
  | .transpPathP fam p => Nat.max (closureLb fam) (valLb p)
  | .pathPLine fam j => Nat.max (closureLb fam) (j.levelBound)
  | .pathPEnd fam _ => closureLb fam
  | .mapApp br x => Nat.max (closureLb br) (valLb x)
  | .mapFst br => closureLb br
  | .mapSnd br => closureLb br
  | .mapPApp br lhs rhs j => Nat.max (Nat.max (Nat.max (closureLb br) (valLb lhs)) (valLb rhs)) (j.levelBound)
  | .natPred br => closureLb br
  | .hcompPi cod sys u₀ => Nat.max (Nat.max (closureLb cod) (sysLb sys)) (valLb u₀)
  | .hcompPathP fam lhs rhs sys u₀ => Nat.max (Nat.max (Nat.max (Nat.max (closureLb fam) (valLb lhs)) (valLb rhs)) (sysLb sys)) (valLb u₀)
  | .hfill ty sys u₀ => Nat.max (Nat.max (valLb ty) (sysLb sys)) (valLb u₀)
  | .compTube line br => Nat.max (closureLb line) (closureLb br)
  | .glueBase fam => closureLb fam
  | .glueBranchT fam _ => closureLb fam
  | .glueBranchW fam _ => closureLb fam
  | .glueDeltaTube fam _ u₀ => Nat.max (closureLb fam) (valLb u₀)
  | .fiberCod f A a => Nat.max (Nat.max (valLb f) (valLb A)) (valLb a)
  | .pappLine p lhs rhs => Nat.max (Nat.max (valLb p) (valLb lhs)) (valLb rhs)
  | .s1loopFam motive => closureLb motive
  | .s1elimTube motive b l br => Nat.max (Nat.max (Nat.max (closureLb motive) (valLb b)) (valLb l)) (closureLb br)
  | .iposArg br => closureLb br
  | .inegsucArg br => closureLb br
  | .inlArg br => closureLb br
  | .inrArg br => closureLb br
  | .natrecS motive => closureLb motive
  | .natrecS2 motive k => Nat.max (closureLb motive) (valLb k)
  | .intcasePos motive => closureLb motive
  | .intcaseNeg motive => closureLb motive
  | .sumcaseL motive => closureLb motive
  | .sumcaseR motive => closureLb motive
  | .sumLeftOf c => closureLb c
  | .sumRightOf c => closureLb c
  | .suspMcCod motive nc sc => Nat.max (Nat.max (closureLb motive) (valLb nc)) (valLb sc)
  | .suspMeridFam motive a => Nat.max (closureLb motive) (valLb a)
  | .suspLineOf c => closureLb c
  | .susprecTube motive nc sc mc br => Nat.max (Nat.max (Nat.max (Nat.max (closureLb motive) (valLb nc)) (valLb sc)) (valLb mc)) (closureLb br)
  | .torusLoopPFam motive => closureLb motive
  | .torusLoopQFam motive => closureLb motive
  | .torusSurfFam motive bc pc => Nat.max (Nat.max (closureLb motive) (valLb bc)) (valLb pc)
  | .torusSurfInner motive ri => Nat.max (closureLb motive) (ri.levelBound)
  | .torusrecTube motive bc pc qc sc br => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (closureLb motive) (valLb bc)) (valLb pc)) (valLb qc)) (valLb sc)) (closureLb br)
  | .pushLcCod motive => closureLb motive
  | .pushRcCod motive => closureLb motive
  | .pushPcCod motive lc rc f g => Nat.max (Nat.max (Nat.max (Nat.max (closureLb motive) (valLb lc)) (valLb rc)) (valLb f)) (valLb g)
  | .pushPcFam motive f g c => Nat.max (Nat.max (Nat.max (closureLb motive) (valLb f)) (valLb g)) (valLb c)
  | .pushAOf c => closureLb c
  | .pushBOf c => closureLb c
  | .pushCOf c => closureLb c
  | .pushrecTube motive lc rc pc br => Nat.max (Nat.max (Nat.max (Nat.max (closureLb motive) (valLb lc)) (valLb rc)) (valLb pc)) (closureLb br)
  | .em1recCCod B C mul l b => Nat.max (Nat.max (Nat.max (Nat.max (valLb B) (valLb C)) (valLb mul)) (valLb l)) (valLb b)
  | .em1recCCod2 B mul l b g => Nat.max (Nat.max (Nat.max (Nat.max (valLb B) (valLb mul)) (valLb l)) (valLb b)) (valLb g)
  | .em1recCFam B l b h => Nat.max (Nat.max (Nat.max (valLb B) (valLb l)) (valLb b)) (valLb h)
  | .em1elimLCod motive b => Nat.max (closureLb motive) (valLb b)
  | .em1elimLFam motive g => Nat.max (closureLb motive) (valLb g)
  | .em1elimDCCod motive C mul l b => Nat.max (Nat.max (Nat.max (Nat.max (closureLb motive) (valLb C)) (valLb mul)) (valLb l)) (valLb b)
  | .em1elimDCCod2 motive mul l b g => Nat.max (Nat.max (Nat.max (Nat.max (closureLb motive) (valLb mul)) (valLb l)) (valLb b)) (valLb g)
  | .em1elimDCFam motive mul l b g h => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (closureLb motive) (valLb mul)) (valLb l)) (valLb b)) (valLb g)) (valLb h)
  | .em1elimDCInner motive mul g h rj => Nat.max (Nat.max (Nat.max (Nat.max (closureLb motive) (valLb mul)) (valLb g)) (valLb h)) (rj.levelBound)
  | .em1elimGCod motive => closureLb motive
  | .em1elimTube motive gP b l c br => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (closureLb motive) (valLb gP)) (valLb b)) (valLb l)) (valLb c)) (closureLb br)
  | .em1CarOf c => closureLb c
  | .em1recTube B gB b l c br => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (valLb B) (valLb gB)) (valLb b)) (valLb l)) (valLb c)) (closureLb br)
  | .bgrecTube bT gB pf pl pc br => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (valLb bT) (valLb gB)) (valLb pf)) (valLb pl)) (valLb pc)) (closureLb br)
  | .bgelimTube m gP pb pl pc br => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max (closureLb m) (valLb gP)) (valLb pb)) (valLb pl)) (valLb pc)) (closureLb br)
  | .listCcCod motive A => Nat.max (closureLb motive) (valLb A)
  | .listCcCod2 motive h => Nat.max (closureLb motive) (valLb h)
  | .listArgOf c => closureLb c
  | .lheadArg br => closureLb br
  | .ltailArg br => closureLb br
  | .listrecTube motive nc cc br => Nat.max (Nat.max (Nat.max (closureLb motive) (valLb nc)) (valLb cc)) (closureLb br)
  | .qelimInCod motive => closureLb motive
  | .qelimEqCod motive A rel f => Nat.max (Nat.max (Nat.max (closureLb motive) (valLb A)) (valLb rel)) (valLb f)
  | .qelimEqCod2 motive rel f a => Nat.max (Nat.max (Nat.max (closureLb motive) (valLb rel)) (valLb f)) (valLb a)
  | .qelimEqCod3 motive f a b => Nat.max (Nat.max (Nat.max (closureLb motive) (valLb f)) (valLb a)) (valLb b)
  | .qelimEqFam motive a b w => Nat.max (Nat.max (Nat.max (closureLb motive) (valLb a)) (valLb b)) (valLb w)
  | .qelimSetCod motive => closureLb motive
  | .isSetOf1 T => valLb T
  | .isSetOf2 T u => Nat.max (valLb T) (valLb u)
  | .isSetOf3 T u v => Nat.max (Nat.max (valLb T) (valLb u)) (valLb v)
  | .isSetOf4 T u v p => Nat.max (Nat.max (Nat.max (valLb T) (valLb u)) (valLb v)) (valLb p)
  | .quotAOf c => closureLb c
  | .qelimTube motive mset f feq br => Nat.max (Nat.max (Nat.max (Nat.max (closureLb motive) (valLb mset)) (valLb f)) (valLb feq)) (closureLb br)
  | .truncArgOf c => closureLb c
  | .truncrecTube mB prp f br => Nat.max (Nat.max (Nat.max (valLb mB) (valLb prp)) (valLb f)) (closureLb br)
end

/-- Native-only bound computation: the elaborator's interpreter (where
`implemented_by` on the cache flags is inert) would otherwise walk huge
witness graphs at every neutral construction.  The pure model stores the
sentinel — sound (the `usesLvl` shortcut just never fires there, i.e.
exactly the pre-refactor interpreter behaviour); compiled code computes
the real bound, with the `lvlClosedByCache` O(1) cut on shared defn
witnesses. -/
unsafe def neLbHookUnsafe (n : Neutral) : Nat :=
  unsafeBaseIO do
    -- Gated like every other native mechanism: precompiled build-time
    -- guards run THIS code with the flag off (cheap sentinel = exact
    -- pre-refactor behaviour); runners opt in via `defnCacheEnable`,
    -- which also arms the `lvlClosedByCache` O(1) witness cuts that
    -- keep the bound computation shallow.
    if (← defnCacheEnabledRef.get) then pure (neLb n) else pure sentinelLb
@[never_extract, implemented_by neLbHookUnsafe]
def neLbHook (_n : Neutral) : Nat := sentinelLb

/-- O(1) level bound of a value: the stored stamp for stamped
constructors, `0` for closed atoms, the generation fallback `fresh + 1`
otherwise (sound: any value built at depth `fresh` has free levels
`≤ fresh`).  Reading children through this makes freshly-rebuilt
wrappers around old content inherit *tight* bounds, so the constancy
cut fires even on conv-driven re-evaluations. -/
def quickLb (fresh : Nat) : Val → Nat
  | .vne lb _ | .vpi lb _ _ | .vlam lb _ | .vsigma lb _ _
  | .vpair lb _ _ | .vpathP lb _ _ _ | .vplam lb _
  | .vglueTy lb _ _ | .vglue lb _ _ _
  | .vsucc lb _ | .vipos lb _ | .vinegsuc lb _ | .vinl lb _ | .vinr lb _
  | .vlcons lb _ _ | .vtin lb _ | .vqin lb _ | .vsusp lb _
  | .vpinl lb _ | .vpinr lb _
  | .vsum lb _ _ | .vlist lb _ | .vquot lb _ _ | .vtrunc lb _
  | .vem1 lb _ _ | .vmerid lb _ _ | .vppush lb _ _ _ _
  | .vemloop lb _ _ | .vemcomp lb _ _ _ _ _
  | .vemsquash lb _ _ _ _ _ _ _ _ _ | .vqeq lb _ _ _ _
  | .vbgpd lb _ _ _ | .vbpt lb _ | .vbarr lb _ _ _ _
  | .vbcomp lb _ _ _ _ _ _ _ _ | .vbsquash lb _ _ _ _ _ _ _ _ _
  | .vqsquash lb _ _ _ _ _ _ | .vsquash lb _ _ _
  | .vpushout lb _ _ _ _ _ => lb
  | .vsloop r => r.levelBound
  | .vtloopP r | .vtloopQ r => r.levelBound
  | .vtsurf r s2 => Nat.max r.levelBound s2.levelBound
  | .vuniv _ | .vnat | .vzero | .vint | .vunit | .vtt | .vempty
  | .vs1 | .vsbase | .vnorth | .vsouth | .vtorus | .vtbase | .vlnil
  | .vembase => 0
  | .vi r => r.levelBound

def cofQuickLb : VCof → Nat
  | [] => 0
  | (r, _) :: rest => Nat.max r.levelBound (cofQuickLb rest)

mutual
/-- O(1)-per-node level bound of a closure: stored stamp for `.mk`,
tight children-max for every derived form (fields are Closures, Vals —
which read their stored stamps in O(1) — intervals, and systems); only
`reparam` (opaque interval function) falls back to the generation bound.
Recursion depth = derived-closure nesting, which the Kan operations keep
shallow except along `comp`/tube chains. -/
partial def quickLbC (fresh : Nat) : Closure → Nat
  | .mk lb _ _ => lb
  | .constV v => quickLb fresh v
  | .comp outer inner => Nat.max (quickLbC fresh outer) (quickLbC fresh inner)
  | .piDomOf c => (quickLbC fresh c)
  | .sigDomOf c => (quickLbC fresh c)
  | .transpPi fam f => Nat.max (quickLbC fresh fam) (quickLb fresh f)
  | .transpPiCod fam x₁ => Nat.max (quickLbC fresh fam) (quickLb fresh x₁)
  | .transpSigSnd fam u => Nat.max (quickLbC fresh fam) (quickLb fresh u)
  | .transpPathP fam p => Nat.max (quickLbC fresh fam) (quickLb fresh p)
  | .pathPLine fam j => Nat.max (quickLbC fresh fam) j.levelBound
  | .pathPEnd fam _ => (quickLbC fresh fam)
  | .mapApp br x => Nat.max (quickLbC fresh br) (quickLb fresh x)
  | .mapFst br => (quickLbC fresh br)
  | .mapSnd br => (quickLbC fresh br)
  | .mapPApp br lhs rhs j => Nat.max (Nat.max (Nat.max ((quickLbC fresh br)) ((quickLb fresh lhs))) ((quickLb fresh rhs))) (j.levelBound)
  | .natPred br => (quickLbC fresh br)
  | .hcompPi cod sys u₀ => Nat.max (Nat.max ((quickLbC fresh cod)) ((sysQuickLb fresh sys))) ((quickLb fresh u₀))
  | .hcompPathP fam lhs rhs sys u₀ => Nat.max (Nat.max (Nat.max (Nat.max ((quickLbC fresh fam)) ((quickLb fresh lhs))) ((quickLb fresh rhs))) ((sysQuickLb fresh sys))) ((quickLb fresh u₀))
  | .hfill ty sys u₀ => Nat.max (Nat.max ((quickLb fresh ty)) ((sysQuickLb fresh sys))) ((quickLb fresh u₀))
  | .compTube line br => Nat.max (quickLbC fresh line) (quickLbC fresh br)
  | .glueBase fam => (quickLbC fresh fam)
  | .glueBranchT fam _ => (quickLbC fresh fam)
  | .glueBranchW fam _ => (quickLbC fresh fam)
  | .glueDeltaTube fam _ u₀ => Nat.max (quickLbC fresh fam) (quickLb fresh u₀)
  | .fiberCod f A a => Nat.max (Nat.max ((quickLb fresh f)) ((quickLb fresh A))) ((quickLb fresh a))
  | .pappLine p lhs rhs => Nat.max (Nat.max ((quickLb fresh p)) ((quickLb fresh lhs))) ((quickLb fresh rhs))
  | .s1loopFam motive => (quickLbC fresh motive)
  | .s1elimTube motive b l br => Nat.max (Nat.max (Nat.max ((quickLbC fresh motive)) ((quickLb fresh b))) ((quickLb fresh l))) ((quickLbC fresh br))
  | .iposArg br => (quickLbC fresh br)
  | .inegsucArg br => (quickLbC fresh br)
  | .inlArg br => (quickLbC fresh br)
  | .inrArg br => (quickLbC fresh br)
  | .natrecS motive => (quickLbC fresh motive)
  | .natrecS2 motive k => Nat.max (quickLbC fresh motive) (quickLb fresh k)
  | .intcasePos motive => (quickLbC fresh motive)
  | .intcaseNeg motive => (quickLbC fresh motive)
  | .sumcaseL motive => (quickLbC fresh motive)
  | .sumcaseR motive => (quickLbC fresh motive)
  | .sumLeftOf c => (quickLbC fresh c)
  | .suspMcCod motive nc sc => Nat.max (Nat.max ((quickLbC fresh motive)) ((quickLb fresh nc))) ((quickLb fresh sc))
  | .suspMeridFam motive a => Nat.max (quickLbC fresh motive) (quickLb fresh a)
  | .suspLineOf c => (quickLbC fresh c)
  | .susprecTube motive nc sc mc br => Nat.max (Nat.max (Nat.max (Nat.max ((quickLbC fresh motive)) ((quickLb fresh nc))) ((quickLb fresh sc))) ((quickLb fresh mc))) ((quickLbC fresh br))
  | .torusLoopPFam motive => (quickLbC fresh motive)
  | .torusSurfFam motive bc pc => Nat.max (Nat.max ((quickLbC fresh motive)) ((quickLb fresh bc))) ((quickLb fresh pc))
  | .torusSurfInner motive ri => Nat.max (quickLbC fresh motive) ri.levelBound
  | .torusrecTube motive bc pc qc sc br => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max ((quickLbC fresh motive)) ((quickLb fresh bc))) ((quickLb fresh pc))) ((quickLb fresh qc))) ((quickLb fresh sc))) ((quickLbC fresh br))
  | .pushLcCod motive => (quickLbC fresh motive)
  | .pushPcCod motive lc rc f g => Nat.max (Nat.max (Nat.max (Nat.max ((quickLbC fresh motive)) ((quickLb fresh lc))) ((quickLb fresh rc))) ((quickLb fresh f))) ((quickLb fresh g))
  | .pushPcFam motive f g c => Nat.max (Nat.max (Nat.max ((quickLbC fresh motive)) ((quickLb fresh f))) ((quickLb fresh g))) ((quickLb fresh c))
  | .pushAOf c => (quickLbC fresh c)
  | .pushBOf c => (quickLbC fresh c)
  | .pushCOf c => (quickLbC fresh c)
  | .em1recCCod B C mul l b => Nat.max (Nat.max (Nat.max (Nat.max ((quickLb fresh B)) ((quickLb fresh C))) ((quickLb fresh mul))) ((quickLb fresh l))) ((quickLb fresh b))
  | .em1recCCod2 B mul l b g => Nat.max (Nat.max (Nat.max (Nat.max ((quickLb fresh B)) ((quickLb fresh mul))) ((quickLb fresh l))) ((quickLb fresh b))) ((quickLb fresh g))
  | .em1recCFam B l b h => Nat.max (Nat.max (Nat.max ((quickLb fresh B)) ((quickLb fresh l))) ((quickLb fresh b))) ((quickLb fresh h))
  | .em1elimLCod motive b => Nat.max (quickLbC fresh motive) (quickLb fresh b)
  | .em1elimLFam motive g => Nat.max (quickLbC fresh motive) (quickLb fresh g)
  | .em1elimDCCod motive C mul l b => Nat.max (Nat.max (Nat.max (Nat.max ((quickLbC fresh motive)) ((quickLb fresh C))) ((quickLb fresh mul))) ((quickLb fresh l))) ((quickLb fresh b))
  | .em1elimDCCod2 motive mul l b g => Nat.max (Nat.max (Nat.max (Nat.max ((quickLbC fresh motive)) ((quickLb fresh mul))) ((quickLb fresh l))) ((quickLb fresh b))) ((quickLb fresh g))
  | .em1elimDCFam motive mul l b g h => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max ((quickLbC fresh motive)) ((quickLb fresh mul))) ((quickLb fresh l))) ((quickLb fresh b))) ((quickLb fresh g))) ((quickLb fresh h))
  | .em1elimDCInner motive mul g h rj => Nat.max (Nat.max (Nat.max (Nat.max ((quickLbC fresh motive)) ((quickLb fresh mul))) ((quickLb fresh g))) ((quickLb fresh h))) (rj.levelBound)
  | .em1elimGCod motive => (quickLbC fresh motive)
  | .em1elimTube motive gP b l c br => Nat.max (Nat.max (Nat.max (Nat.max (Nat.max ((quickLbC fresh motive)) ((quickLb fresh gP))) ((quickLb fresh b))) ((quickLb fresh l))) ((quickLb fresh c))) ((quickLbC fresh br))
  | .em1CarOf c => (quickLbC fresh c)
  | .listCcCod motive A => Nat.max (quickLbC fresh motive) (quickLb fresh A)
  | .listCcCod2 motive h => Nat.max (quickLbC fresh motive) (quickLb fresh h)
  | .listArgOf c => (quickLbC fresh c)
  | .lheadArg br => (quickLbC fresh br)
  | .ltailArg br => (quickLbC fresh br)
  | .listrecTube motive nc cc br => Nat.max (Nat.max (Nat.max ((quickLbC fresh motive)) ((quickLb fresh nc))) ((quickLb fresh cc))) ((quickLbC fresh br))
  | .qelimEqCod motive A rel f => Nat.max (Nat.max (Nat.max ((quickLbC fresh motive)) ((quickLb fresh A))) ((quickLb fresh rel))) ((quickLb fresh f))
  | .qelimEqCod2 motive rel f a => Nat.max (Nat.max (Nat.max ((quickLbC fresh motive)) ((quickLb fresh rel))) ((quickLb fresh f))) ((quickLb fresh a))
  | .qelimEqCod3 motive f a b => Nat.max (Nat.max (Nat.max ((quickLbC fresh motive)) ((quickLb fresh f))) ((quickLb fresh a))) ((quickLb fresh b))
  | .qelimEqFam motive a b w => Nat.max (Nat.max (Nat.max ((quickLbC fresh motive)) ((quickLb fresh a))) ((quickLb fresh b))) ((quickLb fresh w))
  | .qelimSetCod motive => (quickLbC fresh motive)
  | .isSetOf1 T => (quickLb fresh T)
  | .isSetOf2 T u => Nat.max (quickLb fresh T) (quickLb fresh u)
  | .isSetOf3 T u v => Nat.max (Nat.max ((quickLb fresh T)) ((quickLb fresh u))) ((quickLb fresh v))
  | .isSetOf4 T u v p => Nat.max (Nat.max (Nat.max ((quickLb fresh T)) ((quickLb fresh u))) ((quickLb fresh v))) ((quickLb fresh p))
  | .quotAOf c => (quickLbC fresh c)
  | .qelimTube motive mset f feq br => Nat.max (Nat.max (Nat.max (Nat.max ((quickLbC fresh motive)) ((quickLb fresh mset))) ((quickLb fresh f))) ((quickLb fresh feq))) ((quickLbC fresh br))
  | .truncArgOf c => (quickLbC fresh c)
  | .truncrecTube mB prp f br => Nat.max (Nat.max (Nat.max ((quickLb fresh mB)) ((quickLb fresh prp))) ((quickLb fresh f))) ((quickLbC fresh br))
  | .reparam _ _ => fresh + 1  -- unparsed/opaque field
  | .sumRightOf c => quickLbC fresh c
  | .torusLoopQFam motive => quickLbC fresh motive
  | .pushRcCod motive => quickLbC fresh motive
  | .pushrecTube motive lc rc pc br =>
    Nat.max (Nat.max (quickLbC fresh motive) (quickLb fresh lc))
      (Nat.max (Nat.max (quickLb fresh rc) (quickLb fresh pc))
        (quickLbC fresh br))
  | .em1recTube B gB b l c br =>
    Nat.max (Nat.max (Nat.max (quickLb fresh B) (quickLb fresh gB))
        (Nat.max (quickLb fresh b) (quickLb fresh l)))
      (Nat.max (quickLb fresh c) (quickLbC fresh br))
  | .bgrecTube bT gB pf pl pc br =>
    Nat.max (Nat.max (Nat.max (quickLb fresh bT) (quickLb fresh gB))
        (Nat.max (quickLb fresh pf) (quickLb fresh pl)))
      (Nat.max (quickLb fresh pc) (quickLbC fresh br))
  | .bgelimTube m gP pb pl pc br =>
    Nat.max (Nat.max (Nat.max (quickLbC fresh m) (quickLb fresh gP))
        (Nat.max (quickLb fresh pb) (quickLb fresh pl)))
      (Nat.max (quickLb fresh pc) (quickLbC fresh br))
  | .qelimInCod motive => quickLbC fresh motive

partial def envQuickLb (fresh : Nat) : List Val → Nat
  | [] => 0
  | v :: rest => Nat.max (quickLb fresh v) (envQuickLb fresh rest)

partial def sysQuickLb (fresh : Nat) : List (VCof × Closure) → Nat
  | [] => 0
  | (co, br) :: rest =>
    Nat.max (Nat.max (cofQuickLb co) (quickLbC fresh br))
      (sysQuickLb fresh rest)
end

/-- Shallow tight bound of a neutral: fields via the O(1) `quickLb`
readers, recursion only along the (short) eliminator spine — `hcomp`
towers live at the `Val` layer where the stored stamps cut them off. -/
def neQuickLb (fresh : Nat) : Neutral → Nat
  | .var l => l + 1
  | .app fn arg => Nat.max (neQuickLb fresh fn) (quickLb fresh arg)
  | .fst p => neQuickLb fresh p
  | .snd p => neQuickLb fresh p
  | .natrec m z s n =>
    Nat.max (Nat.max (quickLbC fresh m) (quickLb fresh z))
      (Nat.max (quickLb fresh s) (neQuickLb fresh n))
  | .papp p lhs rhs r =>
    Nat.max (Nat.max (neQuickLb fresh p) (quickLb fresh lhs))
      (Nat.max (quickLb fresh rhs) r.levelBound)
  | .transp fam a => Nat.max (quickLbC fresh fam) (quickLb fresh a)
  | .hcomp ty sys u₀ =>
    Nat.max (Nat.max (quickLb fresh ty) (sysQuickLb fresh sys))
      (quickLb fresh u₀)
  | .unglue ty b => Nat.max (quickLb fresh ty) (neQuickLb fresh b)
  | .s1elim m b l t =>
    Nat.max (Nat.max (quickLbC fresh m) (quickLb fresh b))
      (Nat.max (quickLb fresh l) (neQuickLb fresh t))
  | .intcase m fp fn t =>
    Nat.max (Nat.max (quickLbC fresh m) (quickLb fresh fp))
      (Nat.max (quickLb fresh fn) (neQuickLb fresh t))
  | .unitrec m p t =>
    Nat.max (quickLbC fresh m)
      (Nat.max (quickLb fresh p) (neQuickLb fresh t))
  | .emptyrec ty t => Nat.max (quickLb fresh ty) (neQuickLb fresh t)
  | .sumcase m fl fr t =>
    Nat.max (Nat.max (quickLbC fresh m) (quickLb fresh fl))
      (Nat.max (quickLb fresh fr) (neQuickLb fresh t))
  | .susprec m nc sc mc t =>
    Nat.max (Nat.max (quickLbC fresh m) (quickLb fresh nc))
      (Nat.max (Nat.max (quickLb fresh sc) (quickLb fresh mc))
        (neQuickLb fresh t))
  | .torusrec m bc pc qc sc t =>
    Nat.max (Nat.max (quickLbC fresh m) (quickLb fresh bc))
      (Nat.max (Nat.max (quickLb fresh pc) (quickLb fresh qc))
        (Nat.max (quickLb fresh sc) (neQuickLb fresh t)))
  | .truncrec mB prp f t =>
    Nat.max (Nat.max (quickLb fresh mB) (quickLb fresh prp))
      (Nat.max (quickLb fresh f) (neQuickLb fresh t))
  | .pushrec m lc rc pc t =>
    Nat.max (Nat.max (quickLbC fresh m) (quickLb fresh lc))
      (Nat.max (Nat.max (quickLb fresh rc) (quickLb fresh pc))
        (neQuickLb fresh t))
  | .listrec m nc cc t =>
    Nat.max (Nat.max (quickLbC fresh m) (quickLb fresh nc))
      (Nat.max (quickLb fresh cc) (neQuickLb fresh t))
  | .em1rec B gB b l c t =>
    Nat.max (Nat.max (Nat.max (quickLb fresh B) (quickLb fresh gB))
        (Nat.max (quickLb fresh b) (quickLb fresh l)))
      (Nat.max (quickLb fresh c) (neQuickLb fresh t))
  | .em1elim m gP b l c t =>
    Nat.max (Nat.max (Nat.max (quickLbC fresh m) (quickLb fresh gP))
        (Nat.max (quickLb fresh b) (quickLb fresh l)))
      (Nat.max (quickLb fresh c) (neQuickLb fresh t))
  | .bgrec bT gB pf pl pc t =>
    Nat.max (Nat.max (Nat.max (quickLb fresh bT) (quickLb fresh gB))
        (Nat.max (quickLb fresh pf) (quickLb fresh pl)))
      (Nat.max (quickLb fresh pc) (neQuickLb fresh t))
  | .bgelim m gP pb pl pc t =>
    Nat.max (Nat.max (Nat.max (quickLbC fresh m) (quickLb fresh gP))
        (Nat.max (quickLb fresh pb) (quickLb fresh pl)))
      (Nat.max (quickLb fresh pc) (neQuickLb fresh t))
  | .emsquashCell x y p q u v r1 r2 r3 =>
    Nat.max (Nat.max (Nat.max (quickLb fresh x) (quickLb fresh y))
        (Nat.max (quickLb fresh p) (quickLb fresh q)))
      (Nat.max (Nat.max (quickLb fresh u) (quickLb fresh v))
        (Nat.max r1.levelBound (Nat.max r2.levelBound r3.levelBound)))
  | .qelim m mset f feq t =>
    Nat.max (Nat.max (quickLbC fresh m) (quickLb fresh mset))
      (Nat.max (Nat.max (quickLb fresh f) (quickLb fresh feq))
        (neQuickLb fresh t))
  | .qsquashCell x y p q r s =>
    Nat.max (Nat.max (Nat.max (quickLb fresh x) (quickLb fresh y))
        (Nat.max (quickLb fresh p) (quickLb fresh q)))
      (Nat.max r.levelBound s.levelBound)

def vneAt (fresh : Nat) (n : Neutral) : Val :=
  Val.vne (neQuickLb fresh n) n
def vsuccAt (fresh : Nat) (n : Val) : Val := .vsucc (quickLb fresh n) n
def viposAt (fresh : Nat) (n : Val) : Val := .vipos (quickLb fresh n) n
def vinegsucAt (fresh : Nat) (n : Val) : Val :=
  .vinegsuc (quickLb fresh n) n
def vinlAt (fresh : Nat) (t : Val) : Val := .vinl (quickLb fresh t) t
def vinrAt (fresh : Nat) (t : Val) : Val := .vinr (quickLb fresh t) t
def vlconsAt (fresh : Nat) (h t : Val) : Val :=
  .vlcons (Nat.max (quickLb fresh h) (quickLb fresh t)) h t
def vtinAt (fresh : Nat) (t : Val) : Val := .vtin (quickLb fresh t) t
def vqinAt (fresh : Nat) (t : Val) : Val := .vqin (quickLb fresh t) t
def vsuspAt (fresh : Nat) (a : Val) : Val := .vsusp (quickLb fresh a) a
def vpinlAt (fresh : Nat) (t : Val) : Val := .vpinl (quickLb fresh t) t
def vpinrAt (fresh : Nat) (t : Val) : Val := .vpinr (quickLb fresh t) t
def vsumAt (fresh : Nat) (l r : Val) : Val :=
  .vsum (Nat.max (quickLb fresh l) (quickLb fresh r)) l r
def vlistAt (fresh : Nat) (a : Val) : Val := .vlist (quickLb fresh a) a
def vquotAt (fresh : Nat) (a r : Val) : Val :=
  .vquot (Nat.max (quickLb fresh a) (quickLb fresh r)) a r
def vtruncAt (fresh : Nat) (a : Val) : Val := .vtrunc (quickLb fresh a) a
def vem1At (fresh : Nat) (car mul : Val) : Val :=
  .vem1 (Nat.max (quickLb fresh car) (quickLb fresh mul)) car mul
def vmeridAt (fresh : Nat) (a : Val) (r : IVal) : Val :=
  .vmerid (Nat.max (quickLb fresh a) r.levelBound) a r
def vppushAt (fresh : Nat) (f g c : Val) (r : IVal) : Val :=
  .vppush (Nat.max (Nat.max (quickLb fresh f) (quickLb fresh g))
    (Nat.max (quickLb fresh c) r.levelBound)) f g c r
def vemloopAt (fresh : Nat) (g : Val) (r : IVal) : Val :=
  .vemloop (Nat.max (quickLb fresh g) r.levelBound) g r
def vemcompAt (fresh : Nat) (mul g h : Val) (rj ri : IVal) : Val :=
  .vemcomp (Nat.max (Nat.max (quickLb fresh mul) (quickLb fresh g))
    (Nat.max (quickLb fresh h) (Nat.max rj.levelBound ri.levelBound)))
    mul g h rj ri
def vbgpdAt (fresh : Nat) (ob hom cm : Val) : Val :=
  .vbgpd (Nat.max (Nat.max (quickLb fresh ob) (quickLb fresh hom))
    (quickLb fresh cm)) ob hom cm
def vbptAt (fresh : Nat) (t : Val) : Val := .vbpt (quickLb fresh t) t
def vbarrAt (fresh : Nat) (x y f : Val) (r : IVal) : Val :=
  .vbarr (Nat.max (Nat.max (Nat.max (quickLb fresh x) (quickLb fresh y))
    (quickLb fresh f)) r.levelBound) x y f r
def vbcompAt (fresh : Nat) (cm x y z f g : Val) (rj ri : IVal) : Val :=
  .vbcomp (Nat.max (Nat.max
      (Nat.max (Nat.max (quickLb fresh cm) (quickLb fresh x))
        (Nat.max (quickLb fresh y) (quickLb fresh z)))
      (Nat.max (quickLb fresh f) (quickLb fresh g)))
    (Nat.max rj.levelBound ri.levelBound)) cm x y z f g rj ri
def vbsquashAt (fresh : Nat) (x y p q u v : Val) (r1 r2 r3 : IVal) : Val :=
  .vbsquash (Nat.max
    (Nat.max (Nat.max (quickLb fresh x) (quickLb fresh y))
      (Nat.max (quickLb fresh p) (quickLb fresh q)))
    (Nat.max (Nat.max (quickLb fresh u) (quickLb fresh v))
      (Nat.max r1.levelBound (Nat.max r2.levelBound r3.levelBound))))
    x y p q u v r1 r2 r3
def vemsquashAt (fresh : Nat) (x y p q u v : Val) (r1 r2 r3 : IVal) :
    Val :=
  .vemsquash (Nat.max
    (Nat.max (Nat.max (quickLb fresh x) (quickLb fresh y))
      (Nat.max (quickLb fresh p) (quickLb fresh q)))
    (Nat.max (Nat.max (quickLb fresh u) (quickLb fresh v))
      (Nat.max r1.levelBound (Nat.max r2.levelBound r3.levelBound))))
    x y p q u v r1 r2 r3
def vqeqAt (fresh : Nat) (a b w : Val) (r : IVal) : Val :=
  .vqeq (Nat.max (Nat.max (quickLb fresh a) (quickLb fresh b))
    (Nat.max (quickLb fresh w) r.levelBound)) a b w r
def vqsquashAt (fresh : Nat) (x y p q : Val) (r s2 : IVal) : Val :=
  .vqsquash (Nat.max
    (Nat.max (quickLb fresh x) (quickLb fresh y))
    (Nat.max (Nat.max (quickLb fresh p) (quickLb fresh q))
      (Nat.max r.levelBound s2.levelBound))) x y p q r s2
def vsquashAt (fresh : Nat) (x y : Val) (r : IVal) : Val :=
  .vsquash (Nat.max (Nat.max (quickLb fresh x) (quickLb fresh y))
    r.levelBound) x y r
def vpushoutAt (fresh : Nat) (a b c f g : Val) : Val :=
  .vpushout (Nat.max
    (Nat.max (Nat.max (quickLb fresh a) (quickLb fresh b))
      (quickLb fresh c))
    (Nat.max (quickLb fresh f) (quickLb fresh g))) a b c f g
def vpiAt (fresh : Nat) (d : Val) (c : Closure) : Val :=
  .vpi (Nat.max (quickLb fresh d) (quickLbC fresh c)) d c
def vlamAt (fresh : Nat) (c : Closure) : Val := .vlam (quickLbC fresh c) c
def vsigmaAt (fresh : Nat) (d : Val) (c : Closure) : Val :=
  .vsigma (Nat.max (quickLb fresh d) (quickLbC fresh c)) d c
def vpairAt (fresh : Nat) (a b : Val) : Val :=
  .vpair (Nat.max (quickLb fresh a) (quickLb fresh b)) a b
def vpathPAt (fresh : Nat) (f : Closure) (l r : Val) : Val :=
  .vpathP (Nat.max (Nat.max (quickLbC fresh f) (quickLb fresh l))
    (quickLb fresh r)) f l r
def vplamAt (fresh : Nat) (c : Closure) : Val := .vplam (quickLbC fresh c) c
def mkAt (fresh : Nat) (env : List Val) (b : Term) : Closure :=
  .mk (envQuickLb fresh env) env b
def glueTySysQuickLb (fresh : Nat) : List (VCof × Val × Val) → Nat
  | [] => 0
  | (co, T, e) :: rest =>
    Nat.max (Nat.max (cofQuickLb co)
      (Nat.max (quickLb fresh T) (quickLb fresh e)))
      (glueTySysQuickLb fresh rest)
def glueSysQuickLb (fresh : Nat) : List (VCof × Val) → Nat
  | [] => 0
  | (co, t) :: rest =>
    Nat.max (Nat.max (cofQuickLb co) (quickLb fresh t))
      (glueSysQuickLb fresh rest)
def vglueTyAt (fresh : Nat) (sys : List (VCof × Val × Val)) (base : Val) :
    Val :=
  .vglueTy (Nat.max (glueTySysQuickLb fresh sys) (quickLb fresh base))
    sys base
def vglueAt (fresh : Nat) (ty : Val) (sys : List (VCof × Val))
    (base : Val) : Val :=
  .vglue (Nat.max (quickLb fresh ty)
      (Nat.max (glueSysQuickLb fresh sys) (quickLb fresh base)))
    ty sys base

mutual

/-- Lazy face reduction: a `Glue` branch whose face holds identically
selects its type/term (identically false branches are discarded), the loop
constructor collapses to the base point at the interval endpoints, and an
`hcomp` HIT cell with an identically-true face selects its tube at `1`.
Applied at every site that inspects the head of a value.  Keeping these
reductions lazy preserves the structure the Kan operations need (e.g.
`helix (loop 0)` must stay a `Glue` for `transpGlue`, even though it is
convertible to `ℤ`). -/
partial def force (fresh : Nat) (v : Val) : Val :=
  if profTick 3 v then panic! "unreachable" else
  match v with
  | .vsloop r => if r.isZero || r.isOne then .vsbase else v
  | .vmerid _ _ r =>
    if r.isZero then .vnorth else if r.isOne then .vsouth else v
  | .vsquash _ x y r =>
    if r.isZero then force fresh x else if r.isOne then force fresh y else v
  | .vppush _ f g c r =>
    if r.isZero then vpinlAt fresh (vapp fresh f c)
    else if r.isOne then vpinrAt fresh (vapp fresh g c)
    else v
  | .vqeq _ a b _ r =>
    if r.isZero then vqinAt fresh a else if r.isOne then vqinAt fresh b else v
  | .vemloop _ _ r =>
    if r.isZero || r.isOne then .vembase else v
  | .vemcomp _ mul g h rj ri =>
    if ri.isZero then .vembase
    else if ri.isOne then force fresh (vemloopAt fresh h rj)
    else if rj.isZero then force fresh (vemloopAt fresh g ri)
    else if rj.isOne then
      force fresh (vemloopAt fresh (vapp fresh (vapp fresh mul g) h) ri)
    else v
  | .vemsquash _ x y p q u v2 r1 r2 r3 =>
    if r1.isZero then force fresh (vpapp fresh
      (vpapp fresh u p q r2) x y r3)
    else if r1.isOne then force fresh (vpapp fresh
      (vpapp fresh v2 p q r2) x y r3)
    else if r2.isZero then force fresh (vpapp fresh p x y r3)
    else if r2.isOne then force fresh (vpapp fresh q x y r3)
    else if r3.isZero then force fresh x
    else if r3.isOne then force fresh y
    else v
  | .vbarr _ x y _ r =>
    if r.isZero then force fresh (vbptAt fresh x)
    else if r.isOne then force fresh (vbptAt fresh y)
    else v
  | .vbcomp _ cm x y z f g rj ri =>
    if ri.isZero then force fresh (vbptAt fresh x)
    else if ri.isOne then force fresh (vbarrAt fresh y z g rj)
    else if rj.isZero then force fresh (vbarrAt fresh x y f ri)
    else if rj.isOne then
      force fresh (vbarrAt fresh x z
        (vapp fresh (vapp fresh (vapp fresh (vapp fresh
          (vapp fresh cm x) y) z) f) g) ri)
    else v
  | .vbsquash _ x y p q u v2 r1 r2 r3 =>
    if r1.isZero then force fresh (vpapp fresh
      (vpapp fresh u p q r2) x y r3)
    else if r1.isOne then force fresh (vpapp fresh
      (vpapp fresh v2 p q r2) x y r3)
    else if r2.isZero then force fresh (vpapp fresh p x y r3)
    else if r2.isOne then force fresh (vpapp fresh q x y r3)
    else if r3.isZero then force fresh x
    else if r3.isOne then force fresh y
    else v
  | .vqsquash _ x y p q r s =>
    if r.isZero then force fresh (vpapp fresh p x y s)
    else if r.isOne then force fresh (vpapp fresh q x y s)
    else if s.isZero then force fresh x
    else if s.isOne then force fresh y
    else v
  | .vtloopP r => if r.isZero || r.isOne then .vtbase else v
  | .vtloopQ r => if r.isZero || r.isOne then .vtbase else v
  | .vtsurf r s =>
    if r.isZero || r.isOne then force fresh (.vtloopQ s)
    else if s.isZero || s.isOne then force fresh (.vtloopP r)
    else v
  | .vglueTy lb sys base =>
    match sys.find? (fun (c, _, _) => cofStatus c == .isTrue) with
    | some (_, T, _) => force fresh T
    | none =>
      .vglueTy lb (sys.filter fun (c, _, _) => !(cofStatus c == .isFalse))
        base
  | .vglue lb ty sys base =>
    match sys.find? (fun (c, _) => cofStatus c == .isTrue) with
    | some (_, t) => force fresh t
    | none =>
      .vglue lb ty (sys.filter fun (c, _) => !(cofStatus c == .isFalse)) base
  | .vne _ (.hcomp ty sys u₀) =>
    match sys.find? (fun (c, _) => cofStatus c == .isTrue) with
    | some (_, br) => force fresh (capp fresh br (.vi .one))
    | none =>
      vneAt fresh (.hcomp ty (sys.filter fun (c, _) => !(cofStatus c == .isFalse)) u₀)
  | v => v

partial def eval (fresh : Nat) (env : List Val) : Term → Val
  | .var i => env[i]!
  | .univ n => .vuniv n
  | .pi d c => vpiAt fresh (eval fresh env d) (mkAt fresh env c)
  | .lam b => vlamAt fresh (mkAt fresh env b)
  | .app f a => vapp fresh (eval fresh env f) (eval fresh env a)
  | .sigma d c => vsigmaAt fresh (eval fresh env d) (mkAt fresh env c)
  | .pair a b => vpairAt fresh (eval fresh env a) (eval fresh env b)
  | .fst p => vfst fresh (eval fresh env p)
  | .snd p => vsnd fresh (eval fresh env p)
  | .nat => .vnat
  | .zero => .vzero
  | .succ n => vsuccAt fresh (eval fresh env n)
  | .natrec m z s n =>
    vnatrec fresh (mkAt fresh env m) (eval fresh env z) (eval fresh env s) (eval fresh env n)
  | .int => .vint
  | .ipos t => viposAt fresh (eval fresh env t)
  | .inegsuc t => vinegsucAt fresh (eval fresh env t)
  | .unit => .vunit
  | .tt => .vtt
  | .unitrec m pt t =>
    vunitrec fresh (mkAt fresh env m) (eval fresh env pt) (eval fresh env t)
  | .empty => .vempty
  | .emptyrec ty t => vemptyrec fresh (eval fresh env ty) (eval fresh env t)
  | .sum l r => vsumAt fresh (eval fresh env l) (eval fresh env r)
  | .inl t => vinlAt fresh (eval fresh env t)
  | .inr t => vinrAt fresh (eval fresh env t)
  | .sumcase m fl fr t =>
    vsumcase fresh (mkAt fresh env m) (eval fresh env fl) (eval fresh env fr)
      (eval fresh env t)
  | .susp a => vsuspAt fresh (eval fresh env a)
  | .north => .vnorth
  | .south => .vsouth
  | .merid a r => vmeridAt fresh (eval fresh env a) (eval fresh env r).asIVal
  | .susprec m nc sc mc t =>
    vsusprec fresh (mkAt fresh env m) (eval fresh env nc) (eval fresh env sc)
      (eval fresh env mc) (eval fresh env t)
  | .pushout a b c f g =>
    vpushoutAt fresh (eval fresh env a) (eval fresh env b) (eval fresh env c)
      (eval fresh env f) (eval fresh env g)
  | .pinl t => vpinlAt fresh (eval fresh env t)
  | .pinr t => vpinrAt fresh (eval fresh env t)
  | .ppush f g c r =>
    vppushAt fresh (eval fresh env f) (eval fresh env g) (eval fresh env c)
      (eval fresh env r).asIVal
  | .pushrec m lc rc pc t =>
    vpushrec fresh (mkAt fresh env m) (eval fresh env lc) (eval fresh env rc)
      (eval fresh env pc) (eval fresh env t)
  | .defn n tm _ => evalDefnCached n fresh (fun _ => eval fresh env tm)
  | .em1 car mul => vem1At fresh (eval fresh env car) (eval fresh env mul)
  | .embase => .vembase
  | .emloop g r => vemloopAt fresh (eval fresh env g) (eval fresh env r).asIVal
  | .emcomp mul g h r s2 =>
    vemcompAt fresh (eval fresh env mul) (eval fresh env g) (eval fresh env h)
      (eval fresh env r).asIVal (eval fresh env s2).asIVal
  | .emsquash x y p q u v j1 j2 j3 =>
    vemsquashAt fresh (eval fresh env x) (eval fresh env y) (eval fresh env p)
      (eval fresh env q) (eval fresh env u) (eval fresh env v)
      (eval fresh env j1).asIVal (eval fresh env j2).asIVal
      (eval fresh env j3).asIVal
  | .bgpd ob hom cm =>
    vbgpdAt fresh (eval fresh env ob) (eval fresh env hom)
      (eval fresh env cm)
  | .bpt t => vbptAt fresh (eval fresh env t)
  | .barr x y f r =>
    vbarrAt fresh (eval fresh env x) (eval fresh env y) (eval fresh env f)
      (eval fresh env r).asIVal
  | .bcomp cm x y z f g r s2 =>
    vbcompAt fresh (eval fresh env cm) (eval fresh env x)
      (eval fresh env y) (eval fresh env z) (eval fresh env f)
      (eval fresh env g) (eval fresh env r).asIVal
      (eval fresh env s2).asIVal
  | .bsquash x y p q u v j1 j2 j3 =>
    vbsquashAt fresh (eval fresh env x) (eval fresh env y)
      (eval fresh env p) (eval fresh env q) (eval fresh env u)
      (eval fresh env v) (eval fresh env j1).asIVal
      (eval fresh env j2).asIVal (eval fresh env j3).asIVal
  | .bgrec bT gB pf pl pc t =>
    vbgrecApp fresh (eval fresh env bT) (eval fresh env gB)
      (eval fresh env pf) (eval fresh env pl) (eval fresh env pc)
      (eval fresh env t)
  | .bgelim m gP pb pl pc t =>
    vbgelimApp fresh (mkAt fresh env m) (eval fresh env gP)
      (eval fresh env pb) (eval fresh env pl) (eval fresh env pc)
      (eval fresh env t)
  | .em1rec bT gB b l c t =>
    vem1rec fresh (eval fresh env bT) (eval fresh env gB)
      (eval fresh env b) (eval fresh env l) (eval fresh env c)
      (eval fresh env t)
  | .em1elim m gP b l c t =>
    vem1elim fresh (mkAt fresh env m) (eval fresh env gP) (eval fresh env b)
      (eval fresh env l) (eval fresh env c) (eval fresh env t)
  | .list a => vlistAt fresh (eval fresh env a)
  | .lnil => .vlnil
  | .lcons h t => vlconsAt fresh (eval fresh env h) (eval fresh env t)
  | .listrec m nc cc t =>
    vlistrec fresh (mkAt fresh env m) (eval fresh env nc) (eval fresh env cc)
      (eval fresh env t)
  | .quot a r => vquotAt fresh (eval fresh env a) (eval fresh env r)
  | .qin t => vqinAt fresh (eval fresh env t)
  | .qeq a b w r =>
    vqeqAt fresh (eval fresh env a) (eval fresh env b) (eval fresh env w)
      (eval fresh env r).asIVal
  | .qsquash x y p q r s2 =>
    vqsquashAt fresh (eval fresh env x) (eval fresh env y) (eval fresh env p)
      (eval fresh env q) (eval fresh env r).asIVal
      (eval fresh env s2).asIVal
  | .qelim m mset f feq t =>
    vqelim fresh (mkAt fresh env m) (eval fresh env mset) (eval fresh env f)
      (eval fresh env feq) (eval fresh env t)
  | .trunc a => vtruncAt fresh (eval fresh env a)
  | .tin t => vtinAt fresh (eval fresh env t)
  | .squash x y r =>
    vsquashAt fresh (eval fresh env x) (eval fresh env y) (eval fresh env r).asIVal
  | .truncrec mB prp f t =>
    vtruncrec fresh (eval fresh env mB) (eval fresh env prp)
      (eval fresh env f) (eval fresh env t)
  | .torus => .vtorus
  | .tbase => .vtbase
  | .tloopP r => .vtloopP (eval fresh env r).asIVal
  | .tloopQ r => .vtloopQ (eval fresh env r).asIVal
  | .tsurf r s2 =>
    .vtsurf (eval fresh env r).asIVal (eval fresh env s2).asIVal
  | .torusrec m bc pc qc sc t =>
    vtorusrec fresh (mkAt fresh env m) (eval fresh env bc) (eval fresh env pc)
      (eval fresh env qc) (eval fresh env sc) (eval fresh env t)
  | .s1 => .vs1
  | .sbase => .vsbase
  | .sloop r => .vsloop (eval fresh env r).asIVal
  | .intcase m fp fn t =>
    vintcase fresh (mkAt fresh env m) (eval fresh env fp) (eval fresh env fn)
      (eval fresh env t)
  | .s1elim m b l x =>
    vs1elim fresh (mkAt fresh env m) (eval fresh env b) (eval fresh env l)
      (eval fresh env x)
  | .i0 => .vi .zero
  | .i1 => .vi .one
  | .imax l r => .vi (IVal.iMax (eval fresh env l).asIVal (eval fresh env r).asIVal)
  | .imin l r => .vi (IVal.iMin (eval fresh env l).asIVal (eval fresh env r).asIVal)
  | .ineg r => .vi (IVal.iNeg (eval fresh env r).asIVal)
  | .pathP f l r => vpathPAt fresh (mkAt fresh env f) (eval fresh env l) (eval fresh env r)
  | .plam b => vplamAt fresh (mkAt fresh env b)
  | .papp p l r s =>
    vpapp fresh (eval fresh env p) (eval fresh env l) (eval fresh env r)
      (eval fresh env s).asIVal
  | .transp f a => vtransp fresh (mkAt fresh env f) (eval fresh env a)
  | .hcomp ty sys u₀ =>
    vhcomp fresh (eval fresh env ty)
      (sys.map fun (cof, body) =>
        (cof.map fun (f, b) => ((eval fresh env f).asIVal, b), mkAt fresh env body))
      (eval fresh env u₀)
  | .glueTy sys base =>
    vglueTyAt fresh
      (sys.map fun (cof, T, e) =>
        (cof.map fun (f, b) => ((eval fresh env f).asIVal, b),
          eval fresh env T, eval fresh env e))
      (eval fresh env base)
  | .glueTm gty sys base =>
    vglueAt fresh (eval fresh env gty)
      (sys.map fun (cof, t) =>
        (cof.map fun (f, b) => ((eval fresh env f).asIVal, b), eval fresh env t))
      (eval fresh env base)
  | .unglue gty b => vunglue fresh (eval fresh env gty) (eval fresh env b)
  | .ann t _ => eval fresh env t

partial def capp (fresh : Nat) (c : Closure) (v : Val) : Val :=
  if profTick 1 v then panic! "unreachable" else
  cappCached c v fresh (fun _ => cappRun fresh c v)

partial def cappRun (fresh : Nat) (c : Closure) (v : Val) : Val :=
  match c with
  | .mk _ env body => eval fresh (v :: env) body
  | .reparam c f => capp fresh c (.vi (f v.asIVal))
  | .constV w => w
  | .comp outer inner => capp fresh outer (capp fresh inner v)
  | .piDomOf c =>
    match force fresh (capp fresh c v) with
    | .vpi _ d _ => d
    | _ => panic! "piDomOf: family is not a Π-line"
  | .sigDomOf c =>
    match force fresh (capp fresh c v) with
    | .vsigma _ d _ => d
    | _ => panic! "sigDomOf: family is not a Σ-line"
  | .transpPi fam f =>
    -- v is x₁ : B 1;  w x₁ 0 = transp (λ j, B (¬j)) x₁ : B 0
    let w0 := vtransp fresh (.piDomOf (.reparam fam IVal.iNeg)) v
    vtransp fresh (.transpPiCod fam v) (vapp fresh f w0)
  | .transpPiCod fam x₁ =>
    -- v is the interval point i;  w x₁ i = transp (λ j, B (i ∨ ¬j)) x₁ : B i
    let i := v.asIVal
    let wi := vtransp fresh
      (.piDomOf (.reparam fam (fun j => IVal.iMax i (IVal.iNeg j)))) x₁
    match force fresh (capp fresh fam v) with
    | .vpi _ _ cod => capp fresh cod wi
    | _ => panic! "transpPiCod: family is not a Π-line"
  | .transpSigSnd fam u =>
    -- v is the interval point i;  u i = transp (λ j, B (i ∧ j)) u : B i
    let i := v.asIVal
    let ui := vtransp fresh
      (.sigDomOf (.reparam fam (fun j => IVal.iMin i j))) u
    match force fresh (capp fresh fam v) with
    | .vsigma _ _ cod => capp fresh cod ui
    | _ => panic! "transpSigSnd: family is not a Σ-line"
  | .transpPathP fam p =>
    -- v is j; result: comp (λ i, B i j) [(j=0) ↦ a, (j=1) ↦ b] (p @ j)
    let j := v.asIVal
    let (l0, r0) :=
      match force fresh (capp fresh fam (.vi .zero)) with
      | .vpathP _ _ l r => (l, r)
      | _ => panic! "transpPathP: family is not a PathP-line"
    vcomp fresh (.pathPLine fam j)
      [([(j, false)], .pathPEnd fam false), ([(j, true)], .pathPEnd fam true)]
      (vpapp fresh p l0 r0 j)
  | .pathPLine fam j =>
    match force fresh (capp fresh fam v) with
    | .vpathP _ a _ _ => capp fresh a (.vi j)
    | _ => panic! "pathPLine: family is not a PathP-line"
  | .pathPEnd fam side =>
    match force fresh (capp fresh fam v) with
    | .vpathP _ _ l r => if side then r else l
    | _ => panic! "pathPEnd: family is not a PathP-line"
  | .glueBase fam =>
    match capp fresh fam v with
    | .vglueTy _ _ b => b
    | v' => panic! s!"glueBase: family is not a Glue-line: {v'.head}"
  | .glueBranchT fam k =>
    match capp fresh fam v with
    | .vglueTy _ s _ => (s[k]!).2.1
    | _ => panic! "glueBranchT: family is not a Glue-line"
  | .glueBranchW fam k =>
    match capp fresh fam v with
    | .vglueTy _ s _ => (s[k]!).2.2
    | _ => panic! "glueBranchW: family is not a Glue-line"
  | .glueDeltaTube fam k u₀ =>
    let i := v.asIVal
    let fill := vtransp fresh
      (.reparam (.glueBranchT fam k) (fun j => IVal.iMin i j)) u₀
    vapp fresh (vfst fresh (capp fresh (.glueBranchW fam k) v)) fill
  | .fiberCod f A a => vpathPAt fresh (.constV A) a (vapp fresh f v)
  | .pappLine p lhs rhs => vpapp fresh p lhs rhs v.asIVal
  | .s1loopFam motive => capp fresh motive (.vsloop v.asIVal)
  | .s1elimTube motive b l br => vs1elim fresh motive b l (capp fresh br v)
  | .iposArg br =>
    match force fresh (capp fresh br v) with
    | .vipos _ n => n
    | _ => panic! "iposArg: tube element is not a pos"
  | .inlArg br =>
    match force fresh (capp fresh br v) with
    | .vinl _ n => n
    | _ => panic! "inlArg: tube element is not inl"
  | .inrArg br =>
    match force fresh (capp fresh br v) with
    | .vinr _ n => n
    | _ => panic! "inrArg: tube element is not inr"
  | .inegsucArg br =>
    match force fresh (capp fresh br v) with
    | .vinegsuc _ n => n
    | _ => panic! "inegsucArg: tube element is not a negsuc"
  | .mapApp br x => vapp fresh (capp fresh br v) x
  | .mapFst br => vfst fresh (capp fresh br v)
  | .mapSnd br => vsnd fresh (capp fresh br v)
  | .mapPApp br l r j => vpapp fresh (capp fresh br v) l r j
  | .natPred br =>
    match capp fresh br v with
    | .vsucc _ n => n
    | _ => panic! "natPred: tube element is not a successor"
  | .hcompPi cod sys u₀ =>
    -- v is the function argument x
    vhcomp fresh (capp fresh cod v)
      (sys.map fun (co, br) => (co, Closure.mapApp br v))
      (vapp fresh u₀ v)
  | .hcompPathP fam l r sys u₀ =>
    -- v is j
    let j := v.asIVal
    vhcomp fresh (capp fresh fam v)
      ((sys.map fun (co, br) => (co, Closure.mapPApp br l r j))
        ++ [([(j, false)], .constV l), ([(j, true)], .constV r)])
      (vpapp fresh u₀ l r j)
  | .hfill ty sys u₀ => hfillAt fresh ty sys u₀ v.asIVal
  | .compTube line br =>
    let i := v.asIVal
    vtransp fresh (.reparam line (fun i' => IVal.iMax i i')) (capp fresh br v)
  | .natrecS motive => vpiAt fresh (capp fresh motive v) (.natrecS2 motive v)
  | .natrecS2 motive k => capp fresh motive (vsuccAt fresh k)
  | .intcasePos motive => capp fresh motive (viposAt fresh v)
  | .intcaseNeg motive => capp fresh motive (vinegsucAt fresh v)
  | .sumcaseL motive => capp fresh motive (vinlAt fresh v)
  | .sumcaseR motive => capp fresh motive (vinrAt fresh v)
  | .sumLeftOf c =>
    match force fresh (capp fresh c v) with
    | .vsum _ l _ => l
    | _ => panic! "sumLeftOf: family is not a sum-line"
  | .sumRightOf c =>
    match force fresh (capp fresh c v) with
    | .vsum _ _ r => r
    | _ => panic! "sumRightOf: family is not a sum-line"
  | .suspMcCod motive nc sc => vpathPAt fresh (.suspMeridFam motive v) nc sc
  | .suspMeridFam motive a => capp fresh motive (vmeridAt fresh a v.asIVal)
  | .suspLineOf c =>
    match force fresh (capp fresh c v) with
    | .vsusp _ a => a
    | _ => panic! "suspLineOf: family is not a suspension-line"
  | .susprecTube motive nc sc mc br =>
    vsusprec fresh motive nc sc mc (capp fresh br v)
  | .torusLoopPFam motive => capp fresh motive (.vtloopP v.asIVal)
  | .torusLoopQFam motive => capp fresh motive (.vtloopQ v.asIVal)
  | .torusSurfFam motive bc pc =>
    vpathPAt fresh (.torusSurfInner motive v.asIVal)
      (vpapp fresh pc bc bc v.asIVal) (vpapp fresh pc bc bc v.asIVal)
  | .torusSurfInner motive ri =>
    capp fresh motive (.vtsurf ri v.asIVal)
  | .torusrecTube motive bc pc qc sc br =>
    vtorusrec fresh motive bc pc qc sc (capp fresh br v)
  | .pushLcCod motive => capp fresh motive (vpinlAt fresh v)
  | .pushRcCod motive => capp fresh motive (vpinrAt fresh v)
  | .pushPcCod motive lc rc f g =>
    vpathPAt fresh (.pushPcFam motive f g v)
      (vapp fresh lc (vapp fresh f v)) (vapp fresh rc (vapp fresh g v))
  | .pushPcFam motive f g c =>
    capp fresh motive (vppushAt fresh f g c v.asIVal)
  | .pushAOf c =>
    match force fresh (capp fresh c v) with
    | .vpushout _ a _ _ _ _ => a
    | _ => panic! "pushAOf: family is not a pushout-line"
  | .pushBOf c =>
    match force fresh (capp fresh c v) with
    | .vpushout _ _ b _ _ _ => b
    | _ => panic! "pushBOf: family is not a pushout-line"
  | .pushCOf c =>
    match force fresh (capp fresh c v) with
    | .vpushout _ _ _ cc _ _ => cc
    | _ => panic! "pushCOf: family is not a pushout-line"
  | .pushrecTube motive lc rc pc br =>
    vpushrec fresh motive lc rc pc (capp fresh br v)
  | .em1recCCod B C mul l b => vpiAt fresh C (.em1recCCod2 B mul l b v)
  | .em1recCCod2 B mul l b g =>
    vpathPAt fresh (.em1recCFam B l b v)
      (vapp fresh l g) (vapp fresh l (vapp fresh (vapp fresh mul g) v))
  | .em1recCFam B l b h =>
    vpathPAt fresh (.constV B) b (vpapp fresh (vapp fresh l h) b b v.asIVal)
  | .em1elimLCod motive b => vpathPAt fresh (.em1elimLFam motive v) b b
  | .em1elimLFam motive g => capp fresh motive (vemloopAt fresh g v.asIVal)
  | .em1elimDCCod motive C mul l b =>
    vpiAt fresh C (.em1elimDCCod2 motive mul l b v)
  | .em1elimDCCod2 motive mul l b g =>
    vpathPAt fresh (.em1elimDCFam motive mul l b g v)
      (vapp fresh l g) (vapp fresh l (vapp fresh (vapp fresh mul g) v))
  | .em1elimDCFam motive mul l b g h =>
    vpathPAt fresh (.em1elimDCInner motive mul g h v.asIVal) b
      (vpapp fresh (vapp fresh l h) b b v.asIVal)
  | .em1elimDCInner motive mul g h rj =>
    capp fresh motive (vemcompAt fresh mul g h rj v.asIVal)
  | .em1elimGCod motive =>
    vapp fresh (eval fresh [] em1IsGpdTm) (capp fresh motive v)
  | .em1elimTube motive gP b l cc br =>
    vem1elim fresh motive gP b l cc (capp fresh br v)
  | .em1CarOf c =>
    match force fresh (capp fresh c v) with
    | .vem1 _ car _ => car
    | _ => panic! "em1CarOf: family is not an EM1-line"
  | .em1recTube B gB b l cc br =>
    vem1rec fresh B gB b l cc (capp fresh br v)
  | .bgrecTube bT gB pf pl pc br =>
    vbgrecApp fresh bT gB pf pl pc (capp fresh br v)
  | .bgelimTube m gP pb pl pc br =>
    vbgelimApp fresh m gP pb pl pc (capp fresh br v)
  | .listCcCod motive A => vpiAt fresh (vlistAt fresh A) (.listCcCod2 motive v)
  | .listCcCod2 motive h =>
    vpiAt fresh (capp fresh motive v) (.constV (capp fresh motive (vlconsAt fresh h v)))
  | .listArgOf c =>
    match force fresh (capp fresh c v) with
    | .vlist _ a => a
    | _ => panic! "listArgOf: family is not a list-line"
  | .lheadArg br =>
    match force fresh (capp fresh br v) with
    | .vlcons _ h _ => h
    | _ => panic! "lheadArg: tube element is not a cons"
  | .ltailArg br =>
    match force fresh (capp fresh br v) with
    | .vlcons _ _ t => t
    | _ => panic! "ltailArg: tube element is not a cons"
  | .listrecTube motive nc cc br =>
    vlistrec fresh motive nc cc (capp fresh br v)
  | .qelimInCod motive => capp fresh motive (vqinAt fresh v)
  | .qelimEqCod motive A rel f =>
    vpiAt fresh A (.qelimEqCod2 motive rel f v)
  | .qelimEqCod2 motive rel f a =>
    vpiAt fresh (vapp fresh (vapp fresh rel a) v) (.qelimEqCod3 motive f a v)
  | .qelimEqCod3 motive f a b =>
    vpathPAt fresh (.qelimEqFam motive a b v)
      (vapp fresh f a) (vapp fresh f b)
  | .qelimEqFam motive a b w =>
    capp fresh motive (vqeqAt fresh a b w v.asIVal)
  | .qelimSetCod motive =>
    let T := capp fresh motive v
    vpiAt fresh T (.isSetOf1 T)
  | .isSetOf1 T => vpiAt fresh T (.isSetOf2 T v)
  | .isSetOf2 T u => vpiAt fresh (vpathPAt fresh (.constV T) u v) (.isSetOf3 T u v)
  | .isSetOf3 T u v2 => vpiAt fresh (vpathPAt fresh (.constV T) u v2) (.isSetOf4 T u v2 v)
  | .isSetOf4 T u v2 p =>
    vpathPAt fresh (.constV (vpathPAt fresh (.constV T) u v2)) p v
  | .quotAOf c =>
    match force fresh (capp fresh c v) with
    | .vquot _ a _ => a
    | _ => panic! "quotAOf: family is not a quotient-line"
  | .qelimTube motive mset f feq br =>
    vqelim fresh motive mset f feq (capp fresh br v)
  | .truncArgOf c =>
    match force fresh (capp fresh c v) with
    | .vtrunc _ a => a
    | _ => panic! "truncArgOf: family is not a truncation-line"
  | .truncrecTube mB prp f br =>
    vtruncrec fresh mB prp f (capp fresh br v)

partial def vapp (fresh : Nat) (f a : Val) : Val :=
  match force fresh f with
  | .vlam _ c => capp fresh c a
  | .vne _ n => vneAt fresh (.app n a)
  | junk => junk -- off-face junk passthrough

partial def vfst (fresh : Nat) (v : Val) : Val :=
  match force fresh v with
  | .vpair _ a _ => a
  | .vne _ n => vneAt fresh (.fst n)
  | junk => junk -- off-face junk passthrough

partial def vsnd (fresh : Nat) (v : Val) : Val :=
  match force fresh v with
  | .vpair _ _ b => b
  | .vne _ n => vneAt fresh (.snd n)
  | junk => junk -- off-face junk passthrough

partial def vnatrec (fresh : Nat) (motive : Closure) (z s : Val) (n : Val) : Val :=
  match force fresh n with
  | .vzero => z
  | .vsucc _ m => vapp fresh (vapp fresh s m) (vnatrec fresh motive z s m)
  | .vne _ n => vneAt fresh (.natrec motive z s n)
  | junk => junk -- off-face junk passthrough

/-- ℤ case split. -/
partial def vintcase (fresh : Nat) (motive : Closure) (fpos fneg : Val)
    (t : Val) : Val :=
  match force fresh t with
  | .vipos _ n => vapp fresh fpos n
  | .vinegsuc _ n => vapp fresh fneg n
  | .vne _ ne => vneAt fresh (.intcase motive fpos fneg ne)
  | junk => junk -- off-face junk (transpGlue partial elements): pass through, sound off-face

/-- Unit elimination (computes on `tt` only; no η). -/
partial def vunitrec (fresh : Nat) (motive : Closure) (ptt : Val) (t : Val) : Val :=
  match force fresh t with
  | .vtt => ptt
  | .vne _ ne => vneAt fresh (.unitrec motive ptt ne)
  | junk => junk -- off-face junk (transpGlue partial elements): pass through, sound off-face

/-- Sum case split. -/
partial def vsumcase (fresh : Nat) (motive : Closure) (fl fr : Val)
    (t : Val) : Val :=
  match force fresh t with
  | .vinl _ a => vapp fresh fl a
  | .vinr _ b => vapp fresh fr b
  | .vne _ ne => vneAt fresh (.sumcase motive fl fr ne)
  | junk => junk -- off-face junk (transpGlue partial elements): pass through, sound off-face

/-- Empty elimination (always blocked: there are no canonical elements). -/
partial def vemptyrec (fresh : Nat) (ty : Val) (t : Val) : Val :=
  match force fresh t with
  | .vne _ ne => vneAt fresh (.emptyrec ty ne)
  | _ => panic! "vemptyrec: a canonical element of the empty type?!"

/-- Circle elimination.  On an `hcomp` cell it commutes with the
composition: `elim (hcomp [φ ↦ u] u₀) = comp (λ i, P (hfill u u₀ i))
[φ ↦ elim ∘ u] (elim u₀)`.  (For a universe-valued motive the resulting
`hcomp U` is stuck — HCompU is phase 2b'.) -/
partial def vpushrec (fresh : Nat) (motive : Closure) (lc rc pc : Val)
    (x : Val) : Val :=
  match x with
  | .vppush _ f g c r =>
    vpapp fresh (vapp fresh pc c)
      (vapp fresh lc (vapp fresh f c)) (vapp fresh rc (vapp fresh g c)) r
  | .vne _ (.hcomp tyc sys u₀) =>
    match force fresh tyc with
    | .vpushout _ _ _ _ _ _ =>
      vcomp fresh (.comp motive (.hfill tyc sys u₀))
        (sys.map fun (co, br) => (co, .pushrecTube motive lc rc pc br))
        (vpushrec fresh motive lc rc pc u₀)
    | _ => vneAt fresh (.pushrec motive lc rc pc (.hcomp tyc sys u₀))
  | _ =>
  match force fresh x with
  | .vpinl _ a => vapp fresh lc a
  | .vpinr _ b => vapp fresh rc b
  | .vppush _ f g c r =>
    vpapp fresh (vapp fresh pc c)
      (vapp fresh lc (vapp fresh f c)) (vapp fresh rc (vapp fresh g c)) r
  | .vne _ n => vneAt fresh (.pushrec motive lc rc pc n)
  | junk => junk -- off-face junk (transpGlue partial elements): pass through, sound off-face

partial def vem1elim (fresh : Nat) (motive : Closure) (gP b l c : Val)
    (x : Val) : Val :=
  match x with
  | .vemloop _ g r => vpapp fresh (vapp fresh l g) b b r
  | .vemcomp _ mul g h rj ri =>
    let lg := vapp fresh l g
    let lgh := vapp fresh l (vapp fresh (vapp fresh mul g) h)
    vpapp fresh
      (vpapp fresh (vapp fresh (vapp fresh c g) h) lg lgh rj)
      b (vpapp fresh (vapp fresh l h) b b rj) ri
  | .vemsquash _ xx yy p q u v r1 r2 r3 =>
    vneAt fresh (.em1elim motive gP b l c (.emsquashCell xx yy p q u v r1 r2 r3))
  | .vne _ (.hcomp tyc sys u₀) =>
    match force fresh tyc with
    | .vem1 _ _ _ =>
      vcomp fresh (.comp motive (.hfill tyc sys u₀))
        (sys.map fun (co, br) => (co, .em1elimTube motive gP b l c br))
        (vem1elim fresh motive gP b l c u₀)
    | _ => vneAt fresh (.em1elim motive gP b l c (.hcomp tyc sys u₀))
  | _ =>
  match force fresh x with
  | .vembase => b
  | .vemloop _ g r => vpapp fresh (vapp fresh l g) b b r
  | .vemcomp _ mul g h rj ri =>
    let lg := vapp fresh l g
    let lgh := vapp fresh l (vapp fresh (vapp fresh mul g) h)
    vpapp fresh
      (vpapp fresh (vapp fresh (vapp fresh c g) h) lg lgh rj)
      b (vpapp fresh (vapp fresh l h) b b rj) ri
  | .vemsquash _ xx yy p q u v r1 r2 r3 =>
    vneAt fresh (.em1elim motive gP b l c (.emsquashCell xx yy p q u v r1 r2 r3))
  | .vne _ n => vneAt fresh (.em1elim motive gP b l c n)
  | junk => junk -- off-face junk (transpGlue partial elements): pass through, sound off-face

/-- Dependent elimination for the groupoid classifying space (mirrors
`vem1elim`; same computation as `vbgrecApp`, motive-typed hcomp tubes). -/
partial def vbgelimApp (fresh : Nat) (motive : Closure) (gP pb pl pc : Val)
    (x : Val) : Val :=
  let plAt (xx yy ff : Val) : Val :=
    vapp fresh (vapp fresh (vapp fresh pl xx) yy) ff
  match force fresh x with
  | .vbpt _ t => vapp fresh pb t
  | .vbarr _ xx yy f r =>
    vpapp fresh (plAt xx yy f) (vapp fresh pb xx) (vapp fresh pb yy) r
  | .vbcomp _ cm xx yy zz f g rj ri =>
    let lf := plAt xx yy f
    let lfg := plAt xx zz
      (vapp fresh (vapp fresh (vapp fresh (vapp fresh
        (vapp fresh cm xx) yy) zz) f) g)
    let ccell := vapp fresh (vapp fresh (vapp fresh (vapp fresh
      (vapp fresh pc xx) yy) zz) f) g
    vpapp fresh
      (vpapp fresh ccell lf lfg rj)
      (vapp fresh pb xx)
      (vpapp fresh (plAt yy zz g) (vapp fresh pb yy)
        (vapp fresh pb zz) rj)
      ri
  | .vbsquash _ xx yy p q u v r1 r2 r3 =>
    vneAt fresh (.bgelim motive gP pb pl pc
      (.emsquashCell xx yy p q u v r1 r2 r3))
  | .vne _ (.hcomp tyc sys u₀) =>
    match force fresh tyc with
    | .vbgpd _ _ _ _ =>
      vcomp fresh (.comp motive (.hfill tyc sys u₀))
        (sys.map fun (co, br) => (co, .bgelimTube motive gP pb pl pc br))
        (vbgelimApp fresh motive gP pb pl pc u₀)
    | _ => vneAt fresh (.bgelim motive gP pb pl pc (.hcomp tyc sys u₀))
  | .vne _ n => vneAt fresh (.bgelim motive gP pb pl pc n)
  | junk => junk -- off-face junk passthrough

/-- Recursion for the groupoid classifying space (mirrors `vem1rec`):
points, arrows and composition squares compute; the truncation cell is
kept stuck behind the generic `emsquashCell` neutral wrapper; `hcomp`
cells commute into the motive. -/
partial def vbgrecApp (fresh : Nat) (bT gB pf pl pc : Val) (x : Val) :
    Val :=
  let plAt (xx yy ff : Val) : Val :=
    vapp fresh (vapp fresh (vapp fresh pl xx) yy) ff
  match force fresh x with
  | .vbpt _ t => vapp fresh pf t
  | .vbarr _ xx yy f r =>
    vpapp fresh (plAt xx yy f) (vapp fresh pf xx) (vapp fresh pf yy) r
  | .vbcomp _ cm xx yy zz f g rj ri =>
    let lf := plAt xx yy f
    let lfg := plAt xx zz
      (vapp fresh (vapp fresh (vapp fresh (vapp fresh
        (vapp fresh cm xx) yy) zz) f) g)
    let ccell := vapp fresh (vapp fresh (vapp fresh (vapp fresh
      (vapp fresh pc xx) yy) zz) f) g
    vpapp fresh
      (vpapp fresh ccell lf lfg rj)
      (vapp fresh pf xx)
      (vpapp fresh (plAt yy zz g) (vapp fresh pf yy)
        (vapp fresh pf zz) rj)
      ri
  | .vbsquash _ xx yy p q u v r1 r2 r3 =>
    vneAt fresh (.bgrec bT gB pf pl pc
      (.emsquashCell xx yy p q u v r1 r2 r3))
  | .vne _ (.hcomp tyc sys u₀) =>
    match force fresh tyc with
    | .vbgpd _ _ _ _ =>
      vhcomp fresh bT
        (sys.map fun (co, br) => (co, .bgrecTube bT gB pf pl pc br))
        (vbgrecApp fresh bT gB pf pl pc u₀)
    | _ => vneAt fresh (.bgrec bT gB pf pl pc (.hcomp tyc sys u₀))
  | .vne _ n => vneAt fresh (.bgrec bT gB pf pl pc n)
  | junk => junk -- off-face junk passthrough

partial def vem1rec (fresh : Nat) (B gB b l c : Val) (x : Val) : Val :=
  match x with
  | .vemloop _ g r => vpapp fresh (vapp fresh l g) b b r
  | .vemcomp _ mul g h rj ri =>
    let lg := vapp fresh l g
    let lgh := vapp fresh l (vapp fresh (vapp fresh mul g) h)
    vpapp fresh
      (vpapp fresh (vapp fresh (vapp fresh c g) h) lg lgh rj)
      b (vpapp fresh (vapp fresh l h) b b rj) ri
  | .vemsquash _ xx yy p q u v r1 r2 r3 =>
    vneAt fresh (.em1rec B gB b l c (.emsquashCell xx yy p q u v r1 r2 r3))
  | .vne _ (.hcomp tyc sys u₀) =>
    match force fresh tyc with
    | .vem1 _ _ _ =>
      vhcomp fresh B
        (sys.map fun (co, br) => (co, .em1recTube B gB b l c br))
        (vem1rec fresh B gB b l c u₀)
    | _ => vneAt fresh (.em1rec B gB b l c (.hcomp tyc sys u₀))
  | _ =>
  match force fresh x with
  | .vembase => b
  | .vemloop _ g r => vpapp fresh (vapp fresh l g) b b r
  | .vemcomp _ mul g h rj ri =>
    let lg := vapp fresh l g
    let lgh := vapp fresh l (vapp fresh (vapp fresh mul g) h)
    vpapp fresh
      (vpapp fresh (vapp fresh (vapp fresh c g) h) lg lgh rj)
      b (vpapp fresh (vapp fresh l h) b b rj) ri
  | .vemsquash _ xx yy p q u v r1 r2 r3 =>
    vneAt fresh (.em1rec B gB b l c (.emsquashCell xx yy p q u v r1 r2 r3))
  | .vne _ n => vneAt fresh (.em1rec B gB b l c n)
  | junk => junk -- off-face junk (transpGlue partial elements): pass through, sound off-face

partial def vlistrec (fresh : Nat) (motive : Closure) (nc cc : Val)
    (x : Val) : Val :=
  match force fresh x with
  | .vlnil => nc
  | .vlcons _ h t =>
    vapp fresh (vapp fresh (vapp fresh cc h) t)
      (vlistrec fresh motive nc cc t)
  | .vne _ (.hcomp tyc sys u₀) =>
    match force fresh tyc with
    | .vlist _ _ =>
      vcomp fresh (.comp motive (.hfill tyc sys u₀))
        (sys.map fun (co, br) => (co, .listrecTube motive nc cc br))
        (vlistrec fresh motive nc cc u₀)
    | _ => vneAt fresh (.listrec motive nc cc (.hcomp tyc sys u₀))
  | .vne _ n => vneAt fresh (.listrec motive nc cc n)
  | junk => junk -- off-face junk (transpGlue partial elements): pass through, sound off-face

partial def vqelim (fresh : Nat) (motive : Closure) (mset f feq : Val)
    (x : Val) : Val :=
  match x with
  | .vqeq _ a b w r =>
    vpapp fresh (vapp fresh (vapp fresh (vapp fresh feq a) b) w)
      (vapp fresh f a) (vapp fresh f b) r
  | .vqsquash _ xx yy p q r s =>
    -- Deliberately stuck at generic r/s (sound: `force` collapses the
    -- cell whenever a face decides; full computation would need the
    -- isSet→SquareP fill — future work).
    vneAt fresh (.qelim motive mset f feq (.qsquashCell xx yy p q r s))
  | .vne _ (.hcomp tyc sys u₀) =>
    match force fresh tyc with
    | .vquot _ _ _ =>
      vcomp fresh (.comp motive (.hfill tyc sys u₀))
        (sys.map fun (co, br) => (co, .qelimTube motive mset f feq br))
        (vqelim fresh motive mset f feq u₀)
    | _ => vneAt fresh (.qelim motive mset f feq (.hcomp tyc sys u₀))
  | _ =>
  match force fresh x with
  | .vqin _ a => vapp fresh f a
  | .vqeq _ a b w r =>
    vpapp fresh (vapp fresh (vapp fresh (vapp fresh feq a) b) w)
      (vapp fresh f a) (vapp fresh f b) r
  | .vqsquash _ xx yy p q r s =>
    vneAt fresh (.qelim motive mset f feq (.qsquashCell xx yy p q r s))
  | .vne _ n => vneAt fresh (.qelim motive mset f feq n)
  | junk => junk -- off-face junk (transpGlue partial elements): pass through, sound off-face

partial def vtruncrec (fresh : Nat) (mB prp f : Val) (x : Val) : Val :=
  -- squash cells and hcomp cells are matched UNFORCED first.
  match x with
  | .vsquash _ a b r =>
    let ra := vtruncrec fresh mB prp f a
    let rb := vtruncrec fresh mB prp f b
    vpapp fresh (vapp fresh (vapp fresh prp ra) rb) ra rb r
  | .vne _ (.hcomp tyc sys u₀) =>
    match force fresh tyc with
    | .vtrunc _ _ =>
      -- the codomain is constant, so the commute is a homogeneous hcomp
      vhcomp fresh mB
        (sys.map fun (co, br) => (co, .truncrecTube mB prp f br))
        (vtruncrec fresh mB prp f u₀)
    | _ => vneAt fresh (.truncrec mB prp f (.hcomp tyc sys u₀))
  | _ =>
  match force fresh x with
  | .vtin _ a => vapp fresh f a
  | .vsquash _ a b r =>
    let ra := vtruncrec fresh mB prp f a
    let rb := vtruncrec fresh mB prp f b
    vpapp fresh (vapp fresh (vapp fresh prp ra) rb) ra rb r
  | .vne _ n => vneAt fresh (.truncrec mB prp f n)
  | junk => junk -- off-face junk (transpGlue partial elements): pass through, sound off-face

partial def vtorusrec (fresh : Nat) (motive : Closure) (bc pc qc sc : Val)
    (x : Val) : Val :=
  -- Cells are matched UNFORCED first (lazy-collapse discipline).
  match x with
  | .vtloopP r => vpapp fresh pc bc bc r
  | .vtloopQ r => vpapp fresh qc bc bc r
  | .vtsurf r s =>
    vpapp fresh (vpapp fresh sc qc qc r)
      (vpapp fresh pc bc bc r) (vpapp fresh pc bc bc r) s
  | .vne _ (.hcomp tyc sys u₀) =>
    match force fresh tyc with
    | .vtorus =>
      vcomp fresh (.comp motive (.hfill tyc sys u₀))
        (sys.map fun (co, br) => (co, .torusrecTube motive bc pc qc sc br))
        (vtorusrec fresh motive bc pc qc sc u₀)
    | _ => vneAt fresh (.torusrec motive bc pc qc sc (.hcomp tyc sys u₀))
  | _ =>
  match force fresh x with
  | .vtbase => bc
  | .vtloopP r => vpapp fresh pc bc bc r
  | .vtloopQ r => vpapp fresh qc bc bc r
  | .vtsurf r s =>
    vpapp fresh (vpapp fresh sc qc qc r)
      (vpapp fresh pc bc bc r) (vpapp fresh pc bc bc r) s
  | .vne _ n => vneAt fresh (.torusrec motive bc pc qc sc n)
  | junk => junk -- off-face junk (transpGlue partial elements): pass through, sound off-face

partial def vsusprec (fresh : Nat) (motive : Closure) (nc sc mc : Val)
    (x : Val) : Val :=
  -- Match `merid` cells and hcomp cells UNFORCED first (lazy-collapse
  -- discipline: eager endpoint collapse would destroy Kan structure).
  match x with
  | .vmerid _ a r => vpapp fresh (vapp fresh mc a) nc sc r
  | .vne _ (.hcomp tyc sys u₀) =>
    match force fresh tyc with
    | .vsusp _ _ =>
      vcomp fresh (.comp motive (.hfill tyc sys u₀))
        (sys.map fun (co, br) => (co, .susprecTube motive nc sc mc br))
        (vsusprec fresh motive nc sc mc u₀)
    | _ => vneAt fresh (.susprec motive nc sc mc (.hcomp tyc sys u₀))
  | _ =>
  match force fresh x with
  | .vnorth => nc
  | .vsouth => sc
  | .vmerid _ a r => vpapp fresh (vapp fresh mc a) nc sc r
  | .vne _ n => vneAt fresh (.susprec motive nc sc mc n)
  | junk => junk -- off-face junk (transpGlue partial elements): pass through, sound off-face

partial def vs1elim (fresh : Nat) (motive : Closure) (b l : Val) (x : Val) : Val :=
  -- Match the loop constructor and hcomp cells *before* forcing:
  -- `elim (sloop 0) = l @ 0` is convertible to `b` by the checked boundary
  -- of `l`, and the commute rule agrees with true-face collapse — but unlike
  -- the collapsed values, these preserve the `Glue` structure that
  -- `transpGlue` extracts at endpoints.
  match x with
  | .vsloop r => vpapp fresh l b b r
  | .vne _ (.hcomp tyc sys u₀) =>
    match force fresh tyc with
    | .vs1 =>
      vcomp fresh (.comp motive (.hfill .vs1 sys u₀))
        (sys.map fun (co, br) => (co, .s1elimTube motive b l br))
        (vs1elim fresh motive b l u₀)
    | _ => vneAt fresh (.s1elim motive b l (.hcomp tyc sys u₀))
  | _ =>
  match force fresh x with
  | .vsbase => b
  | .vsloop r => vpapp fresh l b b r
  | .vne _ n => vneAt fresh (.s1elim motive b l n)
  | junk => junk -- off-face junk (transpGlue partial elements): pass through, sound off-face

/-- Path application.  A `plam` is instantiated even at the endpoints (the
checker verified the boundary conditions, so this is definitionally equal to
the annotation and, crucially, preserves `Glue` branch structure for the Kan
operations).  The endpoint annotations implement the boundary rules for
*neutral* paths. -/
partial def vpapp (fresh : Nat) (p lhs rhs : Val) (r : IVal) : Val :=
  match force fresh p with
  | .vplam _ c => capp fresh c (.vi r)
  | .vne _ n =>
    if r.isZero then lhs
    else if r.isOne then rhs
    else vneAt fresh (.papp n lhs rhs r)
  | junk => junk -- off-face junk passthrough

/-- Kan transport. -/
partial def vtransp (fresh : Nat) (fam : Closure) (a : Val) : Val :=
  if profTick 5 a then panic! "unreachable" else
  -- Fast path: a plain closure whose body never mentions its binder is
  -- constant, with no evaluation at all.
  if (match fam with
      | .mk _ _ body => !body.dependsOn 0
      | _ => false) then a
  else
  -- Inspect the family at a generic point (level `fresh`).
  let generic := capp (fresh + 1) fam (.vi (.var fresh))
  -- Constancy: occurs-check of the generic level in the value (mirrors
  -- quotation, incl. `force`, but allocates nothing and exits early).
  -- If the family is constant, transport is identity.
  if !(usesLvl (fresh + 1) fresh generic) then a
  else
    match force fresh generic with
    | .vpi _ _ _ => vlamAt fresh (.transpPi fam a)
    | .vsigma _ _ _ =>
      let u1 := vtransp fresh (.sigDomOf fam) (vfst fresh a)
      let v1 := vtransp fresh (.transpSigSnd fam (vfst fresh a)) (vsnd fresh a)
      vpairAt fresh u1 v1
    | .vpathP _ _ _ _ => vplamAt fresh (.transpPathP fam a)
    | .vglueTy _ _ _ => transpGlue fresh fam a
    | .vnat => a
    | .vint => a
    | .vunit => a
    | .vempty => a
    | .vs1 => a
    | .vtorus => a
    | .vpushout _ _ _ _ _ _ =>
      match force fresh a with
      | .vpinl _ x => vpinlAt fresh (vtransp fresh (.pushAOf fam) x)
      | .vpinr _ y => vpinrAt fresh (vtransp fresh (.pushBOf fam) y)
      | .vppush _ _ _ c r =>
        (match force fresh (capp fresh fam (.vi .one)) with
         | .vpushout _ _ _ _ f1 g1 =>
           vppushAt fresh f1 g1 (vtransp fresh (.pushCOf fam) c) r
         | _ => panic! "vtransp: pushout line lost")
      | .vne _ _ => vneAt fresh (.transp fam a)
      | junk => junk -- off-face junk passthrough
    | .vem1 _ _ _ =>
      match force fresh a with
      | .vembase => .vembase
      | .vemloop _ g r =>
        vemloopAt fresh (vtransp fresh (.em1CarOf fam) g) r
      | .vemcomp _ _ g h rj ri =>
        (match force fresh (capp fresh fam (.vi .one)) with
         | .vem1 _ _ mul1 =>
           vemcompAt fresh mul1 (vtransp fresh (.em1CarOf fam) g)
             (vtransp fresh (.em1CarOf fam) h) rj ri
         | _ => panic! "vtransp: EM1 line lost")
      | .vne _ _ => vneAt fresh (.transp fam a)
      | _ => vneAt fresh (.transp fam a)
    | .vlist _ _ =>
      match force fresh a with
      | .vlnil => .vlnil
      | .vlcons _ h t =>
        vlconsAt fresh (vtransp fresh (.listArgOf fam) h) (vtransp fresh fam t)
      | .vne _ _ => vneAt fresh (.transp fam a)
      | junk => junk -- off-face junk passthrough
    | .vquot _ _ _ =>
      match force fresh a with
      | .vqin _ x => vqinAt fresh (vtransp fresh (.quotAOf fam) x)
      | _ => vneAt fresh (.transp fam a)
    | .vtrunc _ _ =>
      match force fresh a with
      | .vtin _ x => vtinAt fresh (vtransp fresh (.truncArgOf fam) x)
      | .vsquash _ x y r =>
        vsquashAt fresh (vtransp fresh fam x) (vtransp fresh fam y) r
      | .vne _ _ => vneAt fresh (.transp fam a)
      | junk => junk -- off-face junk passthrough
    | .vsusp _ _ =>
      match force fresh a with
      | .vnorth => .vnorth
      | .vsouth => .vsouth
      | .vmerid _ x r => vmeridAt fresh (vtransp fresh (.suspLineOf fam) x) r
      | .vne _ _ => vneAt fresh (.transp fam a)
      | junk => junk -- off-face junk passthrough
    | .vsum _ _ _ =>
      match force fresh a with
      | .vinl _ x => vinlAt fresh (vtransp fresh (.sumLeftOf fam) x)
      | .vinr _ y => vinrAt fresh (vtransp fresh (.sumRightOf fam) y)
      | .vne _ _ => vneAt fresh (.transp fam a)
      | junk => junk -- off-face junk passthrough
    | .vuniv _ => a
    | .vne _ _ => vneAt fresh (.transp fam a)
    | _ => panic! "vtransp: family is not a line of types"

/-- Transport along a line of `Glue` types (CCHM §6.2, with per-branch
`δₖ := ∀i.φₖ` computed by `cofForall`):

1. unglue the input at `0`;
2. where `δₖ` is live, transport in the branch's own type line
   (`t₁'ₖ := transp Tₖ u₀`) and add the tube `λ i, wₖ i (fillₖ i)` to the
   base transport, so that `a₁' ≡ w₁ₖ t₁'ₖ` *definitionally* on `δₖ`;
3. at `1`, each live face produces a fiber point of `w₁ₖ` over `a₁'`:
   the center of the contractible fiber, corrected on `δₖ` — where the
   result must agree with `t₁'ₖ` — by composing along the contraction path
   with an `hcomp` *on the fiber Σ-type*;
4. adjust the base by the fiber paths and reassemble with `glue`.
   A face that holds identically at `1` collapses the result to its fiber
   point. -/
partial def transpGlue (fresh : Nat) (fam : Closure) (u₀ : Val) : Val :=
  let sysG :=
    match capp (fresh + 1) fam (.vi (.var fresh)) with
    | .vglueTy _ s _ => s
    | v' => panic! s!"transpGlue: family is not a Glue-line: {v'.head}"
  let n := sysG.length
  let deltas := sysG.map fun (c, _, _) => cofForall fresh c
  let deltaAt := fun (k : Nat) =>
    match deltas[k]! with
    | some dc => if cofStatus dc == .isFalse then none else some dc
    | none => none
  let t1'At := fun (k : Nat) =>
    (deltaAt k).map fun _ => vtransp fresh (.glueBranchT fam k) u₀
  let a0 := vunglue fresh (capp fresh fam (.vi .zero)) u₀
  let baseLine := Closure.glueBase fam
  let deltaTubes := (List.range n).filterMap fun k =>
    (deltaAt k).map fun dc => (dc, Closure.glueDeltaTube fam k u₀)
  let a1' :=
    if deltaTubes.isEmpty then vtransp fresh baseLine a0
    else vcomp fresh baseLine deltaTubes a0
  match capp fresh fam (.vi .one) with
  | .vglueTy _ sys1 base1 =>
    -- the fiber point (t₁ₖ, αₖ) of branch k over a₁'
    let fiberPoint := fun (k : Nat) =>
      let (_, T1k, w1k) := sys1[k]!
      let centerContr := vapp fresh (vsnd fresh w1k) a1'
      let plain :=
        let ctr := vfst fresh centerContr
        (vfst fresh ctr, vsnd fresh ctr)
      match deltaAt k, t1'At k with
      | some dc, some t1' =>
        match cofStatus dc with
        | .isTrue =>
          -- on δ the base tube makes `a₁' ≡ w₁ₖ t₁'ₖ` hold definitionally
          (t1', vplamAt fresh (.constV a1'))
        | .undet =>
          -- compose the center towards the δ-partial solution on the fiber
          let ctr := vfst fresh centerContr
          let pδ : Val := vpairAt fresh t1' (vplamAt fresh (.constV a1'))
          let q := vapp fresh (vsnd fresh centerContr) pδ
          let fibTy : Val := vsigmaAt fresh T1k (.fiberCod (vfst fresh w1k) base1 a1')
          let res := vhcomp fresh fibTy [(dc, .pappLine q ctr pδ)] ctr
          (vfst fresh res, vsnd fresh res)
        | .isFalse => plain
      | _, _ => plain
    match (List.range n).find? (fun k => cofStatus (sys1[k]!).1 == .isTrue) with
    | some k => (fiberPoint k).1
    | none =>
      let live := (List.range n).filter fun k =>
        !(cofStatus (sys1[k]!).1 == .isFalse)
      let fibs := live.map fun k =>
        let (c1k, _, w1k) := sys1[k]!
        let (t1k, αk) := fiberPoint k
        (c1k, t1k, Closure.pappLine αk a1' (vapp fresh (vfst fresh w1k) t1k))
      let a1 := vhcomp fresh base1
        (fibs.map fun (c, _, tube) => (c, tube)) a1'
      vglueAt fresh (capp fresh fam (.vi .one)) (fibs.map fun (c, t, _) => (c, t)) a1
  | v' => panic! s!"transpGlue: family is not a Glue-line: {v'.head}"

/-- Unglue, driven by the (unforced) `Glue` type of the argument: on a face
that holds, apply the equivalence; on a `glue` value, project the base. -/
partial def vunglue (fresh : Nat) (ty : Val) (b : Val) : Val :=
  match ty with
  | .vglueTy _ sys _ =>
    match sys.find? (fun (c, _, _) => cofStatus c == .isTrue) with
    | some (_, _, w) => vapp fresh (vfst fresh w) b
    | none =>
      match force fresh b with
      | .vglue _ _ _ a => a
      | .vne _ n => vneAt fresh (.unglue ty n)
      | _ => panic! "vunglue: not a glue value"
  | ty => panic! s!"vunglue: not a Glue type: {ty.head}"

/-- Homogeneous composition. -/
partial def vhcomp (fresh : Nat) (ty : Val) (sys : List (VCof × Closure))
    (u₀ : Val) : Val :=
  if profTick 4 u₀ then panic! "unreachable" else
  -- HCompU: composition *of types* is a `Glue` along the branch lines,
  -- glued by `lineEquiv` (reversed transport is an equivalence).  Handled
  -- before the true-face rule: the branch selection happens lazily in
  -- `force`, so the Kan structure stays available (same principle as the
  -- other lazy boundary collapses).  Branches are kept unfiltered for
  -- stable positions.
  match force fresh ty with
  | .vuniv _ =>
    let lineEquivV := eval fresh [] lineEquivTm
    vglueTyAt fresh
      (sys.map fun (co, brE) =>
        let e0 := capp fresh brE (.vi .zero)
        let e1 := capp fresh brE (.vi .one)
        (co, e1,
          vapp fresh (vapp fresh (vapp fresh lineEquivV e0) e1) (vplamAt fresh brE)))
      u₀
  -- HIT cell: kept as a value even on a true face — the collapse happens
  -- lazily in `force`, so the eliminator's commute rule (which agrees with
  -- the collapse) still sees the composition structure.
  | .vs1 => vneAt fresh (.hcomp .vs1 sys u₀)
  | .vsusp lb a => vneAt fresh (.hcomp (.vsusp lb a) sys u₀)
  | .vtorus => vneAt fresh (.hcomp .vtorus sys u₀)
  | .vtrunc lb a => vneAt fresh (.hcomp (.vtrunc lb a) sys u₀)
  | .vpushout lb a b c f g => vneAt fresh (.hcomp (.vpushout lb a b c f g) sys u₀)
  | .vquot lb a r => vneAt fresh (.hcomp (.vquot lb a r) sys u₀)
  | .vlist _ a => listHcomp fresh a sys u₀
  | .vem1 lb car mul => vneAt fresh (.hcomp (.vem1 lb car mul) sys u₀)
  | .vbgpd lb ob hom cm =>
    vneAt fresh (.hcomp (.vbgpd lb ob hom cm) sys u₀)
  | _ =>
  -- a face that holds identically selects its branch at 1
  match sys.find? (fun (c, _) => cofStatus c == .isTrue) with
  | some (_, br) => capp fresh br (.vi .one)
  | none =>
    -- discard faces that fail identically
    let sys := sys.filter fun (c, _) => !(cofStatus c == .isFalse)
    match force fresh ty with
    | .vpi _ _ cod => vlamAt fresh (.hcompPi cod sys u₀)
    | .vsigma _ d cod =>
      let sysF := sys.map fun (co, br) => (co, Closure.mapFst br)
      let u0f := vfst fresh u₀
      let fstV := vhcomp fresh d sysF u0f
      let line := Closure.comp cod (.hfill d sysF u0f)
      let sysS := sys.map fun (co, br) => (co, Closure.mapSnd br)
      vpairAt fresh fstV (vcomp fresh line sysS (vsnd fresh u₀))
    | .vpathP _ fam l r => vplamAt fresh (.hcompPathP fam l r sys u₀)
    | .vnat => natHcomp fresh sys u₀
    | .vint => intHcomp fresh sys u₀
    | .vunit => unitHcomp fresh sys u₀
    | .vempty => vneAt fresh (.hcomp .vempty sys u₀)
    | .vsum _ sl sr => sumHcomp fresh sl sr sys u₀
    | .vglueTy _ _ _ => vneAt fresh (.hcomp ty sys u₀)   -- hcomp at Glue: out of scope
    | .vne _ _ => vneAt fresh (.hcomp ty sys u₀)
    | _ => panic! "vhcomp: not a composable type"

/-- `hcomp` at `ℕ`: `zero` and `succ` commute with composition. -/
partial def natHcomp (fresh : Nat) (sys : List (VCof × Closure)) (u₀ : Val) : Val :=
  let genericIs (pred : Val → Bool) (br : Closure) : Bool :=
    pred (capp (fresh + 1) br (.vi (.var fresh)))
  match u₀ with
  | .vzero =>
    if sys.all (fun (_, br) => genericIs (· matches .vzero) br) then .vzero
    else vneAt fresh (.hcomp .vnat sys u₀)
  | .vsucc _ v =>
    if sys.all (fun (_, br) => genericIs (· matches .vsucc _ _) br) then
      vsuccAt fresh (vhcomp fresh .vnat (sys.map fun (co, br) => (co, .natPred br)) v)
    else vneAt fresh (.hcomp .vnat sys u₀)
  | _ => vneAt fresh (.hcomp .vnat sys u₀)

/-- `hcomp` at ℤ: `ipos`/`inegsuc` commute with composition (into ℕ). -/
partial def intHcomp (fresh : Nat) (sys : List (VCof × Closure)) (u₀ : Val) : Val :=
  let genericIs (pred : Val → Bool) (br : Closure) : Bool :=
    pred (force (fresh + 1) (capp (fresh + 1) br (.vi (.var fresh))))
  match force fresh u₀ with
  | .vipos _ v =>
    if sys.all (fun (_, br) => genericIs (· matches .vipos _ _) br) then
      viposAt fresh (vhcomp fresh .vnat (sys.map fun (co, br) => (co, .iposArg br)) v)
    else vneAt fresh (.hcomp .vint sys u₀)
  | .vinegsuc _ v =>
    if sys.all (fun (_, br) => genericIs (· matches .vinegsuc _ _) br) then
      vinegsucAt fresh (vhcomp fresh .vnat
        (sys.map fun (co, br) => (co, .inegsucArg br)) v)
    else vneAt fresh (.hcomp .vint sys u₀)
  | _ => vneAt fresh (.hcomp .vint sys u₀)

/-- `hcomp` at sums: `inl`/`inr` commute with composition. -/
partial def sumHcomp (fresh : Nat) (sl sr : Val)
    (sys : List (VCof × Closure)) (u₀ : Val) : Val :=
  let genericIs (pred : Val → Bool) (br : Closure) : Bool :=
    pred (force (fresh + 1) (capp (fresh + 1) br (.vi (.var fresh))))
  match force fresh u₀ with
  | .vinl _ v =>
    if sys.all (fun (_, br) => genericIs (· matches .vinl _ _) br) then
      vinlAt fresh (vhcomp fresh sl (sys.map fun (co, br) => (co, .inlArg br)) v)
    else vneAt fresh (.hcomp (vsumAt fresh sl sr) sys u₀)
  | .vinr _ v =>
    if sys.all (fun (_, br) => genericIs (· matches .vinr _ _) br) then
      vinrAt fresh (vhcomp fresh sr (sys.map fun (co, br) => (co, .inrArg br)) v)
    else vneAt fresh (.hcomp (vsumAt fresh sl sr) sys u₀)
  | _ => vneAt fresh (.hcomp (vsumAt fresh sl sr) sys u₀)

/-- `hcomp` at lists: `nil`/`cons` commute with composition. -/
partial def listHcomp (fresh : Nat) (elemTy : Val)
    (sys : List (VCof × Closure)) (u₀ : Val) : Val :=
  let genericIs (pred : Val → Bool) (br : Closure) : Bool :=
    pred (force (fresh + 1) (capp (fresh + 1) br (.vi (.var fresh))))
  match force fresh u₀ with
  | .vlnil =>
    if sys.all (fun (_, br) => genericIs (· matches .vlnil) br) then
      .vlnil
    else vneAt fresh (.hcomp (vlistAt fresh elemTy) sys u₀)
  | .vlcons _ h t =>
    if sys.all (fun (_, br) => genericIs (· matches .vlcons _ _ _) br) then
      vlconsAt fresh
        (vhcomp fresh elemTy (sys.map fun (co, br) => (co, .lheadArg br)) h)
        (vhcomp fresh (vlistAt fresh elemTy)
          (sys.map fun (co, br) => (co, .ltailArg br)) t)
    else vneAt fresh (.hcomp (vlistAt fresh elemTy) sys u₀)
  | _ => vneAt fresh (.hcomp (vlistAt fresh elemTy) sys u₀)

/-- `hcomp` at ⊤. -/
partial def unitHcomp (fresh : Nat) (sys : List (VCof × Closure)) (u₀ : Val) : Val :=
  let genericIs (pred : Val → Bool) (br : Closure) : Bool :=
    pred (force (fresh + 1) (capp (fresh + 1) br (.vi (.var fresh))))
  match force fresh u₀ with
  | .vtt =>
    if sys.all (fun (_, br) => genericIs (· matches .vtt) br) then .vtt
    else vneAt fresh (.hcomp .vunit sys u₀)
  | _ => vneAt fresh (.hcomp .vunit sys u₀)

/-- The filler of a composition:
`hfill ty [φ ↦ u] u₀ i = hcomp ty [φ ↦ (λ i', u (i' ∧ i)), (i=0) ↦ u₀] u₀`,
so that `hfill 0 = u₀` and `hfill 1 = hcomp`. -/
partial def hfillAt (fresh : Nat) (ty : Val) (sys : List (VCof × Closure))
    (u₀ : Val) (i : IVal) : Val :=
  vhcomp fresh ty
    ((sys.map fun (co, br) => (co, Closure.reparam br (fun i' => IVal.iMin i' i)))
      ++ [([(i, false)], .constV u₀)])
    u₀

/-- Heterogeneous composition, reduced to `hcomp` + `transp` (CCHM):
`comp L [φ ↦ u] u₀ = hcomp (L 1) [φ ↦ (λ i, transp (λ i', L (i ∨ i')) (u i))] (transp L u₀)`. -/
partial def vcomp (fresh : Nat) (line : Closure) (sys : List (VCof × Closure))
    (u₀ : Val) : Val :=
  vhcomp fresh (capp fresh line (.vi .one))
    (sys.map fun (co, br) => (co, Closure.compTube line br))
    (vtransp fresh line u₀)

-- Quotation (readback)

partial def quote (depth : Nat) (v : Val) : Term :=
  match force depth v with
  | .vuniv n => .univ n
  | .vnat => .nat
  | .vzero => .zero
  | .vsucc _ n => .succ (quote depth n)
  | .vint => .int
  | .vipos _ n => .ipos (quote depth n)
  | .vinegsuc _ n => .inegsuc (quote depth n)
  | .vunit => .unit
  | .vtt => .tt
  | .vempty => .empty
  | .vsum _ l r => .sum (quote depth l) (quote depth r)
  | .vinl _ t => .inl (quote depth t)
  | .vinr _ t => .inr (quote depth t)
  | .vs1 => .s1
  | .vsbase => .sbase
  | .vsloop r => .sloop (quoteIVal depth r)
  | .vsusp _ a => .susp (quote depth a)
  | .vnorth => .north
  | .vsouth => .south
  | .vmerid _ a r => .merid (quote depth a) (quoteIVal depth r)
  | .vpushout _ a b c f g =>
    .pushout (quote depth a) (quote depth b) (quote depth c)
      (quote depth f) (quote depth g)
  | .vpinl _ t => .pinl (quote depth t)
  | .vpinr _ t => .pinr (quote depth t)
  | .vppush _ f g c r =>
    .ppush (quote depth f) (quote depth g) (quote depth c)
      (quoteIVal depth r)
  | .vem1 _ car mul => .em1 (quote depth car) (quote depth mul)
  | .vembase => .embase
  | .vemloop _ g r => .emloop (quote depth g) (quoteIVal depth r)
  | .vemcomp _ mul g h rj ri =>
    .emcomp (quote depth mul) (quote depth g) (quote depth h)
      (quoteIVal depth rj) (quoteIVal depth ri)
  | .vemsquash _ x y p q u v r1 r2 r3 =>
    .emsquash (quote depth x) (quote depth y) (quote depth p)
      (quote depth q) (quote depth u) (quote depth v)
      (quoteIVal depth r1) (quoteIVal depth r2) (quoteIVal depth r3)
  | .vbgpd _ ob hom cm =>
    .bgpd (quote depth ob) (quote depth hom) (quote depth cm)
  | .vbpt _ t => .bpt (quote depth t)
  | .vbarr _ x y f r =>
    .barr (quote depth x) (quote depth y) (quote depth f)
      (quoteIVal depth r)
  | .vbcomp _ cm x y z f g rj ri =>
    .bcomp (quote depth cm) (quote depth x) (quote depth y)
      (quote depth z) (quote depth f) (quote depth g)
      (quoteIVal depth rj) (quoteIVal depth ri)
  | .vbsquash _ x y p q u v r1 r2 r3 =>
    .bsquash (quote depth x) (quote depth y) (quote depth p)
      (quote depth q) (quote depth u) (quote depth v)
      (quoteIVal depth r1) (quoteIVal depth r2) (quoteIVal depth r3)
  | .vlist _ a => .list (quote depth a)
  | .vlnil => .lnil
  | .vlcons _ h t => .lcons (quote depth h) (quote depth t)
  | .vquot _ a r => .quot (quote depth a) (quote depth r)
  | .vqin _ t => .qin (quote depth t)
  | .vqeq _ a b w r =>
    .qeq (quote depth a) (quote depth b) (quote depth w)
      (quoteIVal depth r)
  | .vqsquash _ x y p q r s =>
    .qsquash (quote depth x) (quote depth y) (quote depth p)
      (quote depth q) (quoteIVal depth r) (quoteIVal depth s)
  | .vtrunc _ a => .trunc (quote depth a)
  | .vtin _ t => .tin (quote depth t)
  | .vsquash _ x y r =>
    .squash (quote depth x) (quote depth y) (quoteIVal depth r)
  | .vtorus => .torus
  | .vtbase => .tbase
  | .vtloopP r => .tloopP (quoteIVal depth r)
  | .vtloopQ r => .tloopQ (quoteIVal depth r)
  | .vtsurf r s => .tsurf (quoteIVal depth r) (quoteIVal depth s)
  | .vpi _ d c => .pi (quote depth d) (quoteBinder depth c)
  | .vlam _ c => .lam (quoteBinder depth c)
  | .vsigma _ d c => .sigma (quote depth d) (quoteBinder depth c)
  | .vpair _ a b => .pair (quote depth a) (quote depth b)
  | .vpathP _ f l r => .pathP (quoteIBinder depth f) (quote depth l) (quote depth r)
  | .vplam _ c => .plam (quoteIBinder depth c)
  | .vi r => quoteIVal depth r
  | .vglueTy _ sys base =>
    .glueTy
      (sys.map fun (co, T, e) => (quoteCof depth co, quote depth T, quote depth e))
      (quote depth base)
  | .vglue _ ty sys base =>
    .glueTm (quote depth ty)
      (sys.map fun (co, t) => (quoteCof depth co, quote depth t))
      (quote depth base)
  | .vne _ n => quoteNe depth n

partial def quoteCof (depth : Nat) (co : VCof) : List (Term × Bool) :=
  co.map fun (r, b) => (quoteIVal depth r, b)

/-- Quote a closure under a fresh *term* variable. -/
partial def quoteBinder (depth : Nat) (c : Closure) : Term :=
  quote (depth + 1) (capp (depth + 1) c (vneAt depth (.var depth)))

/-- Quote a closure under a fresh *interval* variable. -/
partial def quoteIBinder (depth : Nat) (c : Closure) : Term :=
  quote (depth + 1) (capp (depth + 1) c (.vi (.var depth)))

partial def quoteIVal (depth : Nat) : IVal → Term
  | .zero => .i0
  | .one => .i1
  | .var l => .var (depth - 1 - l)
  | .max a b => .imax (quoteIVal depth a) (quoteIVal depth b)
  | .min a b => .imin (quoteIVal depth a) (quoteIVal depth b)
  | .neg a => .ineg (quoteIVal depth a)

partial def quoteSys (depth : Nat) (sys : List (VCof × Closure)) :
    List (List (Term × Bool) × Term) :=
  sys.map fun (co, br) => (quoteCof depth co, quoteIBinder depth br)

partial def quoteNe (depth : Nat) : Neutral → Term
  | .var l => .var (depth - 1 - l)
  | .app f a => .app (quoteNe depth f) (quote depth a)
  | .fst p => .fst (quoteNe depth p)
  | .snd p => .snd (quoteNe depth p)
  | .natrec m z s n =>
    .natrec (quoteBinder depth m) (quote depth z) (quote depth s) (quoteNe depth n)
  | .papp p l r s =>
    .papp (quoteNe depth p) (quote depth l) (quote depth r) (quoteIVal depth s)
  | .transp f a => .transp (quoteIBinder depth f) (quote depth a)
  | .hcomp ty sys u₀ =>
    .hcomp (quote depth ty) (quoteSys depth sys) (quote depth u₀)
  | .unglue ty b => .unglue (quote depth ty) (quoteNe depth b)
  | .s1elim m b l t =>
    .s1elim (quoteBinder depth m) (quote depth b) (quote depth l) (quoteNe depth t)
  | .intcase m fp fn t =>
    .intcase (quoteBinder depth m) (quote depth fp) (quote depth fn)
      (quoteNe depth t)
  | .unitrec m pt t =>
    .unitrec (quoteBinder depth m) (quote depth pt) (quoteNe depth t)
  | .emptyrec ty t => .emptyrec (quote depth ty) (quoteNe depth t)
  | .sumcase m fl fr t =>
    .sumcase (quoteBinder depth m) (quote depth fl) (quote depth fr)
      (quoteNe depth t)
  | .susprec m nc sc mc t =>
    .susprec (quoteBinder depth m) (quote depth nc) (quote depth sc)
      (quote depth mc) (quoteNe depth t)
  | .torusrec m bc pc qc sc t =>
    .torusrec (quoteBinder depth m) (quote depth bc) (quote depth pc)
      (quote depth qc) (quote depth sc) (quoteNe depth t)
  | .truncrec mB prp f t =>
    .truncrec (quote depth mB) (quote depth prp) (quote depth f)
      (quoteNe depth t)
  | .pushrec m lc rc pc t =>
    .pushrec (quoteBinder depth m) (quote depth lc) (quote depth rc)
      (quote depth pc) (quoteNe depth t)
  | .qelim m mset f feq t =>
    .qelim (quoteBinder depth m) (quote depth mset) (quote depth f)
      (quote depth feq) (quoteNe depth t)
  | .listrec m nc cc t =>
    .listrec (quoteBinder depth m) (quote depth nc) (quote depth cc)
      (quoteNe depth t)
  | .em1elim m gP b l c t =>
    .em1elim (quoteBinder depth m) (quote depth gP) (quote depth b)
      (quote depth l) (quote depth c) (quoteNe depth t)
  | .em1rec B gB b l c t =>
    .em1rec (quote depth B) (quote depth gB) (quote depth b)
      (quote depth l) (quote depth c) (quoteNe depth t)
  | .bgrec bT gB pf pl pc t =>
    .bgrec (quote depth bT) (quote depth gB) (quote depth pf)
      (quote depth pl) (quote depth pc) (quoteNe depth t)
  | .bgelim m gP pb pl pc t =>
    .bgelim (quoteBinder depth m) (quote depth gP) (quote depth pb)
      (quote depth pl) (quote depth pc) (quoteNe depth t)
  | .emsquashCell x y p q u v r1 r2 r3 =>
    .emsquash (quote depth x) (quote depth y) (quote depth p)
      (quote depth q) (quote depth u) (quote depth v)
      (quoteIVal depth r1) (quoteIVal depth r2) (quoteIVal depth r3)
  | .qsquashCell x y p q r s =>
    .qsquash (quote depth x) (quote depth y) (quote depth p)
      (quote depth q) (quoteIVal depth r) (quoteIVal depth s)

-- Occurs-check of a level in a value: mirrors quotation (incl. `force` and
-- the binder instantiation kinds) but allocates no terms and short-circuits
-- on the first occurrence.  Used by the `transp` constancy check.

/-- **Exact read-back support check**: `usesLvl l v = (l ∈ FV(quote v))`.
The traversal mirrors `quote` clause by clause — same `force` at the
head, same structural recursion on value arguments, binder closures
instantiated at generic levels exactly as `quoteBinder`/`quoteIBinder`,
neutral `hcomp` tubes instantiated exactly as `quoteSys` — so the
constancy check implements the paper's representation-independent
specification `const?_spec(F, ℓ) := ℓ ∉ FV(quote F)` *exactly*, not as
an approximation.  The two optimizations are semantically transparent:
the `lb` generation-stamp cut is exact by the depth lemma (`lb` bounds
every free level), and the memo hooks only cache answers.  (A legacy
non-instantiating closure walk (`usesLvlClosure`/`usesLvlSys`) was
unreachable from this entry point and was removed 2026-07-17.) -/
partial def usesLvl (depth : Nat) (l : Nat) (v : Val) : Bool :=
  -- Generation-stamp cut (O(1)): `lb` upper-bounds every free level of a
  -- stamped value (depth lemma), so `l ≥ lb` means `l` cannot occur.
  -- Values pointer-shared out of environments keep their old (small)
  -- stamps — that is what lets the transport constancy check skip
  -- embedded witnesses wholesale.  Slots 6/7 count cut hits/misses.
  match v with
  | .vne lb _ =>
    if l ≥ lb then (if profTick 6 v then panic! "x" else false)
    else if profTick 7 v then panic! "x" else usesLvlRun depth l v
  | .vpi lb _ _ =>
    if l ≥ lb then (if profTick 6 v then panic! "x" else false)
    else if profTick 7 v then panic! "x" else usesLvlRun depth l v
  | .vlam lb _ =>
    if l ≥ lb then (if profTick 6 v then panic! "x" else false)
    else if profTick 7 v then panic! "x" else usesLvlRun depth l v
  | .vsigma lb _ _ =>
    if l ≥ lb then (if profTick 6 v then panic! "x" else false)
    else if profTick 7 v then panic! "x" else usesLvlRun depth l v
  | .vpair lb _ _ =>
    if l ≥ lb then (if profTick 6 v then panic! "x" else false)
    else if profTick 7 v then panic! "x" else usesLvlRun depth l v
  | .vpathP lb _ _ _ =>
    if l ≥ lb then (if profTick 6 v then panic! "x" else false)
    else if profTick 7 v then panic! "x" else usesLvlRun depth l v
  | .vplam lb _ =>
    if l ≥ lb then (if profTick 6 v then panic! "x" else false)
    else if profTick 7 v then panic! "x" else usesLvlRun depth l v
  | _ =>
    if lvlClosedByCache v then false else
    usesLvlMemoVHook l v (fun _ => usesLvlRun depth l v)

partial def usesLvlRun (depth : Nat) (l : Nat) (v : Val) : Bool :=
  match force depth v with
  | .vuniv _ | .vnat | .vzero | .vint | .vunit | .vtt | .vempty
  | .vs1 | .vsbase | .vnorth | .vsouth | .vtorus | .vtbase => false
  | .vsusp _ a => usesLvl depth l a
  | .vmerid _ a r => usesLvl depth l a || r.mentions l
  | .vpushout _ a b c f g =>
    usesLvl depth l a || usesLvl depth l b || usesLvl depth l c
      || usesLvl depth l f || usesLvl depth l g
  | .vpinl _ a | .vpinr _ a => usesLvl depth l a
  | .vppush _ f g c r =>
    usesLvl depth l f || usesLvl depth l g || usesLvl depth l c
      || r.mentions l
  | .vem1 _ car mul => usesLvl depth l car || usesLvl depth l mul
  | .vembase => false
  | .vemloop _ g r => usesLvl depth l g || r.mentions l
  | .vemcomp _ mul g h rj ri =>
    usesLvl depth l mul || usesLvl depth l g || usesLvl depth l h
      || rj.mentions l || ri.mentions l
  | .vemsquash _ x y p q u v r1 r2 r3 =>
    usesLvl depth l x || usesLvl depth l y || usesLvl depth l p
      || usesLvl depth l q || usesLvl depth l u || usesLvl depth l v
      || r1.mentions l || r2.mentions l || r3.mentions l
  | .vbgpd _ ob hom cm =>
    usesLvl depth l ob || usesLvl depth l hom || usesLvl depth l cm
  | .vbpt _ t => usesLvl depth l t
  | .vbarr _ x y f r =>
    usesLvl depth l x || usesLvl depth l y || usesLvl depth l f
      || r.mentions l
  | .vbcomp _ cm x y z f g rj ri =>
    usesLvl depth l cm || usesLvl depth l x || usesLvl depth l y
      || usesLvl depth l z || usesLvl depth l f || usesLvl depth l g
      || rj.mentions l || ri.mentions l
  | .vbsquash _ x y p q u v r1 r2 r3 =>
    usesLvl depth l x || usesLvl depth l y || usesLvl depth l p
      || usesLvl depth l q || usesLvl depth l u || usesLvl depth l v
      || r1.mentions l || r2.mentions l || r3.mentions l
  | .vlist _ a => usesLvl depth l a
  | .vlnil => false
  | .vlcons _ h t => usesLvl depth l h || usesLvl depth l t
  | .vquot _ a r => usesLvl depth l a || usesLvl depth l r
  | .vqin _ a => usesLvl depth l a
  | .vqeq _ a b w r =>
    usesLvl depth l a || usesLvl depth l b || usesLvl depth l w
      || r.mentions l
  | .vqsquash _ x y p q r s =>
    usesLvl depth l x || usesLvl depth l y || usesLvl depth l p
      || usesLvl depth l q || r.mentions l || s.mentions l
  | .vtrunc _ a => usesLvl depth l a
  | .vtin _ a => usesLvl depth l a
  | .vsquash _ x y r =>
    usesLvl depth l x || usesLvl depth l y || r.mentions l
  | .vtloopP r | .vtloopQ r => r.mentions l
  | .vtsurf r s => r.mentions l || s.mentions l
  | .vsucc _ n | .vipos _ n | .vinegsuc _ n | .vinl _ n | .vinr _ n => usesLvl depth l n
  | .vsum _ a b => usesLvl depth l a || usesLvl depth l b
  | .vsloop r => r.mentions l
  | .vpi _ d c => usesLvl depth l d || usesLvlBinder depth l c
  | .vlam _ c => usesLvlBinder depth l c
  | .vsigma _ d c => usesLvl depth l d || usesLvlBinder depth l c
  | .vpair _ a b => usesLvl depth l a || usesLvl depth l b
  | .vpathP _ f lh rh =>
    usesLvlIBinder depth l f || usesLvl depth l lh || usesLvl depth l rh
  | .vplam _ c => usesLvlIBinder depth l c
  | .vi r => r.mentions l
  | .vglueTy _ sys base =>
    usesLvl depth l base ||
      sys.any fun (co, T, e) =>
        usesLvlCof l co || usesLvl depth l T || usesLvl depth l e
  | .vglue _ ty sys base =>
    usesLvl depth l ty || usesLvl depth l base ||
      sys.any fun (co, t) => usesLvlCof l co || usesLvl depth l t
  | .vne _ n => usesLvlNe depth l n


partial def usesLvlBinder (depth : Nat) (l : Nat) (c : Closure) : Bool :=
  usesLvl (depth + 1) l (capp (depth + 1) c (vneAt depth (.var depth)))

partial def usesLvlIBinder (depth : Nat) (l : Nat) (c : Closure) : Bool :=
  usesLvl (depth + 1) l (capp (depth + 1) c (.vi (.var depth)))

partial def usesLvlCof (l : Nat) (co : VCof) : Bool :=
  co.any fun (r, _) => r.mentions l

partial def usesLvlNe (depth : Nat) (l : Nat) (n : Neutral) : Bool :=
  usesLvlMemoNHook l n (fun _ => usesLvlNeRun depth l n)

partial def usesLvlNeRun (depth : Nat) (l : Nat) (n : Neutral) : Bool :=
  match n with
  | .var lvl => lvl == l
  | .app f a => usesLvlNe depth l f || usesLvl depth l a
  | .fst p => usesLvlNe depth l p
  | .snd p => usesLvlNe depth l p
  | .natrec m z s t =>
    usesLvlBinder depth l m || usesLvl depth l z || usesLvl depth l s
      || usesLvlNe depth l t
  | .papp p lh rh r =>
    usesLvlNe depth l p || usesLvl depth l lh || usesLvl depth l rh
      || r.mentions l
  | .transp f a => usesLvlIBinder depth l f || usesLvl depth l a
  | .hcomp ty sys u₀ =>
    usesLvl depth l ty || usesLvl depth l u₀ ||
      sys.any fun (co, br) => usesLvlCof l co || usesLvlIBinder depth l br
  | .unglue ty b => usesLvl depth l ty || usesLvlNe depth l b
  | .s1elim m b lv t =>
    usesLvlBinder depth l m || usesLvl depth l b || usesLvl depth l lv
      || usesLvlNe depth l t
  | .intcase m fp fn t =>
    usesLvlBinder depth l m || usesLvl depth l fp || usesLvl depth l fn
      || usesLvlNe depth l t
  | .unitrec m pt t =>
    usesLvlBinder depth l m || usesLvl depth l pt || usesLvlNe depth l t
  | .emptyrec ty t => usesLvl depth l ty || usesLvlNe depth l t
  | .sumcase m fl fr t =>
    usesLvlBinder depth l m || usesLvl depth l fl || usesLvl depth l fr
      || usesLvlNe depth l t
  | .susprec m nc sc mc t =>
    usesLvlBinder depth l m || usesLvl depth l nc || usesLvl depth l sc
      || usesLvl depth l mc || usesLvlNe depth l t
  | .torusrec m bc pc qc sc t =>
    usesLvlBinder depth l m || usesLvl depth l bc || usesLvl depth l pc
      || usesLvl depth l qc || usesLvl depth l sc || usesLvlNe depth l t
  | .truncrec mB prp f t =>
    usesLvl depth l mB || usesLvl depth l prp || usesLvl depth l f
      || usesLvlNe depth l t
  | .pushrec m lc rc pc t =>
    usesLvlBinder depth l m || usesLvl depth l lc || usesLvl depth l rc
      || usesLvl depth l pc || usesLvlNe depth l t
  | .qelim m mset f feq t =>
    usesLvlBinder depth l m || usesLvl depth l mset || usesLvl depth l f
      || usesLvl depth l feq || usesLvlNe depth l t
  | .em1elim m gP b l2 c t =>
    usesLvlBinder depth l m || usesLvl depth l gP || usesLvl depth l b
      || usesLvl depth l l2 || usesLvl depth l c || usesLvlNe depth l t
  | .em1rec B gB b l2 c t =>
    usesLvl depth l B || usesLvl depth l gB || usesLvl depth l b
      || usesLvl depth l l2 || usesLvl depth l c || usesLvlNe depth l t
  | .bgrec bT gB pf pl pc t =>
    usesLvl depth l bT || usesLvl depth l gB || usesLvl depth l pf
      || usesLvl depth l pl || usesLvl depth l pc || usesLvlNe depth l t
  | .bgelim m gP pb pl pc t =>
    usesLvlBinder depth l m || usesLvl depth l gP || usesLvl depth l pb
      || usesLvl depth l pl || usesLvl depth l pc || usesLvlNe depth l t
  | .emsquashCell x y p q u v r1 r2 r3 =>
    usesLvl depth l x || usesLvl depth l y || usesLvl depth l p
      || usesLvl depth l q || usesLvl depth l u || usesLvl depth l v
      || r1.mentions l || r2.mentions l || r3.mentions l
  | .listrec m nc cc t =>
    usesLvlBinder depth l m || usesLvl depth l nc || usesLvl depth l cc
      || usesLvlNe depth l t
  | .qsquashCell x y p q r s =>
    usesLvl depth l x || usesLvl depth l y || usesLvl depth l p
      || usesLvl depth l q || r.mentions l || s.mentions l

end

/-- Canonicalize one face constraint `(r = ε)` into atomic literals where
possible.  The constraint is read as `s = 1` with `s := r` or `¬r`; if the
canonical DNF of `s` is a single clause, `⋀ lᵢ = 1` splits into one atomic
literal per `lᵢ` (so `(¬k = 1)` becomes `(k = 0)`, `(i∧j = 1)` becomes
`(i = 1) ∧ (j = 1)`); a satisfied constraint yields no literals; otherwise
the constraint is kept whole with canonical polarity/expression.  All are
logical equivalences, so conversion only identifies more faces. -/
def normCofLit (r : IVal) (b : Bool) : VCof :=
  let s := if b then r else r.iNeg
  match s.dnf with
  | [clause] => clause.map fun (v, neg) => (IVal.var v, !neg)
  | d => [(IVal.fromDnf d, true)]

/-- Sort key for canonical literal order. -/
def cofLitKey : IVal × Bool → List Nat
  | (r, b) => (if b then r else r.iNeg).dnf.map IVal.clauseListKey |>.flatten

def cofLitInsert (l : IVal × Bool) : VCof → VCof
  | [] => [l]
  | x :: xs =>
    if IVal.keysLt (cofLitKey l) (cofLitKey x) then l :: x :: xs
    else if cofLitKey l == cofLitKey x && l.2 == x.2 && l.1.equiv x.1 then
      x :: xs
    else x :: cofLitInsert l xs

/-- Full face normalization: split into canonical atomic literals, drop
satisfied ones, deduplicate, and sort. -/
def normCof (c : VCof) : VCof :=
  let lits := (c.map fun (r, b) => normCofLit r b).flatten
  lits.foldr cofLitInsert []

/-- Drop identically-false branches and normalize the faces of a system. -/
def normSys (sys : List (VCof × Closure)) : List (VCof × Closure) :=
  (sys.filter fun (co, _) => !(cofStatus co == .isFalse)).map
    fun (co, br) => (normCof co, br)

/-- Pointer equality on values (sound to use as a conversion
short-circuit: physically equal values are convertible).  Implemented by
address comparison; the pure model conservatively answers `false`. -/
unsafe def valPtrEqUnsafe (a b : Val) : Bool :=
  ptrAddrUnsafe a == ptrAddrUnsafe b
@[implemented_by valPtrEqUnsafe]
opaque valPtrEq (_ _ : Val) : Bool

unsafe def nePtrEqUnsafe (a b : Neutral) : Bool :=
  ptrAddrUnsafe a == ptrAddrUnsafe b
@[implemented_by nePtrEqUnsafe]
opaque nePtrEq (_ _ : Neutral) : Bool

unsafe def cloPtrEqUnsafe (a b : Closure) : Bool :=
  ptrAddrUnsafe a == ptrAddrUnsafe b
@[implemented_by cloPtrEqUnsafe]
opaque cloPtrEq (_ _ : Closure) : Bool

/-! ## Conversion checking -/


mutual

/-- Untyped conversion with η for functions, pairs, and paths.
Interval components are compared semantically (canonical DNF); `Glue` face
reductions are applied by `force` before comparing. -/
partial def conv (depth : Nat) (v w : Val) : Bool :=
  convMemoHook depth v w (fun _ => convRun depth v w)

partial def convRun (depth : Nat) (v w : Val) : Bool :=
  match force depth v, force depth w with
  | .vuniv n, .vuniv m => n == m
  | .vnat, .vnat => true
  | .vzero, .vzero => true
  | .vsucc _ a, .vsucc _ b => conv depth a b
  | .vint, .vint => true
  | .vipos _ a, .vipos _ b => conv depth a b
  | .vinegsuc _ a, .vinegsuc _ b => conv depth a b
  | .vunit, .vunit => true
  | .vtt, .vtt => true
  | .vempty, .vempty => true
  | .vsum _ l r, .vsum _ l' r' => conv depth l l' && conv depth r r'
  | .vinl _ a, .vinl _ b => conv depth a b
  | .vinr _ a, .vinr _ b => conv depth a b
  | .vs1, .vs1 => true
  | .vsbase, .vsbase => true
  | .vsloop r, .vsloop s => r.equiv s
  | .vsusp _ a, .vsusp _ b => conv depth a b
  | .vnorth, .vnorth => true
  | .vsouth, .vsouth => true
  | .vmerid _ a r, .vmerid _ b s => conv depth a b && r.equiv s
  | .vpushout _ a b c f g, .vpushout _ a' b' c' f' g' =>
    conv depth a a' && conv depth b b' && conv depth c c'
      && conv depth f f' && conv depth g g'
  | .vpinl _ a, .vpinl _ b => conv depth a b
  | .vpinr _ a, .vpinr _ b => conv depth a b
  | .vppush _ _ _ c r, .vppush _ _ _ c' r' => conv depth c c' && r.equiv r'
  | .vem1 _ c m, .vem1 _ c' m' => conv depth c c' && conv depth m m'
  | .vbgpd _ ob hom cm, .vbgpd _ ob' hom' cm' =>
    conv depth ob ob' && conv depth hom hom' && conv depth cm cm'
  | .vbpt _ t, .vbpt _ t' => conv depth t t'
  | .vbarr _ x y f r, .vbarr _ x' y' f' r' =>
    conv depth x x' && conv depth y y' && conv depth f f' && r.equiv r'
  | .vbcomp _ _ x y z f g rj ri, .vbcomp _ _ x' y' z' f' g' rj' ri' =>
    conv depth x x' && conv depth y y' && conv depth z z'
      && conv depth f f' && conv depth g g'
      && rj.equiv rj' && ri.equiv ri'
  | .vbsquash _ x y p q u v r1 r2 r3,
      .vbsquash _ x' y' p' q' u' v' r1' r2' r3' =>
    conv depth x x' && conv depth y y' && conv depth p p'
      && conv depth q q' && conv depth u u' && conv depth v v'
      && r1.equiv r1' && r2.equiv r2' && r3.equiv r3'
  | .vembase, .vembase => true
  | .vemloop _ g r, .vemloop _ g' r' => conv depth g g' && r.equiv r'
  | .vemcomp _ _ g h rj ri, .vemcomp _ _ g' h' rj' ri' =>
    conv depth g g' && conv depth h h' && rj.equiv rj' && ri.equiv ri'
  | .vemsquash _ x y p q u v r1 r2 r3,
      .vemsquash _ x' y' p' q' u' v' r1' r2' r3' =>
    conv depth x x' && conv depth y y' && conv depth p p'
      && conv depth q q' && conv depth u u' && conv depth v v'
      && r1.equiv r1' && r2.equiv r2' && r3.equiv r3'
  | .vlist _ a, .vlist _ b => conv depth a b
  | .vlnil, .vlnil => true
  | .vlcons _ h t, .vlcons _ h' t' => conv depth h h' && conv depth t t'
  | .vquot _ a r, .vquot _ a' r' => conv depth a a' && conv depth r r'
  | .vqin _ a, .vqin _ b => conv depth a b
  | .vqeq _ a b w r, .vqeq _ a' b' w' r' =>
    conv depth a a' && conv depth b b' && conv depth w w' && r.equiv r'
  | .vqsquash _ x y p q r s, .vqsquash _ x' y' p' q' r' s' =>
    conv depth x x' && conv depth y y' && conv depth p p'
      && conv depth q q' && r.equiv r' && s.equiv s'
  | .vtrunc _ a, .vtrunc _ b => conv depth a b
  | .vtin _ a, .vtin _ b => conv depth a b
  | .vsquash _ x y r, .vsquash _ x' y' r' =>
    conv depth x x' && conv depth y y' && r.equiv r'
  | .vtorus, .vtorus => true
  | .vtbase, .vtbase => true
  | .vtloopP r, .vtloopP s => r.equiv s
  | .vtloopQ r, .vtloopQ s => r.equiv s
  | .vtsurf r s, .vtsurf r' s' => r.equiv r' && s.equiv s' 
  | .vpi _ d c, .vpi _ d' c' => conv depth d d' && convBinder depth c c'
  | .vsigma _ d c, .vsigma _ d' c' => conv depth d d' && convBinder depth c c'
  | .vpathP _ f l r, .vpathP _ f' l' r' =>
    convIBinder depth f f' && conv depth l l' && conv depth r r'
  | .vi r, .vi s => r.equiv s
  | .vlam _ c, .vlam _ c' => convBinder depth c c'
  | .vlam _ c, w =>
    let g : Val := vneAt depth (.var depth)
    conv (depth + 1) (capp (depth + 1) c g) (vapp (depth + 1) w g)
  | v, .vlam _ c' =>
    let g : Val := vneAt depth (.var depth)
    conv (depth + 1) (vapp (depth + 1) v g) (capp (depth + 1) c' g)
  | .vpair _ a b, .vpair _ a' b' => conv depth a a' && conv depth b b'
  | .vpair _ a b, w => conv depth a (vfst depth w) && conv depth b (vsnd depth w)
  | v, .vpair _ a' b' => conv depth (vfst depth v) a' && conv depth (vsnd depth v) b'
  | .vplam _ c, .vplam _ c' => convIBinder depth c c'
  | .vplam _ c, w =>
    -- η for paths; the endpoint annotations of the neutral side are dummies,
    -- harmless because neutral `papp` comparison ignores the annotations.
    let g : IVal := .var depth
    conv (depth + 1) (capp (depth + 1) c (.vi g)) (vpappEta (depth + 1) w g)
  | v, .vplam _ c' =>
    let g : IVal := .var depth
    conv (depth + 1) (vpappEta (depth + 1) v g) (capp (depth + 1) c' (.vi g))
  | .vglueTy _ sys base, .vglueTy _ sys' base' =>
    conv depth base base' && convGlueSys depth sys sys'
  | .vglue _ _ sys base, .vglue _ _ sys' base' =>
    -- the type tags agree by typing; compare branches and base
    conv depth base base'
      && sys.length == sys'.length
      && (sys.zip sys').all fun ((co, t), (co', t')) =>
        convCof co co' && conv depth t t'
  | .vne _ n, .vne _ n' => convNe depth n n'
  | _, _ => false

partial def convCof (co co' : VCof) : Bool :=
  co.length == co'.length
    && (co.zip co').all fun ((r, b), (r', b')) => b == b' && r.equiv r'

partial def convGlueSys (depth : Nat) :
    List (VCof × Val × Val) → List (VCof × Val × Val) → Bool
  | [], [] => true
  | (co, T, e) :: s, (co', T', e') :: s' =>
    convCof co co' && conv depth T T' && conv depth e e' && convGlueSys depth s s'
  | _, _ => false

/-- Apply a path value at a *generic* interval point (never an endpoint),
for η-expansion during conversion. -/
partial def vpappEta (fresh : Nat) (p : Val) (r : IVal) : Val :=
  match p with
  | .vplam _ c => capp fresh c (.vi r)
  | .vne _ n => vneAt fresh (.papp n (.vuniv 0) (.vuniv 0) r)  -- dummy endpoints, see above
  | _ => panic! "vpappEta: not a path"

partial def convBinder (depth : Nat) (c c' : Closure) : Bool :=
  if cloPtrEq c c' then true else
  let g : Val := vneAt depth (.var depth)
  conv (depth + 1) (capp (depth + 1) c g) (capp (depth + 1) c' g)

partial def convIBinder (depth : Nat) (c c' : Closure) : Bool :=
  if cloPtrEq c c' then true else
  let g : Val := .vi (.var depth)
  conv (depth + 1) (capp (depth + 1) c g) (capp (depth + 1) c' g)

/-- Compare systems branchwise, in order, after dropping identically-false
branches and normalizing faces (see `normSys`).  (Sound but incomplete:
systems that differ by permutation are not identified.) -/
partial def convSys (depth : Nat) (sys sys' : List (VCof × Closure)) : Bool :=
  convSysGo depth (normSys sys) (normSys sys')

partial def convSysGo (depth : Nat) :
    List (VCof × Closure) → List (VCof × Closure) → Bool
  | [], [] => true
  | (co, br) :: s, (co', br') :: s' =>
    convCof co co' && convIBinder depth br br' && convSysGo depth s s'
  | _, _ => false

partial def convNe (depth : Nat) (n n' : Neutral) : Bool :=
  if nePtrEq n n' then true else
  match n, n' with
  | .var l, .var l' => l == l'
  | .app f a, .app f' a' => convNe depth f f' && conv depth a a'
  | .fst p, .fst p' => convNe depth p p'
  | .snd p, .snd p' => convNe depth p p'
  | .natrec m z s t, .natrec m' z' s' t' =>
    convBinder depth m m' && conv depth z z' && conv depth s s' && convNe depth t t'
  -- endpoint annotations are determined by the type of `p`: not compared.
  | .papp p _ _ r, .papp p' _ _ r' => convNe depth p p' && r.equiv r'
  | .transp f a, .transp f' a' => convIBinder depth f f' && conv depth a a'
  | .hcomp ty sys u₀, .hcomp ty' sys' u₀' =>
    conv depth ty ty' && convSys depth sys sys' && conv depth u₀ u₀'
  -- the Glue-type tag is determined by the type of `b`: not compared.
  | .unglue _ b, .unglue _ b' => convNe depth b b'
  | .s1elim m b l t, .s1elim m' b' l' t' =>
    convBinder depth m m' && conv depth b b' && conv depth l l' && convNe depth t t'
  | .intcase m fp fn t, .intcase m' fp' fn' t' =>
    convBinder depth m m' && conv depth fp fp' && conv depth fn fn'
      && convNe depth t t'
  | .unitrec m pt t, .unitrec m' pt' t' =>
    convBinder depth m m' && conv depth pt pt' && convNe depth t t'
  | .emptyrec ty t, .emptyrec ty' t' =>
    conv depth ty ty' && convNe depth t t'
  | .sumcase m fl fr t, .sumcase m' fl' fr' t' =>
    convBinder depth m m' && conv depth fl fl' && conv depth fr fr'
      && convNe depth t t'
  | .susprec m nc sc mc t, .susprec m' nc' sc' mc' t' =>
    convBinder depth m m' && conv depth nc nc' && conv depth sc sc'
      && conv depth mc mc' && convNe depth t t'
  | .torusrec m bc pc qc sc t, .torusrec m' bc' pc' qc' sc' t' =>
    convBinder depth m m' && conv depth bc bc' && conv depth pc pc'
      && conv depth qc qc' && conv depth sc sc' && convNe depth t t'
  | .truncrec mB prp f t, .truncrec mB' prp' f' t' =>
    conv depth mB mB' && conv depth prp prp' && conv depth f f'
      && convNe depth t t'
  | .pushrec m lc rc pc t, .pushrec m' lc' rc' pc' t' =>
    convBinder depth m m' && conv depth lc lc' && conv depth rc rc'
      && conv depth pc pc' && convNe depth t t'
  | .qelim m mset f feq t, .qelim m' mset' f' feq' t' =>
    convBinder depth m m' && conv depth mset mset' && conv depth f f'
      && conv depth feq feq' && convNe depth t t'
  | .em1elim m gP b l c t, .em1elim m' gP' b' l' c' t' =>
    convBinder depth m m' && conv depth gP gP' && conv depth b b'
      && conv depth l l' && conv depth c c' && convNe depth t t'
  | .em1rec B gB b l c t, .em1rec B' gB' b' l' c' t' =>
    conv depth B B' && conv depth gB gB' && conv depth b b'
      && conv depth l l' && conv depth c c' && convNe depth t t'
  | .bgrec bT gB pf pl pc t, .bgrec bT' gB' pf' pl' pc' t' =>
    conv depth bT bT' && conv depth gB gB' && conv depth pf pf'
      && conv depth pl pl' && conv depth pc pc' && convNe depth t t'
  | .bgelim m gP pb pl pc t, .bgelim m' gP' pb' pl' pc' t' =>
    convBinder depth m m' && conv depth gP gP' && conv depth pb pb'
      && conv depth pl pl' && conv depth pc pc' && convNe depth t t'
  | .emsquashCell x y p q u v r1 r2 r3,
      .emsquashCell x' y' p' q' u' v' r1' r2' r3' =>
    conv depth x x' && conv depth y y' && conv depth p p'
      && conv depth q q' && conv depth u u' && conv depth v v'
      && r1.equiv r1' && r2.equiv r2' && r3.equiv r3'
  | .listrec m nc cc t, .listrec m' nc' cc' t' =>
    convBinder depth m m' && conv depth nc nc' && conv depth cc cc'
      && convNe depth t t'
  | .qsquashCell x y p q r s, .qsquashCell x' y' p' q' r' s' =>
    conv depth x x' && conv depth y y' && conv depth p p'
      && conv depth q q' && r.equiv r' && s.equiv s' 
  | _, _ => false

end

/-- Normal form of a closed term. -/
def nf (t : Term) : Term := quote 0 (eval 0 [] t)

end Cubical
