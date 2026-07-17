import FormalizedMathematics.Cubical.Semantics

/-!
# Bidirectional type checker

The context is a telescope whose entries are either term variables (with a
semantic type) or interval variables.  `env` maps each context entry to its
generic value (a neutral variable, resp. a generic interval point), so types
can be evaluated on the fly (standard NbE checking).

Checking `plam` verifies the *boundary conditions*: the body instantiated at
`0` (resp. `1`) must be convertible with the endpoints of the `PathP` type —
this is where "paths" differ from functions out of an abstract interval.

Universes form a hierarchy `univ n : univ (n+1)` with level inference
(`inferSort`) for the type formers and universe subsumption (cumulativity)
at the checking judgement — type-in-type was removed in phase 2c.

Remaining caveats (see README roadmap): no termination guarantee for
evaluation (normalization of cubical type theory is open research), the
surface face syntax is restricted to conjunctions of `(x = ε)`, and system
comparison is order-sensitive (sound but incomplete).
-/

namespace Cubical

instance : Inhabited (Except String α) := ⟨.error "panic"⟩

inductive CtxEntry where
  | tm (ty : Val)
  | itv
  deriving Inhabited

abbrev Ctx := List CtxEntry

/-- Pretty-printer stub: show the quoted normal form. -/
private def showV (depth : Nat) (v : Val) : String := s!"{repr (quote depth v)}"

/-- Interpret an interval *term* over de Bruijn indices as an `IVal`
(indices play the role of variables), for face resolution. -/
private def faceIVal (Γ : Ctx) : Term → Except String IVal
  | .var i =>
    match Γ[i]? with
    | some .itv => .ok (.var i)
    | _ => .error "face must constrain an interval variable"
  | .i0 => .ok .zero
  | .i1 => .ok .one
  | .ineg a => do .ok (IVal.iNeg (← faceIVal Γ a))
  | .imin a b => do .ok (IVal.iMin (← faceIVal Γ a) (← faceIVal Γ b))
  | .imax a b => do .ok (IVal.iMax (← faceIVal Γ a) (← faceIVal Γ b))
  | _ => .error "face must be an interval expression"

/-- Resolve a face (a conjunction of constraints `(r = ε)` over arbitrary
interval expressions) into the *disjuncts of its canonical DNF*: a list of
substitutions on interval variables whose union covers exactly the face.
Checking a branch under each disjunct is sound and complete (the disjuncts
form an open cover of the cofibration by cube faces).  An unsatisfiable
face yields `[]`; an identically-true face yields `[[]]`. -/
private def resolveFace (Γ : Ctx) (cof : List (Term × Bool)) :
    Except String (List (List (Nat × Bool))) := do
  let mut d : IVal.Dnf := [[]]
  for (f, b) in cof do
    let r ← faceIVal Γ f
    let s := if b then r else IVal.iNeg r
    d := IVal.dnfMeet d (IVal.dnf s)
  .ok (d.map fun clause => clause.map fun (v, neg) => (v, !neg))

private def contradictory (subs : List (Nat × Bool)) : Bool :=
  subs.any fun (i, b) => subs.any fun (j, b') => i == j && b != b'

private def restrictEnv (env : List Val) (subs : List (Nat × Bool)) : List Val :=
  subs.foldl (fun e (i, b) => e.set i (.vi (if b then .one else .zero))) env


/-- `isGroupoid` as a closed object-language predicate, used by the
`em1rec` rule (evaluation is type-free, so the rule simply applies it to
the motive value). -/
private def isGpdRaw : Raw :=
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

private def isGpdTm : Term :=
  match isGpdRaw.resolve [] with
  | .ok t => t
  | .error _ => .univ 0

mutual

/-- Check that `t` is a well-formed interval expression. -/
partial def checkI (Γ : Ctx) : Term → Except String Unit
  | .i0 | .i1 => .ok ()
  | .var i =>
    match Γ[i]? with
    | some .itv => .ok ()
    | some (.tm _) => .error s!"variable #{i} is a term variable, not an interval variable"
    | none => .error s!"unbound variable #{i}"
  | .imax l r | .imin l r => do checkI Γ l; checkI Γ r
  | .ineg r => checkI Γ r
  | t => .error s!"not an interval expression: {repr t}"

/-- Check `t` against type `ty` (a value). -/
partial def check (Γ : Ctx) (env : List Val) (t : Term) (ty : Val) :
    Except String Unit := do
  let depth := env.length
  match t, force depth ty with
  | .lam b, .vpi _ d c =>
    let g : Val := vneAt depth (.var depth)
    check (.tm d :: Γ) (g :: env) b (capp (depth + 1) c g)
  | .lam _, _ => .error s!"λ-abstraction against non-Π type {showV depth ty}"
  | .pair a b, .vsigma _ d c => do
    check Γ env a d
    check Γ env b (capp depth c (eval depth env a))
  | .pair _ _, _ => .error s!"pair against non-Σ type {showV depth ty}"
  | .plam b, .vpathP _ fam lhs rhs => do
    -- body under a generic interval variable
    let g : Val := .vi (.var depth)
    check (.itv :: Γ) (g :: env) b (capp (depth + 1) fam g)
    -- boundary conditions
    let b0 := eval depth (.vi .zero :: env) b
    let b1 := eval depth (.vi .one :: env) b
    unless conv depth b0 lhs do
      .error s!"path boundary at 0: {repr (quote depth b0)} ≠ {showV depth lhs}"
    unless conv depth b1 rhs do
      .error s!"path boundary at 1: {repr (quote depth b1)} ≠ {showV depth rhs}"
  | .plam _, _ => .error s!"path abstraction against non-PathP type {showV depth ty}"
  | .inl t, .vsum _ sl _ => check Γ env t sl
  | .inl _, _ => .error s!"inl against non-sum type {showV depth ty}"
  | .inr t, .vsum _ _ sr => check Γ env t sr
  | .inr _, _ => .error s!"inr against non-sum type {showV depth ty}"
  | .north, .vsusp _ _ => .ok ()
  | .north, _ => .error s!"north against non-suspension type {showV depth ty}"
  | .south, .vsusp _ _ => .ok ()
  | .south, _ => .error s!"south against non-suspension type {showV depth ty}"
  | .merid a r, .vsusp _ A => do check Γ env a A; checkI Γ r
  | .pinl t, .vpushout _ A _ _ _ _ => check Γ env t A
  | .pinl _, _ => .error s!"pinl against non-pushout type {showV depth ty}"
  | .pinr t, .vpushout _ _ B _ _ _ => check Γ env t B
  | .pinr _, _ => .error s!"pinr against non-pushout type {showV depth ty}"
  | .ppush f g c r, .vpushout _ A B C fV gV => do
    check Γ env c C
    checkI Γ r
    let fE := eval depth env f
    let gE := eval depth env g
    if !conv depth fE fV then
      .error "ppush: f annotation does not match the pushout type"
    else if !conv depth gE gV then
      .error "ppush: g annotation does not match the pushout type"
    else .ok ()
  | .ppush _ _ _ _, _ =>
    .error s!"ppush against non-pushout type {showV depth ty}"
  | .embase, .vem1 _ _ _ => .ok ()
  | .bpt t, .vbgpd _ ob _ _ => check Γ env t ob
  | .bpt _, _ => .error s!"bpt against non-BGpd type {showV depth ty}"
  | .barr x y f r, .vbgpd _ ob hom _ => do
    check Γ env x ob
    check Γ env y ob
    let xV := eval depth env x
    let yV := eval depth env y
    check Γ env f (vapp depth (vapp depth hom xV) yV)
    checkI Γ r
  | .barr _ _ _ _, _ =>
    .error s!"barr against non-BGpd type {showV depth ty}"
  | .bcomp cm x y z f g r s2, .vbgpd _ ob hom cmpV => do
    check Γ env x ob
    check Γ env y ob
    check Γ env z ob
    let xV := eval depth env x
    let yV := eval depth env y
    let zV := eval depth env z
    check Γ env f (vapp depth (vapp depth hom xV) yV)
    check Γ env g (vapp depth (vapp depth hom yV) zV)
    checkI Γ r
    checkI Γ s2
    if !conv depth (eval depth env cm) cmpV then
      .error "bcomp: cmp annotation does not match the BGpd type"
    else .ok ()
  | .bcomp _ _ _ _ _ _ _ _, _ =>
    .error s!"bcomp against non-BGpd type {showV depth ty}"
  | .bsquash x y p q u v j1 j2 j3, .vbgpd _ ob hom cmpV => do
    let bV := vbgpdAt depth ob hom cmpV
    check Γ env x bV
    check Γ env y bV
    let xV := eval depth env x
    let yV := eval depth env y
    let pT := vpathPAt depth (.constV bV) xV yV
    check Γ env p pT
    check Γ env q pT
    let pV := eval depth env p
    let qV := eval depth env q
    let uT := vpathPAt depth (.constV pT) pV qV
    check Γ env u uT
    check Γ env v uT
    checkI Γ j1
    checkI Γ j2
    checkI Γ j3
  | .bsquash _ _ _ _ _ _ _ _ _, _ =>
    .error s!"bsquash against non-BGpd type {showV depth ty}"
  | .embase, _ => .error s!"embase against non-EM1 type {showV depth ty}"
  | .emloop g r, .vem1 _ C _ => do
    check Γ env g C
    checkI Γ r
  | .emloop _ _, _ => .error s!"emloop against non-EM1 type {showV depth ty}"
  | .emcomp mul g h r s2, .vem1 _ C M => do
    check Γ env g C
    check Γ env h C
    checkI Γ r
    checkI Γ s2
    if !conv depth (eval depth env mul) M then
      .error "emcomp: mul annotation does not match the EM1 type"
    else .ok ()
  | .emcomp _ _ _ _ _, _ =>
    .error s!"emcomp against non-EM1 type {showV depth ty}"
  | .emsquash x y p q u v j1 j2 j3, .vem1 _ C M => do
    let emV := vem1At depth C M
    check Γ env x emV
    check Γ env y emV
    let xV := eval depth env x
    let yV := eval depth env y
    let pT := vpathPAt depth (.constV emV) xV yV
    check Γ env p pT
    check Γ env q pT
    let pV := eval depth env p
    let qV := eval depth env q
    let uT := vpathPAt depth (.constV pT) pV qV
    check Γ env u uT
    check Γ env v uT
    checkI Γ j1
    checkI Γ j2
    checkI Γ j3
  | .emsquash _ _ _ _ _ _ _ _ _, _ =>
    .error s!"emsquash against non-EM1 type {showV depth ty}"
  | .lnil, .vlist _ _ => .ok ()
  | .lnil, _ => .error s!"lnil against non-list type {showV depth ty}"
  | .lcons h t, .vlist _ A => do
    check Γ env h A
    check Γ env t (vlistAt depth A)
  | .lcons _ _, _ => .error s!"lcons against non-list type {showV depth ty}"
  | .qin t, .vquot _ A _ => check Γ env t A
  | .qin _, _ => .error s!"qin against non-quotient type {showV depth ty}"
  | .qeq a b w r, .vquot _ A R => do
    check Γ env a A
    check Γ env b A
    let aV := eval depth env a
    let bV := eval depth env b
    check Γ env w (vapp depth (vapp depth R aV) bV)
    checkI Γ r
  | .qeq _ _ _ _, _ =>
    .error s!"qeq against non-quotient type {showV depth ty}"
  | .qsquash x y p q r s2, .vquot _ A R => do
    let quotV := vquotAt depth A R
    check Γ env x quotV
    check Γ env y quotV
    let xV := eval depth env x
    let yV := eval depth env y
    check Γ env p (vpathPAt depth (.constV quotV) xV yV)
    check Γ env q (vpathPAt depth (.constV quotV) xV yV)
    checkI Γ r
    checkI Γ s2
  | .qsquash _ _ _ _ _ _, _ =>
    .error s!"qsquash against non-quotient type {showV depth ty}"
  | .tin t, .vtrunc _ A => check Γ env t A
  | .tin _, _ => .error s!"tin against non-truncation type {showV depth ty}"
  | .squash x y r, .vtrunc _ A => do
    check Γ env x (vtruncAt depth A)
    check Γ env y (vtruncAt depth A)
    checkI Γ r
  | .squash _ _ _, _ =>
    .error s!"squash against non-truncation type {showV depth ty}"
  | .merid _ _, _ =>
    .error s!"merid against non-suspension type {showV depth ty}"
  | _, _ => do
    let ty' ← infer Γ env t
    let ok := conv depth ty ty' ||
      -- universe subsumption (cumulativity at the judgement level)
      (match force depth ty, force depth ty' with
       | .vuniv n, .vuniv m => m ≤ n
       | _, _ => false)
    unless ok do
      .error s!"type mismatch: expected {showV depth ty}, inferred {showV depth ty'}"

/-- Infer the universe level of a type. -/
partial def inferSort (Γ : Ctx) (env : List Val) (t : Term) : Except String Nat := do
  match force env.length (← infer Γ env t) with
  | .vuniv n => .ok n
  | ty => .error s!"expected a type, got an element of {showV env.length ty}"

/-- Infer a type for `t`. -/
partial def infer (Γ : Ctx) (env : List Val) : Term → Except String Val
  | .var i =>
    match Γ[i]? with
    | some (.tm ty) => .ok ty
    | some .itv => .error s!"interval variable #{i} used as a term"
    | none => .error s!"unbound variable #{i}"
  | .univ n => .ok (.vuniv (n + 1))
  | .nat => .ok (.vuniv 0)
  | .zero => .ok .vnat
  | .succ n => do check Γ env n .vnat; .ok .vnat
  | .int => .ok (.vuniv 0)
  | .ipos t => do check Γ env t .vnat; .ok .vint
  | .inegsuc t => do check Γ env t .vnat; .ok .vint
  | .intcase m fp fn t => do
    let depth := env.length
    check Γ env t .vint
    let _ ← inferSort (.tm .vint :: Γ) (vneAt depth (.var depth) :: env) m
    let motC : Closure := mkAt depth env m
    check Γ env fp (vpiAt depth .vnat (.intcasePos motC))
    check Γ env fn (vpiAt depth .vnat (.intcaseNeg motC))
    .ok (capp depth motC (eval depth env t))
  | .unit => .ok (.vuniv 0)
  | .tt => .ok .vunit
  | .unitrec m pt t => do
    let depth := env.length
    check Γ env t .vunit
    let _ ← inferSort (.tm .vunit :: Γ) (vneAt depth (.var depth) :: env) m
    let motC : Closure := mkAt depth env m
    check Γ env pt (capp depth motC .vtt)
    .ok (capp depth motC (eval depth env t))
  | .empty => .ok (.vuniv 0)
  | .emptyrec ty t => do
    let depth := env.length
    let _ ← inferSort Γ env ty
    check Γ env t .vempty
    .ok (eval depth env ty)
  | .sum l r => do
    let m ← inferSort Γ env l
    let n ← inferSort Γ env r
    .ok (.vuniv (max m n))
  | .sumcase m fl fr t => do
    let depth := env.length
    match force depth (← infer Γ env t) with
    | .vsum _ sl sr =>
      let _ ← inferSort (.tm (vsumAt depth sl sr) :: Γ) (vneAt depth (.var depth) :: env) m
      let motC : Closure := mkAt depth env m
      check Γ env fl (vpiAt depth sl (.sumcaseL motC))
      check Γ env fr (vpiAt depth sr (.sumcaseR motC))
      .ok (capp depth motC (eval depth env t))
    | ty => .error s!"sumcase on non-sum of type {showV depth ty}"
  | .susp a => do let n ← inferSort Γ env a; .ok (.vuniv n)
  | .susprec m nc sc mc t => do
    let depth := env.length
    match force depth (← infer Γ env t) with
    | .vsusp lbA A =>
      let _ ← inferSort (.tm (.vsusp lbA A) :: Γ)
        (vneAt depth (.var depth) :: env) m
      let motC : Closure := mkAt depth env m
      check Γ env nc (capp depth motC .vnorth)
      check Γ env sc (capp depth motC .vsouth)
      let ncV := eval depth env nc
      let scV := eval depth env sc
      check Γ env mc (vpiAt depth A (.suspMcCod motC ncV scV))
      .ok (capp depth motC (eval depth env t))
    | ty => .error s!"susprec on non-suspension of type {showV depth ty}"
  | .north => .error "cannot infer the type of north (annotate)"
  | .south => .error "cannot infer the type of south (annotate)"
  | .merid _ _ => .error "cannot infer the type of merid (annotate)"
  | .pushout a b c f g => do
    let depth := env.length
    let m1 ← inferSort Γ env a
    let m2 ← inferSort Γ env b
    let m3 ← inferSort Γ env c
    let aV := eval depth env a
    let bV := eval depth env b
    let cV := eval depth env c
    check Γ env f (vpiAt depth cV (.constV aV))
    check Γ env g (vpiAt depth cV (.constV bV))
    .ok (.vuniv (max m1 (max m2 m3)))
  | .pushrec m lc rc pc t => do
    let depth := env.length
    match force depth (← infer Γ env t) with
    | .vpushout _ A B C f g =>
      let _ ← inferSort (.tm (vpushoutAt depth A B C f g) :: Γ)
        (vneAt depth (.var depth) :: env) m
      let motC : Closure := mkAt depth env m
      check Γ env lc (vpiAt depth A (.pushLcCod motC))
      check Γ env rc (vpiAt depth B (.pushRcCod motC))
      let lcV := eval depth env lc
      let rcV := eval depth env rc
      check Γ env pc (vpiAt depth C (.pushPcCod motC lcV rcV f g))
      .ok (capp depth motC (eval depth env t))
    | ty => .error s!"pushrec on non-pushout of type {showV depth ty}"
  | .defn _ _ ty => .ok (eval env.length env ty)
  | .em1 car mul => do
    let depth := env.length
    let n ← inferSort Γ env car
    check Γ env mul
      (eval depth env (.pi car (.pi (car.shift 1 0) (car.shift 2 0))))
    .ok (.vuniv n)
  | .bgpd ob hom cmp => do
    let depth := env.length
    let n ← inferSort Γ env ob
    -- hom : Ob → Ob → U
    check Γ env hom
      (eval depth env (.pi ob (.pi (ob.shift 1 0) (.univ n))))
    -- cmp : Π x y z. hom x y → hom y z → hom x z
    let h3 := hom.shift 3 0
    check Γ env cmp
      (eval depth env (.pi ob (.pi (ob.shift 1 0) (.pi (ob.shift 2 0)
        (.pi (.app (.app (h3.shift 0 0) (.var 2)) (.var 1))
          (.pi (.app (.app (hom.shift 4 0) (.var 2)) (.var 1))
            (.app (.app (hom.shift 5 0) (.var 4)) (.var 2))))))))
    .ok (.vuniv n)
  | .bpt _ => .error "cannot infer bpt (check against a BGpd type)"
  | .barr _ _ _ _ =>
    .error "cannot infer barr (check against a BGpd type)"
  | .bcomp _ _ _ _ _ _ _ _ =>
    .error "cannot infer bcomp (check against a BGpd type)"
  | .bsquash _ _ _ _ _ _ _ _ _ =>
    .error "cannot infer bsquash (check against a BGpd type)"
  | .bgrec bT gB pf pl pc t => do
    let depth := env.length
    match force depth (← infer Γ env t) with
    | .vbgpd _ obV homV cmpV =>
      let _ ← inferSort Γ env bT
      let BV := eval depth env bT
      check Γ env gB (vapp depth (eval depth [] isGpdTm) BV)
      -- pf : Ob → B
      check Γ env pf (vpiAt depth obV (.constV BV))
      let pfV := eval depth env pf
      -- pl : Π x y (f : hom x y). Path B (pf x) (pf y)
      -- (synthesized as a Term over the explicit value environment
      --  [pf, hom, ob, B]; under k binders those sit at k .. k+3)
      let envL : List Val := [pfV, homV, obV, BV]
      let plTy : Term :=
        .pi (.var 2) (.pi (.var 3)
          (.pi (.app (.app (.var 3) (.var 1)) (.var 0))
            (.pathP (.var 7)
              (.app (.var 3) (.var 2))
              (.app (.var 3) (.var 1)))))
      check Γ env pl (eval depth envL plTy)
      let plV := eval depth env pl
      -- pc : Π x y z (f : hom x y) (g : hom y z).
      --        PathP (λ j. Path B (pf x) ((pl y z g) @ j))
      --          (pl x y f) (pl x z (cmp x y z f g))
      -- explicit env [pl, cmp, pf, hom, ob, B]; under k binders: pl = k,
      -- cmp = k+1, pf = k+2, hom = k+3, ob = k+4, B = k+5
      let envC : List Val := [plV, cmpV, pfV, homV, obV, BV]
      let pcTy : Term :=
        .pi (.var 4)                                        -- x
          (.pi (.var 5)                                     -- y
            (.pi (.var 6)                                   -- z
              (.pi (.app (.app (.var 6) (.var 2)) (.var 1)) -- f : hom x y
                (.pi (.app (.app (.var 7) (.var 2)) (.var 1)) -- g : hom y z
                  (.pathP
                    (.pathP (.var 12)                       -- B (+2 itv binders)
                      (.app (.var 8) (.var 5))              -- pf x
                      (.papp
                        (.app (.app (.app (.var 6) (.var 4)) (.var 3))
                          (.var 1))                          -- pl y z g
                        (.app (.var 8) (.var 4))            -- pf y
                        (.app (.var 8) (.var 3))            -- pf z
                        (.var 0)))                          -- @ j
                    (.app (.app (.app (.var 5) (.var 4)) (.var 3))
                      (.var 1))                              -- pl x y f
                    (.app (.app (.app (.var 5) (.var 4)) (.var 2))
                      (.app (.app (.app (.app (.app (.var 6)
                        (.var 4)) (.var 3)) (.var 2)) (.var 1))
                        (.var 0))))))))                      -- pl x z (cmp⁵)
      check Γ env pc (eval depth envC pcTy)
      .ok BV
    | ty => .error s!"bgrec on non-BGpd of type {showV depth ty}"
  | .bgelim m gP pb pl pc t => do
    let depth := env.length
    match force depth (← infer Γ env t) with
    | .vbgpd lbB obV homV cmpV =>
      let bgV := Val.vbgpd lbB obV homV cmpV
      let _ ← inferSort (.tm bgV :: Γ) (vneAt depth (.var depth) :: env) m
      let motC : Closure := mkAt depth env m
      let motV : Val := vlamAt depth motC
      -- gP : Π t. isGpd (motive t)  (compose the closed isGpd closure)
      let gpdC : Closure ←
        match eval depth [] isGpdTm with
        | .vlam _ c => pure c
        | _ => .error "bgelim: isGpd synthesis failed"
      check Γ env gP (vpiAt depth bgV (.comp gpdC motC))
      -- pb : Π x. motive (bpt x)
      let bptC : Closure := mkAt depth [] (.bpt (.var 0))
      check Γ env pb (vpiAt depth obV (.comp motC bptC))
      let pbV := eval depth env pb
      -- pl : Π x y (f : hom x y).
      --        PathP (λ i. motive (barr x y f i)) (pb x) (pb y)
      let envL : List Val := [pbV, motV, homV, obV]
      let plTy : Term :=
        .pi (.var 3) (.pi (.var 4)
          (.pi (.app (.app (.var 4) (.var 1)) (.var 0))
            (.pathP
              (.app (.var 5)
                (.barr (.var 3) (.var 2) (.var 1) (.var 0)))
              (.app (.var 3) (.var 2))
              (.app (.var 3) (.var 1)))))
      check Γ env pl (eval depth envL plTy)
      let plV := eval depth env pl
      -- pc : Π x y z (f : hom x y) (g : hom y z).
      --   PathP (λ rj. PathP (λ ri. motive (bcomp cmp x y z f g rj ri))
      --                 (pb x) ((pl y z g) @ rj))
      --     (pl x y f) (pl x z (cmp x y z f g))
      let envC : List Val := [plV, motV, cmpV, pbV, homV, obV]
      let pcTy : Term :=
        .pi (.var 5) (.pi (.var 6) (.pi (.var 7)
          (.pi (.app (.app (.var 7) (.var 2)) (.var 1))
            (.pi (.app (.app (.var 8) (.var 2)) (.var 1))
              (.pathP
                (.pathP
                  (.app (.var 8)
                    (.bcomp (.var 9) (.var 6) (.var 5) (.var 4)
                      (.var 3) (.var 2) (.var 1) (.var 0)))
                  (.app (.var 9) (.var 5))
                  (.papp
                    (.app (.app (.app (.var 6) (.var 4)) (.var 3))
                      (.var 1))
                    (.app (.var 9) (.var 4))
                    (.app (.var 9) (.var 3))
                    (.var 0)))
                (.app (.app (.app (.var 5) (.var 4)) (.var 3)) (.var 1))
                (.app (.app (.app (.var 5) (.var 4)) (.var 2))
                  (.app (.app (.app (.app (.app (.var 7) (.var 4))
                    (.var 3)) (.var 2)) (.var 1)) (.var 0))))))))
      check Γ env pc (eval depth envC pcTy)
      .ok (capp depth motC (eval depth env t))
    | ty => .error s!"bgelim on non-BGpd of type {showV depth ty}"
  | .em1rec bT gB b l c t => do
    let depth := env.length
    match force depth (← infer Γ env t) with
    | .vem1 _ C M =>
      let _ ← inferSort Γ env bT
      let BV := eval depth env bT
      check Γ env gB (vapp depth (eval depth [] isGpdTm) BV)
      check Γ env b BV
      let bV := eval depth env b
      check Γ env l (vpiAt depth C (.constV (vpathPAt depth (.constV BV) bV bV)))
      let lV := eval depth env l
      check Γ env c (vpiAt depth C (.em1recCCod BV C M lV bV))
      .ok BV
    | ty => .error s!"em1rec on non-EM1 of type {showV depth ty}"
  | .em1elim m gP b l c t => do
    let depth := env.length
    match force depth (← infer Γ env t) with
    | .vem1 _ C M =>
      let emV := vem1At depth C M
      let _ ← inferSort (.tm emV :: Γ) (vneAt depth (.var depth) :: env) m
      let motC : Closure := mkAt depth env m
      check Γ env gP (vpiAt depth emV (.em1elimGCod motC))
      check Γ env b (capp depth motC .vembase)
      let bV := eval depth env b
      check Γ env l (vpiAt depth C (.em1elimLCod motC bV))
      let lV := eval depth env l
      check Γ env c (vpiAt depth C (.em1elimDCCod motC C M lV bV))
      .ok (capp depth motC (eval depth env t))
    | ty => .error s!"em1elim on non-EM1 of type {showV depth ty}"
  | .embase => .error "cannot infer the type of embase (annotate)"
  | .emloop _ _ => .error "cannot infer the type of emloop (annotate)"
  | .emcomp _ _ _ _ _ =>
    .error "cannot infer the type of emcomp (annotate)"
  | .emsquash _ _ _ _ _ _ _ _ _ =>
    .error "cannot infer the type of emsquash (annotate)"
  | .list a => do let n ← inferSort Γ env a; .ok (.vuniv n)
  | .listrec m nc cc t => do
    let depth := env.length
    match force depth (← infer Γ env t) with
    | .vlist _ A =>
      let listV := vlistAt depth A
      let _ ← inferSort (.tm listV :: Γ) (vneAt depth (.var depth) :: env) m
      let motC : Closure := mkAt depth env m
      check Γ env nc (capp depth motC .vlnil)
      check Γ env cc (vpiAt depth A (.listCcCod motC A))
      .ok (capp depth motC (eval depth env t))
    | ty => .error s!"listrec on non-list of type {showV depth ty}"
  | .lnil => .error "cannot infer the type of lnil (annotate)"
  | .lcons _ _ => .error "cannot infer the type of lcons (annotate)"
  | .quot a r => do
    let depth := env.length
    let n ← inferSort Γ env a
    check Γ env r (eval depth env (.pi a (.pi (a.shift 1 0) (.univ n))))
    .ok (.vuniv n)
  | .qelim m mset f feq t => do
    let depth := env.length
    match force depth (← infer Γ env t) with
    | .vquot _ A R =>
      let quotV := vquotAt depth A R
      let _ ← inferSort (.tm quotV :: Γ) (vneAt depth (.var depth) :: env) m
      let motC : Closure := mkAt depth env m
      check Γ env mset (vpiAt depth quotV (.qelimSetCod motC))
      check Γ env f (vpiAt depth A (.qelimInCod motC))
      let fV := eval depth env f
      check Γ env feq (vpiAt depth A (.qelimEqCod motC A R fV))
      .ok (capp depth motC (eval depth env t))
    | ty => .error s!"qelim on non-quotient of type {showV depth ty}"
  | .qin _ => .error "cannot infer the type of qin (annotate)"
  | .qeq _ _ _ _ => .error "cannot infer the type of qeq (annotate)"
  | .qsquash _ _ _ _ _ _ =>
    .error "cannot infer the type of qsquash (annotate)"
  | .trunc a => do let n ← inferSort Γ env a; .ok (.vuniv n)
  | .truncrec mB prp f t => do
    let depth := env.length
    match force depth (← infer Γ env t) with
    | .vtrunc _ A =>
      let _ ← inferSort Γ env mB
      check Γ env prp (eval depth env
        (.pi mB (.pi (mB.shift 1 0)
          (.pathP (mB.shift 3 0) (.var 1) (.var 0)))))
      check Γ env f (vpiAt depth A (mkAt depth env (mB.shift 1 0)))
      .ok (eval depth env mB)
    | ty => .error s!"truncrec on non-truncation of type {showV depth ty}"
  | .pinl _ => .error "cannot infer the type of pinl (annotate)"
  | .pinr _ => .error "cannot infer the type of pinr (annotate)"
  | .ppush _ _ _ _ => .error "cannot infer the type of ppush (annotate)"
  | .tin _ => .error "cannot infer the type of tin (annotate)"
  | .squash _ _ _ => .error "cannot infer the type of squash (annotate)"
  | .torus => .ok (.vuniv 0)
  | .tbase => .ok .vtorus
  | .tloopP r => do checkI Γ r; .ok .vtorus
  | .tloopQ r => do checkI Γ r; .ok .vtorus
  | .tsurf r s2 => do checkI Γ r; checkI Γ s2; .ok .vtorus
  | .torusrec m bc pc qc sc t => do
    let depth := env.length
    check Γ env t .vtorus
    let _ ← inferSort (.tm .vtorus :: Γ) (vneAt depth (.var depth) :: env) m
    let motC : Closure := mkAt depth env m
    check Γ env bc (capp depth motC .vtbase)
    let bcV := eval depth env bc
    check Γ env pc (vpathPAt depth (.torusLoopPFam motC) bcV bcV)
    let pcV := eval depth env pc
    check Γ env qc (vpathPAt depth (.torusLoopQFam motC) bcV bcV)
    let qcV := eval depth env qc
    check Γ env sc (vpathPAt depth (.torusSurfFam motC bcV pcV) qcV qcV)
    .ok (capp depth motC (eval depth env t))
  | .s1 => .ok (.vuniv 0)
  | .sbase => .ok .vs1
  | .sloop r => do checkI Γ r; .ok .vs1
  | .s1elim m b l x => do
    let depth := env.length
    check Γ env x .vs1
    let _ ← inferSort (.tm .vs1 :: Γ) (vneAt depth (.var depth) :: env) m
    let motC : Closure := mkAt depth env m
    check Γ env b (capp depth motC .vsbase)
    let bV := eval depth env b
    check Γ env l (vpathPAt depth (.s1loopFam motC) bV bV)
    .ok (capp depth motC (eval depth env x))
  | .pi d c => do
    let depth := env.length
    let m ← inferSort Γ env d
    let n ← inferSort (.tm (eval depth env d) :: Γ) (vneAt depth (.var depth) :: env) c
    .ok (.vuniv (max m n))
  | .sigma d c => do
    let depth := env.length
    let m ← inferSort Γ env d
    let n ← inferSort (.tm (eval depth env d) :: Γ) (vneAt depth (.var depth) :: env) c
    .ok (.vuniv (max m n))
  | .app f a => do
    let depth := env.length
    match force depth (← infer Γ env f) with
    | .vpi _ d c =>
      check Γ env a d
      .ok (capp depth c (eval depth env a))
    | ty => .error s!"application of non-function of type {showV depth ty}"
  | .fst p => do
    match force env.length (← infer Γ env p) with
    | .vsigma _ d _ => .ok d
    | ty => .error s!".fst of non-pair of type {showV env.length ty}"
  | .snd p => do
    let depth := env.length
    match force depth (← infer Γ env p) with
    | .vsigma _ _ c => .ok (capp depth c (vfst depth (eval depth env p)))
    | ty => .error s!".snd of non-pair of type {showV depth ty}"
  | .natrec m z s n => do
    let depth := env.length
    check Γ env n .vnat
    let _ ← inferSort (.tm .vnat :: Γ) (vneAt depth (.var depth) :: env) m
    let motC : Closure := mkAt depth env m
    check Γ env z (capp depth motC .vzero)
    check Γ env s (vpiAt depth .vnat (.natrecS motC))
    .ok (capp depth motC (eval depth env n))
  | .pathP f l r => do
    let depth := env.length
    let n ← inferSort (.itv :: Γ) (.vi (.var depth) :: env) f
    let famC : Closure := mkAt depth env f
    check Γ env l (capp depth famC (.vi .zero))
    check Γ env r (capp depth famC (.vi .one))
    .ok (.vuniv n)
  | .papp p l r s => do
    let depth := env.length
    checkI Γ s
    match force depth (← infer Γ env p) with
    | .vpathP _ fam lhs rhs =>
      -- verify the endpoint annotations against the type of `p`
      check Γ env l (capp depth fam (.vi .zero))
      check Γ env r (capp depth fam (.vi .one))
      unless conv depth (eval depth env l) lhs do
        .error "papp: left endpoint annotation does not match the path's type"
      unless conv depth (eval depth env r) rhs do
        .error "papp: right endpoint annotation does not match the path's type"
      .ok (capp depth fam (eval depth env s))
    | ty => .error s!"path application of non-path of type {showV depth ty}"
  | .transp f a => do
    let depth := env.length
    let _ ← inferSort (.itv :: Γ) (.vi (.var depth) :: env) f
    let famC : Closure := mkAt depth env f
    check Γ env a (capp depth famC (.vi .zero))
    .ok (capp depth famC (.vi .one))
  | .hcomp ty sys u₀ => do
    let depth := env.length
    let _ ← inferSort Γ env ty
    let A := eval depth env ty
    check Γ env u₀ A
    -- resolve each face to a substitution on ambient interval variables
    let subsList ← sys.mapM fun (cof, _) => resolveFace Γ cof
    -- check each branch under every disjunct of its face
    for k in [0:sys.length] do
      let (_, body) := sys[k]!
      for subs in subsList[k]! do
        unless contradictory subs do
          let env' := restrictEnv env subs
          let A' := eval depth env' ty
          check (.itv :: Γ) (.vi (.var depth) :: env') body A'
          -- adjacency with the base: body[i:=0] ≡ u₀ under the face
          let b0 := eval depth (.vi .zero :: env') body
          let u₀' := eval depth env' u₀
          unless conv depth b0 u₀' do
            .error s!"hcomp branch {k} does not agree with the base at 0"
    -- pairwise compatibility on overlapping faces
    for k in [0:sys.length] do
      for k' in [0:sys.length] do
        if k < k' then
          for subs1 in subsList[k]! do
            for subs2 in subsList[k']! do
              let subs := subs1 ++ subs2
              unless contradictory subs do
                let env' := restrictEnv env subs
                let g : Val := .vi (.var depth)
                let b₁ := eval (depth + 1) (g :: env') (sys[k]!).2
                let b₂ := eval (depth + 1) (g :: env') (sys[k']!).2
                unless conv (depth + 1) b₁ b₂ do
                  .error s!"hcomp branches {k} and {k'} disagree on their overlap"
    .ok A
  | .glueTy sys base => do
    let depth := env.length
    let nb ← inferSort Γ env base
    let mut lvl := nb
    let subsList ← sys.mapM fun (cof, _, _) => resolveFace Γ cof
    -- each branch: a type Tₖ and an equivalence eₖ : Equiv Tₖ base, checked
    -- under the face restriction (the equivalence type is synthesized as an
    -- object-language term and evaluated in the restricted environment)
    for k in [0:sys.length] do
      let (_, T, e) := sys[k]!
      for subs in subsList[k]! do
        unless contradictory subs do
          let env' := restrictEnv env subs
          lvl := max lvl (← inferSort Γ env' T)
          check Γ env' e (eval depth env' (equivT T base))
    -- overlapping branches must agree (both type and equivalence)
    for k in [0:sys.length] do
      for k' in [0:sys.length] do
        if k < k' then
          for subs1 in subsList[k]! do
            for subs2 in subsList[k']! do
              let subs := subs1 ++ subs2
              unless contradictory subs do
                let env' := restrictEnv env subs
                unless conv depth (eval depth env' (sys[k]!).2.1)
                    (eval depth env' (sys[k']!).2.1) do
                  .error s!"Glue branches {k} and {k'}: types disagree on overlap"
                unless conv depth (eval depth env' (sys[k]!).2.2)
                    (eval depth env' (sys[k']!).2.2) do
                  .error s!"Glue branches {k} and {k'}: equivalences disagree on overlap"
    .ok (.vuniv lvl)
  | .glueTm gty sys base => do
    let depth := env.length
    let _ ← inferSort Γ env gty
    let G := eval depth env gty
    match G with
    | .vglueTy _ gsys gbase =>
      unless sys.length == gsys.length do
        .error "glue: system does not match the Glue type's system"
      check Γ env base gbase
      let subsList ← sys.mapM fun (cof, _) => resolveFace Γ cof
      for k in [0:sys.length] do
        let (cof, t) := sys[k]!
        -- the branch face must be the type's face
        let cofV := cof.map fun (f, b) => ((eval depth env f).asIVal, b)
        unless convCof cofV (gsys[k]!).1 do
          .error s!"glue branch {k}: face differs from the Glue type's face"
        for subs in subsList[k]! do
          unless contradictory subs do
            let env' := restrictEnv env subs
            -- under the face, the Glue type collapses to the branch type
            check Γ env' t (force depth (eval depth env' gty))
            -- adjacency: eₖ tₖ ≡ a on the face
            let wk :=
              match eval depth env' gty with
              | .vglueTy _ s _ => (s[k]!).2.2
              | _ => panic! "glueTm: annotation lost its Glue shape"
            unless conv depth (vapp depth (vfst depth wk) (eval depth env' t))
                (eval depth env' base) do
              .error s!"glue branch {k} does not map to the base under its equivalence"
      -- overlapping branches must agree
      for k in [0:sys.length] do
        for k' in [0:sys.length] do
          if k < k' then
            for subs1 in subsList[k]! do
              for subs2 in subsList[k']! do
                let subs := subs1 ++ subs2
                unless contradictory subs do
                  let env' := restrictEnv env subs
                  unless conv depth (eval depth env' (sys[k]!).2)
                      (eval depth env' (sys[k']!).2) do
                    .error s!"glue branches {k} and {k'} disagree on their overlap"
      .ok G
    | _ => .error "glue: annotation is not a Glue type"
  | .unglue gty b => do
    let depth := env.length
    let _ ← inferSort Γ env gty
    let G := eval depth env gty
    match G with
    | .vglueTy _ _ gbase =>
      check Γ env b G
      .ok gbase
    | _ => .error "unglue: annotation is not a Glue type"
  | .ann t ty => do
    let depth := env.length
    let _ ← inferSort Γ env ty
    let tyV := eval depth env ty
    check Γ env t tyV
    .ok tyV
  | .lam _ => .error "cannot infer the type of a λ-abstraction (annotate)"
  | .pair _ _ => .error "cannot infer the type of a pair (annotate)"
  | .plam _ => .error "cannot infer the type of a path abstraction (annotate)"
  | .inl _ => .error "cannot infer the type of inl (annotate)"
  | .inr _ => .error "cannot infer the type of inr (annotate)"
  | .i0 | .i1 | .imax .. | .imin .. | .ineg .. =>
    .error "interval expression where a term was expected"

end

/-! ## Top-level interface -/

/-- Type-check a closed definition `tm : ty` given in surface syntax. -/
def checkDef (tm ty : Raw) : Except String Term := do
  let tyT ← ty.resolve []
  let tmT ← tm.resolve []
  let _ ← inferSort [] [] tyT
  check [] [] tmT (eval 0 [] tyT)
  .ok tmT

/-- Type-check a definition in a preloaded context: `names`/`Γ`/`env`
carry already-verified definitions as variables (innermost first), so a
reference costs one environment lookup and every use shares one value. -/
def checkDefCtx (names : List String) (Γ : Ctx) (env : List Val)
    (tm ty : Raw) : Except String Term := do
  let tyT ← ty.resolve names
  let tmT ← tm.resolve names
  let _ ← inferSort Γ env tyT
  check Γ env tmT (eval env.length env tyT)
  .ok tmT

/-- Normalize a closed, well-typed surface term. -/
def normalize (tm ty : Raw) : Except String Term := do
  let t ← checkDef tm ty
  .ok (nf t)

end Cubical
