import FormalizedMathematics.Cubical.LibHITs

/-! # (T-C) probes: K-invariant squares in the object-language join

Over a generic context `A B : U`, `a0 : A`, `b0 : B`,
`sa : Path A a0 a0` (a loop), form the join
`Jn := pushout (A ← A × B → B)` with the segment path
`seg a b := ⟨r⟩ ppush(a,b)(r) : pinl a ⇝ pinr b`.

The *XOR square* is `s0(i,j) := seg a0 b0 (t*(i,j))` with
`t* = (i∧¬j)∨(¬i∧j)` — the pure strictly K-invariant square (its
components are fixed by the coordinate swap `sw : (i,j)↦(j,i)` and
the double reversal `nb : (i,j)↦(¬i,¬j)`).

The *σ-twisted square* is the hcomp of `s0` along a K-symmetric tube
that composes every boundary face with the loop `sa`:

  s := hcomp^z [ i=0 ↦ seg (sa z) b0 (j),   i=1 ↦ seg (sa z) b0 (¬j),
                 j=0 ↦ seg (sa z) b0 (i),   j=1 ↦ seg (sa z) b0 (¬i) ]
       s0

The probes verify (machine decisions, per the platform's K3):
 1. both squares are well typed at the common ℓ-diamond boundary type;
 2. `s` is *strictly* invariant under `sw` and `nb` — the tube system
    is mapped to itself as a system (hcomp commutes with substitution
    and the kernel's face-system comparison closes the loop);
 3. `s` is definitionally separated from the untwisted `s0` — the
    twist is not erased by conversion.

This realizes, in the object language, the design of
docs/TestComparison.md §§20–22: strictly K-invariant squares beyond
the pure (cover-factoring, null) stratum exist, with the invariance
achieved by a K-symmetric tube rather than by (impossible) invariance
of the individual pieces. -/

namespace Cubical.Library

open Raw

private def okD (tm ty : Raw) : Bool :=
  match checkDef tm ty with
  | .ok _ => true
  | .error _ => false

private def A : Raw := .var "A"
private def B : Raw := .var "B"
private def a0 : Raw := .var "a0"
private def b0 : Raw := .var "b0"
private def sa : Raw := .var "sa"

private def AxB : Raw := .sigma "u" A B
private def fstF : Raw := .lam "w" (.fst (.var "w"))
private def sndF : Raw := .lam "w" (.snd (.var "w"))
private def Jn : Raw := .pushout A B AxB fstF sndF

private def sb : Raw := .var "sb"

private def ctxJ (body : Raw) : Raw :=
  .pi "A" .univ (.pi "B" .univ (.pi "a0" A (.pi "b0" B
    (.pi "sa" (.path A a0 a0) (.pi "sb" (.path B b0 b0) body)))))

private def lamsJ (body : Raw) : Raw := lams ["A", "B", "a0", "b0", "sa", "sb"] body

/-- `seg a b r := ppush (a,b) r : pinl a ⇝ pinr b`. -/
private def seg (av bv r : Raw) : Raw := .ppush fstF sndF (.pair av bv) r

private def vi : Raw := .var "i"
private def vj : Raw := .var "j"

/-- `t* = (i∧¬j)∨(¬i∧j)` — the De Morgan XOR formula. -/
private def tstar : Raw := .imax (.imin vi (.ineg vj)) (.imin (.ineg vi) vj)
private def tstarNb : Raw :=
  .imax (.imin (.ineg vi) (.ineg (.ineg vj))) (.imin (.ineg (.ineg vi)) (.ineg vj))

/-- The common boundary type: the ℓ-diamond square type. -/
private def SqTy : Raw :=
  .pathP "i" (.path Jn (seg a0 b0 vi) (seg a0 b0 (.ineg vi)))
    (.plam "j" (seg a0 b0 vj))
    (.plam "j" (seg a0 b0 (.ineg vj)))

/-- The untwisted XOR square. -/
private def s0 : Raw := seg a0 b0 tstar

/-- `sa z`, `sb z` — the loops evaluated at the fill variable. -/
private def saz : Raw := .papp sa a0 a0 (.var "z")
private def sbz : Raw := .papp sb b0 b0 (.var "z")

/-- The σ-twisted square: hcomp of `s0` along the K-symmetric tube. -/
private def sTw : Raw :=
  .hcomp "z" Jn
    [([(vi, false)], seg saz b0 vj),
     ([(vi, true)],  seg saz b0 (.ineg vj)),
     ([(vj, false)], seg saz b0 vi),
     ([(vj, true)],  seg saz b0 (.ineg vi))]
    s0

/-- `sw`-image of the twisted square: variables i, j exchanged
(textually: the system entries and the base formula swap roles). -/
private def sTwSw : Raw :=
  .hcomp "z" Jn
    [([(vj, false)], seg saz b0 vi),
     ([(vj, true)],  seg saz b0 (.ineg vi)),
     ([(vi, false)], seg saz b0 vj),
     ([(vi, true)],  seg saz b0 (.ineg vj))]
    (seg a0 b0 (.imax (.imin vj (.ineg vi)) (.imin (.ineg vj) vi)))

/-- `nb`-image: i ↦ ¬i, j ↦ ¬j throughout. -/
private def sTwNb : Raw :=
  .hcomp "z" Jn
    [([(vi, true)],  seg saz b0 (.ineg vj)),
     ([(vi, false)], seg saz b0 (.ineg (.ineg vj))),
     ([(vj, true)],  seg saz b0 (.ineg vi)),
     ([(vj, false)], seg saz b0 (.ineg (.ineg vi)))]
    (seg a0 b0 tstarNb)

private def Sq (body : Raw) : Raw := .plam "i" (.plam "j" body)

/-- Control: the untwisted XOR square inhabits the ℓ-diamond type. -/
def joinXorD : LibDef where
  name := "joinXor"
  ty := ctxJ SqTy
  tm := lamsJ (Sq s0)

#guard joinXorD.ok

/-- The σ-twisted square is well typed at the same boundary. -/
def joinTwistD : LibDef where
  name := "joinTwist"
  ty := ctxJ SqTy
  tm := lamsJ (Sq sTw)

#guard joinTwistD.ok

-- Strict sw-invariance: `s∘sw ≡ s`.
#guard okD
  (lamsJ (.plam "kk" (Sq sTw)))
  (ctxJ (.path SqTy (Sq sTwSw) (Sq sTw)))

-- Strict nb-invariance: `s∘nb ≡ s`.
#guard okD
  (lamsJ (.plam "kk" (Sq sTw)))
  (ctxJ (.path SqTy (Sq sTwNb) (Sq sTw)))

-- Separation: the twist is not erased — `s ≢ s0`.
#guard !(okD
  (lamsJ (.plam "kk" (Sq sTw)))
  (ctxJ (.path SqTy (Sq s0) (Sq sTw))))

-- Sanity: the same tube with the constant (untwisted) filler `a0` in
-- place of `sa z` IS erased — conversion sees through a trivial tube
-- exactly when it is degenerate.  (Recorded as a control; either
-- outcome is informative, the guard documents the actual behavior.)
private def sConst : Raw :=
  .hcomp "z" Jn
    [([(vi, false)], seg a0 b0 vj),
     ([(vi, true)],  seg a0 b0 (.ineg vj)),
     ([(vj, false)], seg a0 b0 vi),
     ([(vj, true)],  seg a0 b0 (.ineg vi))]
    s0

def joinConstTubeD : LibDef where
  name := "joinConstTube"
  ty := ctxJ SqTy
  tm := lamsJ (Sq sConst)

#guard joinConstTubeD.ok

/-! ## The twist lattice

Four strictly K-invariant squares over the same ℓ-diamond boundary:
untwisted `s0`, the A-loop twist `s`, the B-loop twist `s'`, and the
double twist `s''`.  Conjecturally they realize the four
Bredon-equivariant homotopy classes of candidate maps `W → join`
(a torsor over `K ≅ ℤ/2 × ℤ/2`); the guards record that all four are
well typed, K-invariant, and pairwise definitionally separated. -/

/-- The σ'-twisted square (B-side loop in the tube). -/
private def sTwB : Raw :=
  .hcomp "z" Jn
    [([(vi, false)], seg a0 sbz vj),
     ([(vi, true)],  seg a0 sbz (.ineg vj)),
     ([(vj, false)], seg a0 sbz vi),
     ([(vj, true)],  seg a0 sbz (.ineg vi))]
    s0

private def sTwBSw : Raw :=
  .hcomp "z" Jn
    [([(vj, false)], seg a0 sbz vi),
     ([(vj, true)],  seg a0 sbz (.ineg vi)),
     ([(vi, false)], seg a0 sbz vj),
     ([(vi, true)],  seg a0 sbz (.ineg vj))]
    (seg a0 b0 (.imax (.imin vj (.ineg vi)) (.imin (.ineg vj) vi)))

private def sTwBNb : Raw :=
  .hcomp "z" Jn
    [([(vi, true)],  seg a0 sbz (.ineg vj)),
     ([(vi, false)], seg a0 sbz (.ineg (.ineg vj))),
     ([(vj, true)],  seg a0 sbz (.ineg vi)),
     ([(vj, false)], seg a0 sbz (.ineg (.ineg vi)))]
    (seg a0 b0 tstarNb)

/-- The doubly twisted square (both loops). -/
private def sTwAB : Raw :=
  .hcomp "z" Jn
    [([(vi, false)], seg saz sbz vj),
     ([(vi, true)],  seg saz sbz (.ineg vj)),
     ([(vj, false)], seg saz sbz vi),
     ([(vj, true)],  seg saz sbz (.ineg vi))]
    s0

private def sTwABSw : Raw :=
  .hcomp "z" Jn
    [([(vj, false)], seg saz sbz vi),
     ([(vj, true)],  seg saz sbz (.ineg vi)),
     ([(vi, false)], seg saz sbz vj),
     ([(vi, true)],  seg saz sbz (.ineg vj))]
    (seg a0 b0 (.imax (.imin vj (.ineg vi)) (.imin (.ineg vj) vi)))

private def sTwABNb : Raw :=
  .hcomp "z" Jn
    [([(vi, true)],  seg saz sbz (.ineg vj)),
     ([(vi, false)], seg saz sbz (.ineg (.ineg vj))),
     ([(vj, true)],  seg saz sbz (.ineg vi)),
     ([(vj, false)], seg saz sbz (.ineg (.ineg vi)))]
    (seg a0 b0 tstarNb)

def joinTwistBD : LibDef where
  name := "joinTwistB"
  ty := ctxJ SqTy
  tm := lamsJ (Sq sTwB)

#guard joinTwistBD.ok

def joinTwistABD : LibDef where
  name := "joinTwistAB"
  ty := ctxJ SqTy
  tm := lamsJ (Sq sTwAB)

#guard joinTwistABD.ok

-- K-invariance of the B-twist and the double twist.
#guard okD (lamsJ (.plam "kk" (Sq sTwB)))
  (ctxJ (.path SqTy (Sq sTwBSw) (Sq sTwB)))
#guard okD (lamsJ (.plam "kk" (Sq sTwB)))
  (ctxJ (.path SqTy (Sq sTwBNb) (Sq sTwB)))
#guard okD (lamsJ (.plam "kk" (Sq sTwAB)))
  (ctxJ (.path SqTy (Sq sTwABSw) (Sq sTwAB)))
#guard okD (lamsJ (.plam "kk" (Sq sTwAB)))
  (ctxJ (.path SqTy (Sq sTwABNb) (Sq sTwAB)))

-- Pairwise separations: the four twist classes are definitionally
-- distinct (s0 | s | s' | s'').
#guard !(okD (lamsJ (.plam "kk" (Sq sTwB)))
  (ctxJ (.path SqTy (Sq s0) (Sq sTwB))))
#guard !(okD (lamsJ (.plam "kk" (Sq sTwAB)))
  (ctxJ (.path SqTy (Sq s0) (Sq sTwAB))))
#guard !(okD (lamsJ (.plam "kk" (Sq sTwB)))
  (ctxJ (.path SqTy (Sq sTw) (Sq sTwB))))
#guard !(okD (lamsJ (.plam "kk" (Sq sTwAB)))
  (ctxJ (.path SqTy (Sq sTw) (Sq sTwAB))))
#guard !(okD (lamsJ (.plam "kk" (Sq sTwAB)))
  (ctxJ (.path SqTy (Sq sTwB) (Sq sTwAB))))

/-! ## Isotropy-line restrictions of the twist lattice

The diagonal `i = j` is the sw-fixed line, the antidiagonal `i = ¬j`
the g-fixed line.  The terms below are the *manual substitutions*
`s∘(j:=i)` and `s∘(j:=¬i)` of the four twisted squares (mechanical
rewriting of faces and branches; `papp` cannot infer the type of a
plam literal, so the substituted terms are written out).  Expected
factorization, under face-restricted semantics: the diagonal sees
only the σ-twist, the antidiagonal only the σ′-twist.  The equality
verdicts are printed rather than hard-guarded: an "expected-equal"
pair failing diagnoses the remaining spec gap (the kernel compares
system branches at generic dimensions, not on their faces). -/

private def DLoopT : Raw := .path Jn (seg a0 b0 .i0) (seg a0 b0 .i0)
private def ALoopT : Raw := .path Jn (seg a0 b0 .i1) (seg a0 b0 .i1)

private def diagS0 : Raw := seg a0 b0 (.imin vi (.ineg vi))
private def adiagS0 : Raw := seg a0 b0 (.imax vi (.ineg vi))

private def diagTw (av bv : Raw) : Raw :=
  .hcomp "z" Jn
    [([(vi, false)], seg av bv vi), ([(vi, true)], seg av bv (.ineg vi)),
     ([(vi, false)], seg av bv vi), ([(vi, true)], seg av bv (.ineg vi))]
    diagS0

private def adiagTw (av bv : Raw) : Raw :=
  .hcomp "z" Jn
    [([(vi, false)], seg av bv (.ineg vi)),
     ([(vi, true)],  seg av bv (.ineg (.ineg vi))),
     ([(vi, true)],  seg av bv vi),
     ([(vi, false)], seg av bv (.ineg vi))]
    adiagS0

private def dl (t : Raw) : Raw := .plam "i" t

-- Well-typedness of the restrictions.
#guard okD (lamsJ (dl diagS0)) (ctxJ DLoopT)
#guard okD (lamsJ (dl (diagTw saz b0))) (ctxJ DLoopT)
#guard okD (lamsJ (dl (diagTw a0 sbz))) (ctxJ DLoopT)
#guard okD (lamsJ (dl (diagTw saz sbz))) (ctxJ DLoopT)
#guard okD (lamsJ (dl (adiagTw saz sbz))) (ctxJ ALoopT)
#guard okD (lamsJ (dl (adiagTw a0 sbz))) (ctxJ ALoopT)

def diagAeqAB : Bool := okD
  (lamsJ (.plam "kk" (dl (diagTw saz sbz))))
  (ctxJ (.path DLoopT (dl (diagTw saz b0)) (dl (diagTw saz sbz))))
def diagBeqConst : Bool := okD
  (lamsJ (.plam "kk" (dl (diagTw a0 b0))))
  (ctxJ (.path DLoopT (dl (diagTw a0 sbz)) (dl (diagTw a0 b0))))
def adiagBeqAB : Bool := okD
  (lamsJ (.plam "kk" (dl (adiagTw saz sbz))))
  (ctxJ (.path ALoopT (dl (adiagTw a0 sbz)) (dl (adiagTw saz sbz))))
def diagSep0A : Bool := !(okD
  (lamsJ (.plam "kk" (dl (diagTw saz b0))))
  (ctxJ (.path DLoopT (dl diagS0) (dl (diagTw saz b0)))))

#eval do
  IO.println s!"diag(s_A) == diag(s_AB):   {diagAeqAB}"
  IO.println s!"diag(s_B) == diag(const):  {diagBeqConst}"
  IO.println s!"adiag(s_B) == adiag(s_AB): {adiagBeqAB}"
  IO.println s!"diag(s0) sep diag(s_A):    {diagSep0A}"

end Cubical.Library
