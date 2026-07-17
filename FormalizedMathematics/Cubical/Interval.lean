/-!
# The De Morgan interval algebra

Cubical type theory's interval `I` is the free De Morgan algebra on the
interval variables in scope: a bounded distributive lattice `(∨, ∧, 0, 1)`
with an involution `¬` satisfying the De Morgan laws — but *not* the Boolean
laws (`i ∧ ¬i ≠ 0` in general: geometrically it is the "distance to the
nearest endpoint").

Equality in a free De Morgan algebra is decidable: push negations to
literals, distribute to a disjunctive normal form, and reduce to a canonical
antichain of clauses (free distributive lattice over literals).  Two interval
expressions are equal iff their canonical DNFs coincide.
-/

namespace Cubical

/-- Interval values.  `var l` is a de Bruijn *level*. -/
inductive IVal where
  | zero
  | one
  | var (l : Nat)
  | max (a b : IVal)
  | min (a b : IVal)
  | neg (a : IVal)
  deriving Repr, BEq, Inhabited

namespace IVal

/-- Smart join: simplifies endpoint cases eagerly (important so that
constancy checks fire, e.g. `1 ∨ ¬j` must become `1` syntactically). -/
def iMax : IVal → IVal → IVal
  | .one, _ => .one
  | _, .one => .one
  | .zero, r => r
  | r, .zero => r
  | a, b => .max a b

/-- Smart meet. -/
def iMin : IVal → IVal → IVal
  | .zero, _ => .zero
  | _, .zero => .zero
  | .one, r => r
  | r, .one => r
  | a, b => .min a b

/-- Smart involution. -/
def iNeg : IVal → IVal
  | .zero => .one
  | .one => .zero
  | .neg r => r
  | r => .neg r

/-! ## Canonical disjunctive normal forms -/

/-- A literal: an interval variable, possibly negated. -/
abbrev Lit := Nat × Bool

def litKey (l : Lit) : Nat := 2 * l.1 + (if l.2 then 1 else 0)

/-- A clause is a meet of literals: kept sorted and duplicate-free. -/
abbrev Clause := List Lit

def clauseInsert (l : Lit) : Clause → Clause
  | [] => [l]
  | x :: xs =>
    if litKey l < litKey x then l :: x :: xs
    else if litKey l == litKey x then x :: xs
    else x :: clauseInsert l xs

def clauseUnion (c d : Clause) : Clause := c.foldr clauseInsert d

/-- `c` subsumes `d` if `c ⊆ d` (then `c ∨ d = c`, so `d` is redundant). -/
def clauseSubsumes (c d : Clause) : Bool := c.all (fun l => d.contains l)

/-- A DNF is a join of clauses: `[]` is `0`, `[[]]` is `1`. -/
abbrev Dnf := List Clause

def clauseListKey : Clause → List Nat := List.map litKey

def keysLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs => a < b || (a == b && keysLt as bs)

def clauseLt (c d : Clause) : Bool := keysLt (clauseListKey c) (clauseListKey d)

def dnfSortInsert (c : Clause) : Dnf → Dnf
  | [] => [c]
  | x :: xs =>
    if clauseLt c x then c :: x :: xs
    else if clauseListKey c == clauseListKey x then x :: xs
    else x :: dnfSortInsert c xs

/-- Canonicalize: sort, deduplicate, and remove subsumed clauses
(antichain normal form of the free distributive lattice). -/
def dnfNorm (d : Dnf) : Dnf :=
  let sorted := d.foldr dnfSortInsert []
  sorted.filter fun c =>
    !(sorted.any fun c' => c' != c && clauseSubsumes c' c)

def dnfJoin (a b : Dnf) : Dnf := dnfNorm (a ++ b)

def dnfMeet (a b : Dnf) : Dnf :=
  dnfNorm ((a.map fun c => b.map fun d => clauseUnion c d).flatten)

/-- Negate a DNF: `¬⋁ᵢ ⋀ⱼ lᵢⱼ = ⋀ᵢ ⋁ⱼ ¬lᵢⱼ`, redistributed to DNF. -/
def dnfNeg (d : Dnf) : Dnf :=
  d.foldl (init := [[]]) fun acc c =>
    dnfNorm ((acc.map fun cl => c.map fun (l, b) => clauseInsert (l, !b) cl).flatten)

/-- Canonical DNF of an interval expression. -/
def dnf : IVal → Dnf
  | .zero => []
  | .one => [[]]
  | .var l => [[(l, false)]]
  | .max a b => dnfJoin (dnf a) (dnf b)
  | .min a b => dnfMeet (dnf a) (dnf b)
  | .neg a => dnfNeg (dnf a)

/-- Decidable semantic equality in the free De Morgan algebra. -/
def equiv (r s : IVal) : Bool := dnf r == dnf s

/-- Rebuild a canonical expression from one clause. -/
def ofClause : Clause → IVal
  | ls => ls.foldr
      (fun (v, n) acc => iMin (if n then iNeg (.var v) else .var v) acc)
      .one

/-- Rebuild a canonical interval expression from a canonical DNF. -/
def fromDnf : Dnf → IVal
  | cs => cs.foldr (fun c acc => iMax (ofClause c) acc) .zero

/-- Substitute an interval expression for the variable at level `l`. -/
def substLvl (l : Nat) (c : IVal) : IVal → IVal
  | .zero => .zero
  | .one => .one
  | .var m => if m == l then c else .var m
  | .max a b => iMax (substLvl l c a) (substLvl l c b)
  | .min a b => iMin (substLvl l c a) (substLvl l c b)
  | .neg a => iNeg (substLvl l c a)

/-- Upper bound on free levels: `1 + (max variable level)`, or `0` if the
expression mentions no variable.  Used by the value-level occurs-check
shortcut. -/
def levelBound : IVal → Nat
  | .zero | .one => 0
  | .var m => m + 1
  | .max a b | .min a b => Nat.max (levelBound a) (levelBound b)
  | .neg a => levelBound a

def mentions (l : Nat) : IVal → Bool
  | .zero | .one => false
  | .var m => m == l
  | .max a b | .min a b => mentions l a || mentions l b
  | .neg a => mentions l a

/-- Does the variable at level `l` occur with both polarities in the
canonical DNF?  (If not, `r` is monotone or antitone in that variable, and
universally quantifying a face over it reduces exactly to its endpoints.) -/
def mixedPolarity (l : Nat) (r : IVal) : Bool :=
  let lits := (dnf r).flatten
  lits.contains (l, false) && lits.contains (l, true)

def isZero (r : IVal) : Bool := dnf r == ([] : Dnf)

def isOne (r : IVal) : Bool := dnf r == ([[]] : Dnf)

end IVal

end Cubical
