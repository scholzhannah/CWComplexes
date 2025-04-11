import Mathlib.Topology.CWComplex.Classical.Basic

noncomputable section

namespace Topology

variable {X : Type*} [TopologicalSpace X]

class RelCWComplex.Subcomplex (C : Set X) {D : Set X} [RelCWComplex C D] (E : Set X) where
  I : Π n, Set (cell C n)
  closed : IsClosed E
  union : D ∪ ⋃ (n : ℕ) (j : I n), openCell (C := C) n j = E

instance CWComplex.instEmpty : CWComplex (∅ : Set X) := sorry

/-- Abbreviation for a subcomplex containing the CW complex. This is used to make type class
  inference work.-/
abbrev Sub (E C : Set X) : Set X := E

/-- `E ⇂ C` should be used to say that `E` is a subcomplex of `C`. -/
scoped infixr:35 " ⇂ "  => Sub

instance RelCWComplex.Subcomplex.instSubcomplex {C D : Set X} [T2Space X] [RelCWComplex C D] (E : Set X)
    [subcomplex : Subcomplex C E] : RelCWComplex (E ⇂ C) D := sorry

instance RelCWComplex.Subcomplex.iUnionSubcomplex {C D : Set X} [T2Space X] [RelCWComplex C D]
    (J : Type*) [Nonempty J] (sub : J → Set X) [cw : ∀ (j : J), Subcomplex C (sub j)] :
    Subcomplex C (⋃ (j : J), sub j) := sorry

instance RelCWComplex.Subcomplex.instSkeletonLT {C D : Set X} [T2Space X] [RelCWComplex C D] (n : ℕ∞) :
    Subcomplex C (skeletonLT C n) := sorry

set_option trace.Meta.synthInstance true in
open RelCWComplex in
instance {C D : Set X} [T2Space X] [RelCWComplex C D] (n : ℕ∞) :
  RelCWComplex (skeletonLT C n) D := inferInstance
