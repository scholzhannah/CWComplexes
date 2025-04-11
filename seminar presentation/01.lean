import Mathlib.Topology.CWComplex.Classical.Basic

noncomputable section

namespace Topology

open RelCWComplex

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

instance CWComplex.Subcomplex.instSubcomplex {C : Set X} [T2Space X] [CWComplex C] (E : Set X)
    [subcomplex : Subcomplex C E] : CWComplex (E ⇂ C) := sorry

instance RelCWComplex.Subcomplex.instSkeleton {C D : Set X} [T2Space X] [RelCWComplex C D] (n : ℕ∞) :
    Subcomplex C (skeleton C n) := sorry

instance {C D : Set X} [T2Space X] [RelCWComplex C D] (n : ℕ∞) :
  RelCWComplex (skeleton C n) D := RelCWComplex.Subcomplex.instSubcomplex (C := C) _

--set_option trace.Meta.synthInstance true in
instance {C D : Set X} [T2Space X] [RelCWComplex C D] (n : ℕ∞) :
  RelCWComplex (skeleton C n) D :=  sorry --inferInstance
