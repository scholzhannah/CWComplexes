import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Homotopy.HomotopyGroup

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

-- I feel like this proof should be wayyy shorter. Correct usage of protected?
lemma aux1 (l : ℕ) {X : Type*} {s : ℕ →  Type*} (Y : (m : ℕ) → s m → Set X):
    ⋃ m, ⋃ (_ : m < Nat.succ l), ⋃ j, Y m j = (⋃ (j : s l), Y l j) ∪ ⋃ m, ⋃ (_ : m < l), ⋃ j, Y m j := by
  ext x
  simp only [Set.mem_iUnion, exists_prop, Set.mem_union]
  constructor
  · intro ⟨i, ⟨iltsuccl, h⟩⟩
    apply Order.le_of_lt_succ at iltsuccl
    by_cases h' : i = l
    · left
      rw [h'] at h
      exact h
    · push_neg at h'
      have := LE.le.lt_of_ne iltsuccl h'
      right
      use i
  · intro h
    rcases h with h | h
    · use l
      exact ⟨Nat.lt_succ_self l, h⟩
    · rcases h with ⟨i, iltl, h⟩
      use i
      exact ⟨lt_trans iltl (Nat.lt_succ_self l), h⟩
