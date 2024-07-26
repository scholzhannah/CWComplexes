import CWcomplexes.Definition

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open Metric Set

namespace CWComplex

variable {X : Type*} [t : TopologicalSpace X]

instance instCWComplexempty : CWComplex (∅ : Set X) where
  cell n := PEmpty
  map n i := by contradiction
  source_eq n i := by contradiction
  cont n i := by contradiction
  cont_symm n i := by contradiction
  pairwiseDisjoint := by
    rw [PairwiseDisjoint, Set.Pairwise]
    intro ⟨_, _⟩
    contradiction
  mapsto n i := by contradiction
  closed A := by
    intro Aempty
    rw [subset_empty_iff] at Aempty
    constructor
    · intro _ _ _
      contradiction
    · intro _
      rw [Aempty]
      exact isClosed_empty
  union := by simp only [iUnion_of_empty, iUnion_empty]

variable [T1Space X]

instance instCWComplexsingleton (x : X) : CWComplex {x} where
  cell n := match n with
    | 0 => PUnit
    | (m + 1) => PEmpty
  map n i := match n with
    | 0 => PartialEquiv.const ![] x
    | (m + 1) => by contradiction
  source_eq n i := match n with
    | 0 => by
      simp only [PartialEquiv.const, Matrix.empty_eq, closedBall, dist_self, zero_le_one, setOf_true]
      rw [Set.eq_univ_iff_forall]
      intro _
      simp only [Matrix.empty_eq, mem_singleton_iff]
    | (m + 1) => by contradiction
  cont n i := match n with
    | 0 => continuousOn_const
    | (m + 1) => by contradiction
  cont_symm n i := match n with
    | 0 => continuousOn_const
    | (m + 1) => by contradiction
  pairwiseDisjoint := by
    rw [PairwiseDisjoint, Set.Pairwise]
    intro ⟨n, j⟩ _ ⟨m, i⟩ _ ne
    rcases n with rfl | n
    · rcases m with rfl | m
      · contradiction
      contradiction
    contradiction
  mapsto n i := match n with
    | 0 => by
      let I m : Finset (match m with | 0 => PUnit.{u_1 + 1}| (m + 1) => PEmpty.{u_1 + 1}) := match m with
        | 0 => Finset.univ
        | (m + 1) => Finset.univ
      use I
      simp only [Matrix.zero_empty, sphere_zero_dim_empty, not_lt_zero', iUnion_of_empty,
        iUnion_empty, mapsTo_empty_iff]
    | (m + 1) => by contradiction
  closed A Asub := by
    constructor
    · intro closedA n j
      rcases n with rfl | n
      · simp [PartialEquiv.const]
        exact IsClosed.inter closedA isClosed_singleton
      · contradiction
    · intro _
      exact Set.Subsingleton.isClosed (Set.subsingleton_of_subset_singleton Asub)
  union := by
    ext y
    constructor
    · simp_rw [mem_iUnion]
      intro ⟨n, j, hn⟩
      rcases n with rfl | n
      · simp only [PartialEquiv.const, Function.const_apply, Matrix.zero_empty,
        nonempty_closedBall, zero_le_one, Nonempty.image_const, mem_singleton_iff] at hn ⊢
        exact hn
      · contradiction
    · intro eq
      rw [mem_singleton_iff] at eq
      subst eq
      simp only [mem_iUnion]
      use 0, default
      simp only [PartialEquiv.const, Function.const_apply, Matrix.zero_empty, nonempty_closedBall,
        zero_le_one, Nonempty.image_const, mem_singleton_iff]

instance instCWComplexinterval (a b : ℝ) :
    CWComplex (Set.Icc a b) where

  cell :=
    fun n ↦ match n with
      | 0 => Fin 2
      | 1 => Fin 1
      | (m + 2) => Empty
  map := sorry
  source_eq := sorry
  cont := sorry
  cont_symm := sorry
  pairwiseDisjoint := sorry
  mapsto := sorry
  closed := sorry
  union := sorry
