import CWcomplexes.Definition

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open Metric Set

namespace CWComplex

variable {X : Type*} [t : TopologicalSpace X] [T2Space X]

instance instCWComplexempty_test : CWComplex (∅ : Set X) := CWComplexFinite
  (cell := fun _ ↦ PEmpty)
  (map := fun _ i ↦ i.elim)
  (finitelevels := by rw [Filter.eventually_atTop]; use 0; exact fun _ _ ↦ instIsEmptyPEmpty)
  (finitecells := fun n ↦ Finite.of_fintype ((fun x ↦ PEmpty) n))
  (source_eq := fun _ _ ↦ by contradiction)
  (cont := fun _ _ ↦ by contradiction)
  (cont_symm := fun _ _ ↦ by contradiction)
  (pairwiseDisjoint' := by rw [PairwiseDisjoint, Set.Pairwise]; intro ⟨_, _⟩; contradiction)
  (mapsto := fun _ _ ↦ by contradiction)
  (union' := by simp [iUnion_of_empty, iUnion_empty])

-- is this really the theorem that should be used?
example (i : PEmpty) : False := by exact Aesop.BuiltinRules.pEmpty_false i

instance instCWComplexempty : CWComplex (∅ : Set X) where
  cell n := PEmpty
  map _ i := (Aesop.BuiltinRules.pEmpty_false i).elim
  source_eq n i := by contradiction
  cont n i := by contradiction
  cont_symm n i := by contradiction
  pairwiseDisjoint' := by
    rw [PairwiseDisjoint, Set.Pairwise]
    intro ⟨_, _⟩
    contradiction
  mapsto n i := by contradiction
  closed' A := by
    intro Aempty
    rw [subset_empty_iff] at Aempty
    constructor
    · intro _ _ _
      contradiction
    · intro _
      rw [Aempty]
      exact isClosed_empty
  union' := by simp only [iUnion_of_empty, iUnion_empty]

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
  pairwiseDisjoint' := by
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
  closed' A Asub := by
    constructor
    · intro closedA n j
      rcases n with rfl | n
      · simp [PartialEquiv.const]
        exact IsClosed.inter closedA isClosed_singleton
      · contradiction
    · intro _
      exact Set.Subsingleton.isClosed (Set.subsingleton_of_subset_singleton Asub)
  union' := by
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

example : (sphere 0 1 : Set ℝ) = {-1, 1} := by
  ext x
  simp [abs]
  aesop



  sorry


instance instCWComplexinterval_test: CWComplex (Set.Icc (-1) 1 : Set ℝ) := CWComplexFinite
  (cell := fun n ↦ match n with
    | 0 => Fin 2
    | 1 => Fin 1
    | (m + 2) => Empty
  )
  (map := fun n i ↦ match n with
    | 0 =>
      match i with
        | 0 => PartialEquiv.const ![] (-1)
        | 1 => PartialEquiv.const ![] 1
    | 1 => (IsometryEquiv.funUnique (Fin 1) ℝ).toPartialEquivOfImageEq (closedBall 0 1)
      (Set.Icc (-1) 1)
      (by rw [IsometryEquiv.coe_toEquiv, IsometryEquiv.image_closedBall,
        IsometryEquiv.funUnique_toFun, Pi.zero_apply, Real.closedBall_eq_Icc, zero_sub, zero_add])
    | (m + 2) => i.elim
  )
  (finitelevels := by
    rw [Filter.eventually_atTop]
    use 2
    intro n nge2
    simp only
    split
    · simp only [ge_iff_le, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero] at nge2
    · simp only [ge_iff_le, Nat.not_ofNat_le_one] at nge2
    · exact instIsEmptyEmpty
  )
  (finitecells := fun n ↦ match n with
    | 0 => Finite.of_fintype _
    | 1 => Finite.of_fintype _
    | (m + 2) => Finite.of_fintype _
  )
  (source_eq := fun n i ↦
    match n with
    | 0 =>
      match i with
      | 0 => by
        simp only [PartialEquiv.const, Matrix.empty_eq, closedBall, dist_self, zero_le_one,
          setOf_true]
        exact toFinset_eq_univ.mp rfl
      | 1 => by
        simp only [PartialEquiv.const, Matrix.empty_eq, closedBall, dist_self, zero_le_one,
          setOf_true]
        exact toFinset_eq_univ.mp rfl
    | 1 => rfl
    | (m + 2) => i.elim
  )
  (cont := fun n i ↦
    match n with
    | 0 =>
      match i with
      | 0 => by simp only [Matrix.empty_eq, closedBall_zero_dim_singleton, continuousOn_singleton]
      | 1 => by simp only [Matrix.empty_eq, closedBall_zero_dim_singleton, continuousOn_singleton]
    | 1 => ((IsometryEquiv.funUnique (Fin 1) ℝ).continuous).continuousOn
    | (m + 2) => i.elim
  )
  (cont_symm := fun n i ↦
    match n with
    | 0 =>
      match i with
      | 0 => by
        simp only [PartialEquiv.const, Function.const_zero, Matrix.zero_empty,
          PartialEquiv.coe_symm_mk, continuousOn_singleton]
      | 1 => by
        simp only [PartialEquiv.const, Function.const_zero, Matrix.zero_empty,
          PartialEquiv.coe_symm_mk, continuousOn_singleton]
    | 1 => ((IsometryEquiv.funUnique (Fin 1) ℝ).symm.continuous).continuousOn
    | (m + 2) => i.elim
  )
  (pairwiseDisjoint' := by
    rw [PairwiseDisjoint, Set.Pairwise]
    intro ⟨n, j⟩ _ ⟨m, i⟩ _ ne
    simp only [Matrix.zero_empty, disjoint_iff, inf_eq_inter, bot_eq_empty]
    exact match n with
      | 0 => match m with
        | 0 => match j with
          | 0 => match i with
            | 0 => (ne rfl).elim
            | 1 => by simp [PartialEquiv.const]
          | 1 => match i with
            | 0 => by simp [PartialEquiv.const]
            | 1 => (ne rfl).elim
        | 1 => match j with
          | 0 => by
            simp_rw [Equiv.toPartialEquivOfImageEq_apply, IsometryEquiv.coe_toEquiv,
              IsometryEquiv.image_ball, IsometryEquiv.funUnique_toFun]
            simp [Matrix.empty_eq, PartialEquiv.const]
          | 1 => by
            simp_rw [Equiv.toPartialEquivOfImageEq_apply, IsometryEquiv.coe_toEquiv,
              IsometryEquiv.image_ball, IsometryEquiv.funUnique_toFun]
            simp [Matrix.empty_eq, PartialEquiv.const]
        | (l + 2) => i.elim
      | 1 => match m with
        | 0 => match i with
          | 0 => by
            simp_rw [Equiv.toPartialEquivOfImageEq_apply, IsometryEquiv.coe_toEquiv,
              IsometryEquiv.image_ball, IsometryEquiv.funUnique_toFun]
            simp [Matrix.empty_eq, PartialEquiv.const]
          | 1 => by
            simp_rw [Equiv.toPartialEquivOfImageEq_apply, IsometryEquiv.coe_toEquiv,
              IsometryEquiv.image_ball, IsometryEquiv.funUnique_toFun]
            simp [Matrix.empty_eq, PartialEquiv.const]
        | 1 => by simp only [Fin.eq_zero, Fin.isValue, ne_eq, not_true_eq_false] at ne
        | (l + 2) => i.elim
      | (l + 2) => j.elim
  )
  (mapsto := fun n i ↦ match n with
    | 0 => match i with
      | 0 => by simp [sphere_zero_dim_empty]
      | 1 => by simp [sphere_zero_dim_empty]
    | 1 => by
      intro x
      simp [mapsTo', IsometryEquiv.image_sphere]
      sorry
    | (m + 2) => i.elim
  )
  (union' := by
    apply subset_antisymm
    · apply iUnion_subset fun n ↦ iUnion_subset fun i ↦ ?_
      exact match n with
        | 0 => match i with
          | 0 => by simp [Matrix.empty_eq, PartialEquiv.const]
          | 1 => by simp [Matrix.empty_eq, PartialEquiv.const]
        | 1 => by
          rw [Equiv.toPartialEquivOfImageEq_apply, IsometryEquiv.coe_toEquiv,
            IsometryEquiv.image_closedBall, IsometryEquiv.funUnique_toFun, Pi.zero_apply,
            Real.closedBall_eq_Icc, zero_sub, zero_add]
        | (m + 2 )=> i.elim
    · apply subset_iUnion_of_subset 1
      apply subset_iUnion_of_subset 0
      rw [Equiv.toPartialEquivOfImageEq_apply, IsometryEquiv.coe_toEquiv,
        IsometryEquiv.image_closedBall, IsometryEquiv.funUnique_toFun, Pi.zero_apply,
        Real.closedBall_eq_Icc, zero_sub, zero_add]
  )

instance instCWComplexinterval: CWComplex (Set.Icc (-1) 1 : Set ℝ) where
  cell :=
    fun n ↦ match n with
      | 0 => Fin 2
      | 1 => Fin 1
      | (m + 2) => Empty
  map n i := match n with
    | 0 =>
      match i with
        | 0 => PartialEquiv.const ![] (-1)
        | 1 => PartialEquiv.const ![] 1
    | 1 => (IsometryEquiv.funUnique (Fin 1) ℝ).toPartialEquivOfImageEq (closedBall 0 1)
      (Set.Icc (-1) 1)
      (by rw [IsometryEquiv.coe_toEquiv, IsometryEquiv.image_closedBall,
        IsometryEquiv.funUnique_toFun, Pi.zero_apply, Real.closedBall_eq_Icc, zero_sub, zero_add])
    | (m + 2) => i.elim
  source_eq n i := match n with
    | 0 =>
      match i with
      | 0 => by
        simp only [PartialEquiv.const, Matrix.empty_eq, closedBall, dist_self, zero_le_one,
          setOf_true]
        exact toFinset_eq_univ.mp rfl
      | 1 => by
        simp only [PartialEquiv.const, Matrix.empty_eq, closedBall, dist_self, zero_le_one,
          setOf_true]
        exact toFinset_eq_univ.mp rfl
    | 1 => rfl
    | (m + 2) => by contradiction
  cont n i := match n with
    | 0 =>
      match i with
      | 0 => by simp only [Matrix.empty_eq, closedBall_zero_dim_singleton, continuousOn_singleton]
      | 1 => by simp only [Matrix.empty_eq, closedBall_zero_dim_singleton, continuousOn_singleton]
    | 1 => ((IsometryEquiv.funUnique (Fin 1) ℝ).continuous).continuousOn
    | (m + 2) => by contradiction
  cont_symm n i := match n with
    | 0 =>
      match i with
      | 0 => by
        simp only [PartialEquiv.const, Function.const_zero, Matrix.zero_empty,
          PartialEquiv.coe_symm_mk, continuousOn_singleton]
      | 1 => by
        simp only [PartialEquiv.const, Function.const_zero, Matrix.zero_empty,
          PartialEquiv.coe_symm_mk, continuousOn_singleton]
    | 1 => ((IsometryEquiv.funUnique (Fin 1) ℝ).symm.continuous).continuousOn
    | (m + 2) => by contradiction
  pairwiseDisjoint' := by
    rw [PairwiseDisjoint, Set.Pairwise]
    intro ⟨n, j⟩ _ ⟨m, i⟩ _ ne
    simp only [Matrix.zero_empty, disjoint_iff, inf_eq_inter, bot_eq_empty]
    exact match n with
      | 0 => match m with
        | 0 => match j with
          | 0 => match i with
            | 0 => (ne rfl).elim
            | 1 => by simp [PartialEquiv.const]
          | 1 => match i with
            | 0 => by simp [PartialEquiv.const]
            | 1 => (ne rfl).elim
        | 1 => match j with
          | 0 => by
            simp_rw [Equiv.toPartialEquivOfImageEq_apply, IsometryEquiv.coe_toEquiv,
              IsometryEquiv.image_ball, IsometryEquiv.funUnique_toFun]
            simp [Matrix.empty_eq, PartialEquiv.const]
          | 1 => by
            simp_rw [Equiv.toPartialEquivOfImageEq_apply, IsometryEquiv.coe_toEquiv,
              IsometryEquiv.image_ball, IsometryEquiv.funUnique_toFun]
            simp [Matrix.empty_eq, PartialEquiv.const]
        | (l + 2) => i.elim
      | 1 => match m with
        | 0 => match i with
          | 0 => by
            simp_rw [Equiv.toPartialEquivOfImageEq_apply, IsometryEquiv.coe_toEquiv,
              IsometryEquiv.image_ball, IsometryEquiv.funUnique_toFun]
            simp [Matrix.empty_eq, PartialEquiv.const]
          | 1 => by
            simp_rw [Equiv.toPartialEquivOfImageEq_apply, IsometryEquiv.coe_toEquiv,
              IsometryEquiv.image_ball, IsometryEquiv.funUnique_toFun]
            simp [Matrix.empty_eq, PartialEquiv.const]
        | 1 => by simp only [Fin.eq_zero, Fin.isValue, ne_eq, not_true_eq_false] at ne
        | (l + 2) => i.elim
      | (l + 2) => j.elim
  mapsto := sorry
  closed' := sorry
  union' := by
    apply subset_antisymm
    · apply iUnion_subset fun n ↦ iUnion_subset fun i ↦ ?_
      exact match n with
        | 0 => match i with
          | 0 => by simp [Matrix.empty_eq, PartialEquiv.const]
          | 1 => by simp [Matrix.empty_eq, PartialEquiv.const]
        | 1 => by
          rw [Equiv.toPartialEquivOfImageEq_apply, IsometryEquiv.coe_toEquiv,
            IsometryEquiv.image_closedBall, IsometryEquiv.funUnique_toFun, Pi.zero_apply,
            Real.closedBall_eq_Icc, zero_sub, zero_add]
        | (m + 2 )=> i.elim
    · apply subset_iUnion_of_subset 1
      apply subset_iUnion_of_subset 0
      rw [Equiv.toPartialEquivOfImageEq_apply, IsometryEquiv.coe_toEquiv,
        IsometryEquiv.image_closedBall, IsometryEquiv.funUnique_toFun, Pi.zero_apply,
        Real.closedBall_eq_Icc, zero_sub, zero_add]
