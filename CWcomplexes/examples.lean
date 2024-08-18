import CWcomplexes.Constructions

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open Metric Set

namespace CWComplex

variable {X : Type*} [t : TopologicalSpace X] [T2Space X]

instance instCWComplexempty : CWComplex (∅ : Set X) := CWComplexFinite
  (cell := fun _ ↦ PEmpty)
  (map := fun _ i ↦ i.elim)
  (finitelevels := by rw [Filter.eventually_atTop]; use 0; exact fun _ _ ↦ instIsEmptyPEmpty)
  (finitecells := fun n ↦ Finite.of_fintype ((fun x ↦ PEmpty) n))
  (source_eq := fun _ i ↦ i.elim)
  (cont := fun _ i ↦ i.elim)
  (cont_symm := fun _ i ↦ i.elim)
  (pairwiseDisjoint' := by rw [PairwiseDisjoint, Set.Pairwise]; intro ⟨_, i⟩; exact i.elim)
  (mapsto := fun _ i ↦ i.elim)
  (union' := by simp [iUnion_of_empty, iUnion_empty])

variable [T1Space X]

instance instCWComplexsingleton (x : X) : CWComplex {x} := CWComplexFinite
  (cell := fun n ↦ match n with
    | 0 => PUnit
    | (m + 1) => PEmpty)
  (map := fun n i ↦
    match n with
    | 0 => PartialEquiv.const ![] x
    | (m + 1) => i.elim)
  (finitelevels := by
    rw [Filter.eventually_atTop]
    use 1
    intro b beq1
    simp only
    split
    · contradiction
    · exact instIsEmptyPEmpty)
  (finitecells := fun n ↦ match n with
    | 0 => Finite.of_fintype _
    | (m + 1) => Finite.of_fintype _)
  (source_eq := fun n i ↦ match n with
    | 0 => by
      simp only [PartialEquiv.const, closedBall, Matrix.empty_eq, dist_self, zero_le_one,
        setOf_true, eq_univ_iff_forall]
      intro _
      simp only [Matrix.empty_eq, mem_singleton_iff]
    | (m + 1) => i.elim)
  (cont := fun n i ↦ match n with | 0 => continuousOn_const | (m + 1) => i.elim)
  (cont_symm := fun n i ↦ match n with
    | 0 => continuousOn_const
    | (m + 1) => i.elim)
  (pairwiseDisjoint' := by
    rw [PairwiseDisjoint, Set.Pairwise]
    exact fun ⟨n, j⟩ _ ⟨m, i⟩ _ ne ↦  match n with
      | 0 => match m with
        | 0 => (ne rfl).elim
        | (l + 1) => i.elim
      | (l + 1) => j.elim)
  (mapsto := fun n i ↦ match n with
    | 0 => by simp only [Matrix.zero_empty, sphere_zero_dim_empty, not_lt_zero', iUnion_of_empty,
      iUnion_empty, mapsTo_empty_iff]
    | (m + 1) => i.elim)
  (union' := by
    ext y
    simp only [mem_iUnion, mem_singleton_iff]
    constructor
    · exact fun ⟨n, j, hn⟩ ↦  match n with
        | 0 => by simp_all only [PartialEquiv.const, Function.const_apply, Matrix.zero_empty,
          nonempty_closedBall, zero_le_one, Nonempty.image_const, mem_singleton_iff]
        | (m + 1) => j.elim
    · intro eq
      use 0, default
      simp only [eq, PartialEquiv.const, Function.const_apply, Matrix.zero_empty,
        nonempty_closedBall, zero_le_one, Nonempty.image_const, mem_singleton_iff])

instance instCWComplexstandardinterval_test: CWComplex (Icc (-1) 1 : Set ℝ) := CWComplexFinite
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
    · contradiction
    · contradiction
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
      simp_rw [mapsTo', Equiv.toPartialEquivOfImageEq_apply, IsometryEquiv.coe_toEquiv,
        IsometryEquiv.image_sphere, IsometryEquiv.funUnique_toFun, Pi.zero_apply, Nat.lt_one_iff, iUnion_iUnion_eq_left, Matrix.zero_empty]
      intro x xmem
      simp only [mem_sphere_iff_norm, norm, sub_zero] at xmem
      replace xmem := eq_or_eq_neg_of_abs_eq xmem
      rw [mem_iUnion]
      rcases xmem with xeq | xeq
      · subst x
        use 1
        simp only [PartialEquiv.const, Function.const_one, Pi.one_apply, nonempty_closedBall,
          zero_le_one, Nonempty.image_const, mem_singleton_iff]
      · subst x
        use 0
        simp only [PartialEquiv.const, Function.const_apply, nonempty_closedBall, zero_le_one,
          Nonempty.image_const, mem_singleton_iff]
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

instance instCWComplexinterval_test (a b : ℝ) (lt : a < b) : CWComplex (Icc a b : Set ℝ) :=
  CWComplex_of_Homeomorph (Icc (-1) 1 : Set ℝ) (Icc a b)
  (affineHomeomorph ((b - a) / 2) ((a + b) / 2) (sorry)) (sorry)

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
