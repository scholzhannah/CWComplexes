import CWcomplexes.Constructions

/-!
# Examples of CW-complexes

In this file we present some examples of CW-complexes:

* `instCWComplexEmpty`: The empty set is a CW-complex.
* `instCWComplexsingleton`: A singleton is a CW-complex.
* `instCWComplexIcc`: The interval `Icc a b` in `ℝ` is a CW-complex.
-/
noncomputable section

open Metric Set

namespace CWComplex

variable {X : Type*} [t : TopologicalSpace X] [T2Space X]

/-- The empty set is a CW-complex.-/
instance instCWComplexEmpty : CWComplex (∅ : Set X) := CWComplexFinite
  (cell := fun _ ↦ PEmpty)
  (map := fun _ i ↦ i.elim)
  (eventually_isEmpty_cell := by
    rw [Filter.eventually_atTop]
    use 0
    exact fun _ _ ↦ instIsEmptyPEmpty)
  (finite_cell := fun n ↦ Finite.of_fintype ((fun _ ↦ PEmpty) n))
  (source_eq := fun _ i ↦ i.elim)
  (cont := fun _ i ↦ i.elim)
  (cont_symm := fun _ i ↦ i.elim)
  (pairwiseDisjoint' := by rw [PairwiseDisjoint, Set.Pairwise]; intro ⟨_, i⟩; exact i.elim)
  (mapsto := fun _ i ↦ i.elim)
  (union' := by simp [iUnion_of_empty, iUnion_empty])

variable [T1Space X]

/-- A singleton is a CW-complex.-/
instance instCWComplexsingleton (x : X) : CWComplex {x} := CWComplexFinite
  (cell := fun n ↦ match n with
    | 0 => PUnit
    | (_ + 1) => PEmpty)
  (map := fun n i ↦
    match n with
    | 0 => PartialEquiv.const ![] x
    | (_ + 1) => i.elim)
  (eventually_isEmpty_cell := by
    rw [Filter.eventually_atTop]
    use 1
    intro b beq1
    simp only
    split
    · contradiction
    · exact instIsEmptyPEmpty)
  (finite_cell := fun n ↦ match n with
    | 0 => Finite.of_fintype _
    | (_ + 1) => Finite.of_fintype _)
  (source_eq := fun n i ↦ match n with
    | 0 => by
      simp only [PartialEquiv.const, closedBall, Matrix.empty_eq, dist_self, zero_le_one,
        setOf_true, eq_univ_iff_forall]
      intro _
      simp only [Matrix.empty_eq, mem_singleton_iff]
    | (_ + 1) => i.elim)
  (cont := fun n i ↦ match n with | 0 => continuousOn_const | (m + 1) => i.elim)
  (cont_symm := fun n i ↦ match n with
    | 0 => continuousOn_const
    | (_ + 1) => i.elim)
  (pairwiseDisjoint' := by
    rw [PairwiseDisjoint, Set.Pairwise]
    exact fun ⟨n, j⟩ _ ⟨m, i⟩ _ ne ↦  match n with
      | 0 => match m with
        | 0 => (ne rfl).elim
        | (_ + 1) => i.elim
      | (_ + 1) => j.elim)
  (mapsto := fun n i ↦ match n with
    | 0 => by simp only [Matrix.zero_empty, sphere_zero_dim_empty, not_lt_zero', iUnion_of_empty,
      iUnion_empty, mapsTo_empty_iff]
    | (_ + 1) => i.elim)
  (union' := by
    ext y
    simp only [mem_iUnion, mem_singleton_iff]
    constructor
    · exact fun ⟨n, j, _⟩ ↦  match n with
        | 0 => by simp_all only [PartialEquiv.const, Function.const_apply, Matrix.zero_empty,
          nonempty_closedBall, zero_le_one, Nonempty.image_const, mem_singleton_iff]
        | (_ + 1) => j.elim
    · intro eq
      use 0, default
      simp only [eq, PartialEquiv.const, Function.const_apply, Matrix.zero_empty,
        nonempty_closedBall, zero_le_one, Nonempty.image_const, mem_singleton_iff])

/-- The interval `Icc (-1) 1` in `ℝ` is a CW-complex.-/
instance instCWComplexstandardinterval: CWComplex (Icc (-1) 1 : Set ℝ) := CWComplexFinite
  (cell := fun n ↦ match n with
    | 0 => Fin 2
    | 1 => Fin 1
    | (_ + 2) => Empty
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
    | (_ + 2) => i.elim
  )
  (eventually_isEmpty_cell := by
    rw [Filter.eventually_atTop]
    use 2
    intro n nge2
    simp only
    split
    · contradiction
    · contradiction
    · exact instIsEmptyEmpty
  )
  (finite_cell := fun n ↦ match n with
    | 0 => Finite.of_fintype _
    | 1 => Finite.of_fintype _
    | (_ + 2) => Finite.of_fintype _
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
    | (_ + 2) => i.elim
  )
  (cont := fun n i ↦
    match n with
    | 0 =>
      match i with
      | 0 => by simp only [Matrix.empty_eq, closedBall_zero_dim_singleton, continuousOn_singleton]
      | 1 => by simp only [Matrix.empty_eq, closedBall_zero_dim_singleton, continuousOn_singleton]
    | 1 => ((IsometryEquiv.funUnique (Fin 1) ℝ).continuous).continuousOn
    | (_ + 2) => i.elim
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
    | (_ + 2) => i.elim
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
            | 1 => by
              simp only [PartialEquiv.const, Function.const_apply, Matrix.zero_empty,
                nonempty_ball, zero_lt_one, Nonempty.image_const, Function.const_one, Pi.one_apply,
                inter_singleton_eq_empty, mem_singleton_iff]
              linarith
          | 1 => match i with
            | 0 => by
              simp only [PartialEquiv.const, Function.const_one, Pi.one_apply,
                Matrix.zero_empty, nonempty_ball, zero_lt_one, Nonempty.image_const,
                Function.const_apply, inter_singleton_eq_empty, mem_singleton_iff]
              linarith
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
        | (_ + 2) => i.elim
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
        | (_ + 2) => i.elim
      | (_ + 2) => j.elim
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
    | (_ + 2) => i.elim
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
        | (_ + 2)=> i.elim
    · apply subset_iUnion_of_subset 1
      apply subset_iUnion_of_subset 0
      rw [Equiv.toPartialEquivOfImageEq_apply, IsometryEquiv.coe_toEquiv,
        IsometryEquiv.image_closedBall, IsometryEquiv.funUnique_toFun, Pi.zero_apply,
        Real.closedBall_eq_Icc, zero_sub, zero_add]
  )

/-- The canonical CW-complex structure on `Icc a b` in `ℝ` for `a < b`.-/
def CWComplexIcc_of_lt {a b : ℝ} (lt : a < b) : CWComplex (Icc a b : Set ℝ) :=
  CWComplex_of_Homeomorph (Icc (-1) 1 : Set ℝ) (Icc a b)
  (affineHomeomorph ((b - a) / 2) ((a + b) / 2) (by linarith))
  (by
    calc
      (affineHomeomorph ((b - a) / 2) ((a + b) / 2) (by intro; linarith)) '' Icc (-1) 1
      _ = (affineHomeomorph ((b - a) / 2) ((a + b) / 2) (by intro; linarith)) ''
          ((affineHomeomorph 2 (-1) two_ne_zero) '' Icc 0 1) := by
        congrm (affineHomeomorph ((b - a) / 2) ((a + b) / 2) (by intro; linarith)) '' ?_
        rw [affineHomeomorph_image_I _ _ zero_lt_two]
        norm_num
      _ = (affineHomeomorph 2 (-1) two_ne_zero).trans
          (affineHomeomorph ((b - a) / 2) ((a + b) / 2) (by intro; linarith)) '' Icc 0 1 := by
        simp only [affineHomeomorph_apply, image_image, Homeomorph.trans_apply]
      _ = Icc a b := by
        rw [affineHomeomorph_trans, affineHomeomorph_image_I _ _ (by linarith)]
        ring_nf
  )

/-- The interval `Icc a b` in `ℝ` is a CW-complex.-/
instance instCWComplexIcc (a b : ℝ) : CWComplex (Icc a b : Set ℝ) :=
  if lt1 : a < b then CWComplexIcc_of_lt lt1
    else if lt2 : b < a then Icc_eq_empty_of_lt lt2 ▸ instCWComplexEmpty
      else Linarith.eq_of_not_lt_of_not_gt _ _ lt1 lt2 ▸ Icc_self a ▸ instCWComplexsingleton a
