import CWcomplexes.Relative.RelConstructions

/-!
# Examples of CW-complexes

In this file we present some examples of CW-complexes:

* `instCWComplexEmpty`: The empty set is a CW-complex.
* `instCWComplexsingleton`: A singleton is a CW-complex.
* `instCWComplexIcc`: The interval `Icc a b` in `ℝ` is a CW-complex.
-/
noncomputable section

open Metric Set

namespace ClasCWComplex

variable {X : Type*} [t : TopologicalSpace X] [T2Space X]

-- should this be a separate instance to the one below?
/-- The empty set is a CW-complex.-/
@[simp]
instance instEmpty : ClasCWComplex (∅ : Set X) := mkFinite ∅
  (cell := fun _ ↦ PEmpty)
  (map := fun _ i ↦ i.elim)
  (eventually_isEmpty_cell := by
    rw [Filter.eventually_atTop]
    use 0
    exact fun b a ↦ PEmpty.instIsEmpty)
  (finite_cell := fun n ↦ Finite.of_fintype ((fun _ ↦ PEmpty) n))
  (source_eq := fun _ i ↦ i.elim)
  (continuousOn := fun _ i ↦ i.elim)
  (continuousOn_symm := fun _ i ↦ i.elim)
  (pairwiseDisjoint' := by rw [PairwiseDisjoint, Set.Pairwise]; intro ⟨_, i⟩; exact i.elim)
  (mapsto := fun _ i ↦ i.elim)
  (union' := by simp [iUnion_of_empty, iUnion_empty])

instance Finite_instEmpty : Finite (∅ : Set X) := Finite_mkFinite ∅
  (cell := fun _ ↦ PEmpty)
  (map := fun _ i ↦ i.elim)
  (eventually_isEmpty_cell := by
    rw [Filter.eventually_atTop]
    use 0
    exact fun b a ↦ PEmpty.instIsEmpty)
  (finite_cell := fun n ↦ Finite.of_fintype ((fun _ ↦ PEmpty) n))
  (source_eq := fun _ i ↦ i.elim)
  (continuousOn := fun _ i ↦ i.elim)
  (continuousOn_symm := fun _ i ↦ i.elim)
  (pairwiseDisjoint' := by rw [PairwiseDisjoint, Set.Pairwise]; intro ⟨_, i⟩; exact i.elim)
  (mapsto := fun _ i ↦ i.elim)
  (union' := by simp [iUnion_of_empty, iUnion_empty])

instance instFiniteSet (C : Set X) [_root_.Finite C] : ClasCWComplex C := mkFinite C
  (cell := fun n ↦ match n with
    | 0 => C
    | (_ + 1) => PEmpty)
  (map := fun n i ↦ match n with
    | 0 => PartialEquiv.single ![] i
    | (_ + 1) => i.elim)
  (eventually_isEmpty_cell := by
    rw [Filter.eventually_atTop]
    use 1
    intro b beq1
    simp only
    split
    · contradiction
    · infer_instance)
  (finite_cell := fun n ↦ match n with
    | 0 => inferInstance
    | (_ + 1) => inferInstance)
  (source_eq := fun n i ↦ match n with
    | 0 => by
      simp [PartialEquiv.single, closedBall, Matrix.empty_eq, eq_univ_iff_forall]
    | (_ + 1) => i.elim)
  (continuousOn := fun n i ↦ match n with
    | 0 => continuousOn_const
    | (m + 1) => i.elim)
  (continuousOn_symm := fun n i ↦ match n with
    | 0 => continuousOn_const
    | (_ + 1) => i.elim)
  (pairwiseDisjoint' := by
    simp_rw [PairwiseDisjoint, Set.Pairwise, Function.onFun]
    exact fun ⟨n, j⟩ _ ⟨m, i⟩ _ ne ↦  match n with
      | 0 => match m with
        | 0 => by simp_all [Subtype.coe_ne_coe]
        | (_ + 1) => i.elim
      | (_ + 1) => j.elim)
  (mapsto := fun n i ↦ match n with
    | 0 => by simp [Matrix.zero_empty, sphere_eq_empty_of_subsingleton]
    | (_ + 1) => i.elim)
  (union' := by
    ext x
    simp only [mem_iUnion]
    constructor
    · intro ⟨n, i, hi⟩
      exact match n with
        | 0 => by simp_all
        | (_ + 1) => i.elim
    · intro hx
      use 0, ⟨x, hx⟩
      simp)

instance Finite_instFiniteSet (C : Set X) [_root_.Finite C] : Finite C := Finite_mkFinite C
  (cell := fun n ↦ match n with
    | 0 => C
    | (_ + 1) => PEmpty)
  (map := fun n i ↦ match n with
    | 0 => PartialEquiv.single ![] i
    | (_ + 1) => i.elim)
  (eventually_isEmpty_cell := by
    rw [Filter.eventually_atTop]
    use 1
    intro b beq1
    simp only
    split
    · contradiction
    · infer_instance)
  (finite_cell := fun n ↦ match n with
    | 0 => inferInstance
    | (_ + 1) => inferInstance)
  (source_eq := fun n i ↦ match n with
    | 0 => by
      simp [PartialEquiv.single, closedBall, Matrix.empty_eq, eq_univ_iff_forall]
    | (_ + 1) => i.elim)
  (continuousOn := fun n i ↦ match n with
    | 0 => continuousOn_const
    | (m + 1) => i.elim)
  (continuousOn_symm := fun n i ↦ match n with
    | 0 => continuousOn_const
    | (_ + 1) => i.elim)
  (pairwiseDisjoint' := by
    simp_rw [PairwiseDisjoint, Set.Pairwise, Function.onFun]
    exact fun ⟨n, j⟩ _ ⟨m, i⟩ _ ne ↦  match n with
      | 0 => match m with
        | 0 => by simp_all [Subtype.coe_ne_coe]
        | (_ + 1) => i.elim
      | (_ + 1) => j.elim)
  (mapsto := fun n i ↦ match n with
    | 0 => by simp [Matrix.zero_empty, sphere_eq_empty_of_subsingleton]
    | (_ + 1) => i.elim)
  (union' := by
    ext x
    simp only [mem_iUnion]
    constructor
    · intro ⟨n, i, hi⟩
      exact match n with
        | 0 => by simp_all
        | (_ + 1) => i.elim
    · intro hx
      use 0, ⟨x, hx⟩
      simp)

example (x : X) : ClasCWComplex {x} := inferInstance

def instIccLT {a b : ℝ} (lt : a < b) : ClasCWComplex (Icc a b : Set ℝ) :=
  let map' := (((IsometryEquiv.funUnique (Fin 1) ℝ).toEquiv.trans
    (affineHomeomorph ((b - a) / 2) ((a + b) / 2) (by linarith))).toPartialEquivOfImageEq
    (closedBall 0 1) (Icc a b) (by
      rw [Equiv.coe_trans, image_comp, IsometryEquiv.coe_toEquiv, IsometryEquiv.image_closedBall,
        IsometryEquiv.funUnique_apply, Pi.zero_apply, Real.closedBall_eq_Icc, zero_sub, zero_add,
        EquivLike.coe_coe, affineHomeomorph_image_Icc _ _ _ _ (by linarith)]
      ring_nf))
  let _ := attachCellFiniteType {a, b} (n := 1)
    map'
    (source_eq' := sorry)
    (continuousOn' := sorry)
    (continuousOn_symm' := sorry)
    (disjoint' := sorry)
    (mapsto' := sorry)
  ofEq (map' '' closedBall 0 1 ∪ {a, b}) ∅ sorry sorry


end ClasCWComplex
