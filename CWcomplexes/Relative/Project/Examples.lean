import CWcomplexes.Relative.RelProduct
import Mathlib.Analysis.NormedSpace.HomeomorphBall
import Mathlib.Geometry.Manifold.Instances.Sphere


/-!
# Examples of CW-complexes

In this file we present some examples of CW-complexes:
## Main definitions
* `instEmpty`: The empty set is a CW-complex.
* `instFiniteSet`: Every finite set is a CW-complex.
* `instIcc`: The interval `Icc a b` in `ℝ` is a CW-complex.
* `instReal`: The real numbers are a CW-complex.
-/
noncomputable section

open Metric Set

namespace ClasCWComplex

variable {X : Type*} [t : TopologicalSpace X] [T2Space X]

/-! # CW-complex structures on finite sets -/

/-- The empty set is a CW-complex.-/
@[simps!]
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

/- **ToDo**: This should just follow from `instFiniteSet`. Delete? -/

/-- The CW-complex on the empty set is finite. -/
instance Finite_instEmpty : Finite (∅ : Set X) := Finite_mkFinite ..

/-- Every finite set is a CW-complex. -/
@[simps!]
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
      simp [PartialEquiv.single, ball, Matrix.empty_eq, eq_univ_iff_forall]
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

/-- The CW-complex on a finite set is finite. -/
instance Finite_instFiniteSet (C : Set X) [_root_.Finite C] : Finite C := Finite_mkFinite ..

/- This works now. 🎉-/
example (x : X) : ClasCWComplex {x} := inferInstance

/-! # CW-complex structure on the interval -/

/-- An auxiliary bijection sending the closed unit ball in `Fin 1 → ℝ` to a desired (non-degenerate)
  closed interval. -/
@[simps!]
def mapLT {a b : ℝ} (hab : a < b) := (IsometryEquiv.funUnique (Fin 1) ℝ).toHomeomorph.trans
    (affineHomeomorph ((b - a) / 2) ((a + b) / 2) (by linarith))

/-- `mapLT` sends the closed unit ball to the desired closed interval. -/
lemma mapLT_image_closedBall {a b : ℝ} (hab : a < b) : mapLT hab '' closedBall 0 1 = Icc a b := by
  change (((affineHomeomorph ((b - a) / 2) ((a + b) / 2) (by linarith))) ∘
    (IsometryEquiv.funUnique (Fin 1) ℝ)) '' closedBall 0 1 = Icc a b
  rw [image_comp, IsometryEquiv.image_closedBall,
    IsometryEquiv.funUnique_apply, Pi.zero_apply, Real.closedBall_eq_Icc, zero_sub, zero_add,
    affineHomeomorph_image_Icc _ _ _ _ (by linarith)]
  ring_nf

/-- `mapLT` sends the unit ball to the desired open interval. -/
lemma mapLT_image_ball {a b : ℝ} (hab : a < b) : mapLT hab '' ball 0 1 = Ioo a b := by
  change (((affineHomeomorph ((b - a) / 2) ((a + b) / 2) (by linarith))) ∘
    (IsometryEquiv.funUnique (Fin 1) ℝ)) '' ball 0 1 = Ioo a b
  rw [image_comp, IsometryEquiv.image_ball,
    IsometryEquiv.funUnique_apply, Pi.zero_apply, Real.ball_eq_Ioo, zero_sub, zero_add,
    affineHomeomorph_image_Ioo _ _ _ _ (by linarith)]
  ring_nf

/-- `mapLT` sends the unit sphere to the set of specified points. -/
lemma mapLT_image_sphere {a b : ℝ} (hab : a < b) : mapLT hab '' sphere 0 1 = {a, b} := by
  rw [← closedBall_diff_ball, image_diff (mapLT hab).injective, mapLT_image_closedBall,
    mapLT_image_ball]
  exact Icc_diff_Ioo_same (le_of_lt hab)

/-- `mapLT` as a partial bijection. -/
@[simps!]
def mapLTPartial {a b : ℝ} (hab : a < b) :=
  (mapLT hab).toPartialEquivOfImageEq (ball 0 1) (Ioo a b) (mapLT_image_ball hab)

-- this simp never actually gets used because of the automatically generated simps above
@[simp]
lemma mapLTPartial_image {a b : ℝ} (hab : a < b) {s : Set (Fin 1 → ℝ)} :
    mapLTPartial hab '' s = mapLT hab '' s :=
  rfl

/-- A helper definition for `instIccLT` where the set is presented differently. -/
@[simps!]
protected def instIccLT' {a b : ℝ} (hab : a < b) :
    ClasCWComplex (mapLTPartial hab '' closedBall 0 1 ∪ {a, b}) :=
  attachCellFiniteType {a, b}
    (mapLTPartial hab)
    (source_eq' := rfl)
    (continuousOn' := (mapLT hab).continuous.continuousOn)
    (continuousOn_symm' := (mapLT hab).symm.continuous.continuousOn)
    (disjoint' := by
      intro m i
      simp only [Equiv.toPartialEquivOfImageEq_apply, Homeomorph.coe_toEquiv,
        mapLTPartial_image, mapLT_image_ball]
      exact match m, i with
        | 0, ⟨i, hi⟩ => by
          simp only [openCell_zero_eq_singleton, instFiniteSet_map, PartialEquiv.single_apply,
            Function.const_apply, disjoint_singleton_right, mem_Ioo, not_and_or, not_lt]
          have : i = a ∨ i = b := by simp_all
          rcases this with hi | hi
          · exact .inl (le_of_eq hi)
          · exact .inr (le_of_eq hi.symm)
        | (_ + 1), i => i.elim)
    (mapsto' := by
      simp only [Nat.lt_one_iff, instFiniteSet_cell, iUnion_iUnion_eq_left,
        closedCell_zero_eq_singleton, instFiniteSet_map, PartialEquiv.single_apply,
        Function.const_apply, iUnion_coe_set, pair_comm, mem_insert_iff, mem_singleton_iff,
        iUnion_iUnion_eq_or_left, union_singleton, mapsTo', mapLTPartial_image, mapLT_image_sphere,
        Subset.rfl])

/-- A helper lemma for `Finite_IccLT.`-/
protected lemma Finite_instIccLT' {a b : ℝ} (hab : a < b) :
    letI := ClasCWComplex.instIccLT' hab
    Finite (mapLTPartial hab '' closedBall 0 1 ∪ {a, b}) :=
  Finite_attachCellFiniteType ..

/-- A (non-degenerate closed interval is a CW-complex.-/
@[simps!]
def instIccLT {a b : ℝ} (hab : a < b) : ClasCWComplex (Icc a b : Set ℝ) :=
  let _ := ClasCWComplex.instIccLT' hab
  ofEq (mapLTPartial hab '' closedBall 0 1 ∪ {a, b}) ∅
    (by
      rw [mapLTPartial_image, mapLT_image_closedBall, union_eq_left, pair_subset_iff, left_mem_Icc,
        right_mem_Icc, and_self]
      exact hab.le)
    rfl

/-- The Cw-complex structure on a (non-degenerate) closed interval is finite. -/
lemma Finite_instIccLT {a b : ℝ} (hab : a < b) :
    letI := instIccLT hab
    Finite (Icc a b) :=
  let _ := instIccLT hab
  let _ := ClasCWComplex.instIccLT' hab
  let _ := ClasCWComplex.Finite_instIccLT' hab
  finite_ofEq (mapLTPartial hab '' closedBall 0 1 ∪ {a, b}) ∅
    (by
      rw [mapLTPartial_image, mapLT_image_closedBall, union_eq_left, pair_subset_iff, left_mem_Icc,
        right_mem_Icc, and_self]
      exact hab.le)
    rfl

/- **ToDo** : Write simp lemmas about `instIcc`. -/

/-- The interval `Icc a b` in `ℝ` is a CW-complex.-/
instance instIcc {a b : ℝ} : ClasCWComplex (Icc a b : Set ℝ) :=
  if lt1 : a < b then instIccLT lt1
    else if lt2 : b < a then Icc_eq_empty_of_lt lt2 ▸ instEmpty
      else Linarith.eq_of_not_lt_of_not_gt _ _ lt1 lt2 ▸ Icc_self a ▸ instFiniteSet {a}

/-! # The CW-complex structure on the real numbers -/

/- **Commment**: This reuses the auxiliary definitions and lemmas of the interval. -/

/-- The real numbers are a CW-complex. -/
@[simps!]
instance instReal : ClasCWComplex (univ : Set ℝ) := mk (univ : Set ℝ)
  (cell := fun n ↦ match n with
    | 0 => ℤ
    | 1 => ℤ
    | (_ + 2) => PEmpty)
  (map := fun n i ↦ match n with
    | 0 => PartialEquiv.single ![] i
    | 1 => mapLTPartial (lt_add_one (i : ℝ))
    | (_ + 2) => i.elim)
  (source_eq := fun n i ↦ match n with
    | 0 => by simp [ball, Matrix.empty_eq, eq_univ_iff_forall]
    | 1 => rfl
    | (_ + 2) => i.elim)
  (continuousOn := fun n i ↦ match n with
    | 0 => continuousOn_const
    | 1 => (mapLT (lt_add_one (i : ℝ))).continuous.continuousOn
    | (_ + 2) => i.elim)
  (continuousOn_symm := fun n i ↦ match n with
    | 0 => continuousOn_const
    | 1 => (mapLT (lt_add_one (i : ℝ))).symm.continuous.continuousOn
    | (_ + 2) => i.elim)
  (pairwiseDisjoint' := by
    simp_rw [PairwiseDisjoint, Set.Pairwise, Function.onFun]
    exact fun ⟨n, j⟩ _ ⟨m, i⟩ _ ne ↦  match n with
      | 0 => match m with
        | 0 => by simp_all
        | 1 => by
          simp only [PartialEquiv.single_apply, Function.const_apply, nonempty_ball, zero_lt_one,
            Nonempty.image_const, mapLTPartial_image, mapLT_image_ball, disjoint_iff_inter_eq_empty,
            singleton_inter_eq_empty, mem_Ioo, Int.cast_lt, not_and, not_lt]
          norm_cast
          exact fun h ↦ h
        | (_ + 2) => i.elim
      | 1 => match m with
        | 0 => by
          simp only [mapLTPartial_image, mapLT_image_ball, PartialEquiv.single_apply,
            Function.const_apply, nonempty_ball, zero_lt_one, Nonempty.image_const,
            disjoint_iff_inter_eq_empty, inter_singleton_eq_empty, mem_Ioo, Int.cast_lt, not_and,
            not_lt]
          norm_cast
          exact fun h ↦ h
        | 1 => by
          simp only [mapLTPartial_image, mapLT_image_ball, disjoint_iff_inter_eq_empty ,
            Ioo_inter_Ioo, Ioo_eq_empty_iff, not_lt]
          norm_cast
          simp_all only [mem_univ, ne_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and, Nat.cast_one,
            le_sup_iff, inf_le_iff, add_le_iff_nonpos_right, or_comm, Int.reduceLE, false_or]
          exact Int.lt_or_gt_of_ne ne
        | (_ +  2) => i.elim
      | (_ + 2) => j.elim)
  (mapsto := fun n i ↦ match n with
    | 0 => by simp [Matrix.zero_empty, sphere_eq_empty_of_subsingleton]
    | 1 => by
      use fun n ↦  match n with
        | 0 => {i, i + 1}
        | (_ + 1) => ∅
      simp only [Nat.lt_one_iff, iUnion_iUnion_eq_left, Finset.mem_insert, Finset.mem_singleton,
        PartialEquiv.single_apply, Function.const_apply, Matrix.zero_empty, nonempty_closedBall,
        zero_le_one, Nonempty.image_const, iUnion_iUnion_eq_or_left, Int.cast_add, Int.cast_one,
        union_singleton, mapsTo', mapLTPartial_image, mapLT_image_sphere, pair_comm]
      exact Subset.rfl
    | (_ + 2) => i.elim)
  (closed' := by
    intro A _ hA
    apply SequentialSpace.isClosed_of_seq
    intro s a hs hsa
    have : a ∈ Ioo (⌊a⌋ - 1 : ℝ) (⌈a⌉ + 1) := by
      simp
      constructor
      · refine lt_of_lt_of_le ?_ (Int.floor_le a)
        norm_num
      · apply lt_of_le_of_lt (Int.le_ceil a)
        exact lt_add_one _
    obtain ⟨N, hN⟩ := tendsto_atTop_nhds.1 hsa (Ioo (⌊a⌋ - 1 : ℝ) (⌈a⌉ + 1)) this isOpen_Ioo
    let t n := s (n + N)
    have hta : Filter.Tendsto t Filter.atTop (nhds a) :=
      (Filter.tendsto_add_atTop_iff_nat N).mpr hsa
    have ht : ∀ (n : ℕ), t n ∈ A := by
      intro n
      exact hs (n + N)
    have htA : ∀ n, t n ∈ A ∩ Icc (⌊a⌋ - 1 : ℝ) (⌈a⌉ + 1) := by
      intro n
      refine ⟨ht n, ?_⟩
      apply Ioo_subset_Icc_self
      apply hN
      exact N.le_add_left n
    have hA : IsClosed (A ∩ Icc (⌊a⌋ - 1 : ℝ) (⌈a⌉ + 1)) := by
      rw [← Icc_union_Icc_eq_Icc (b := (⌊a⌋ : ℝ)) (by linarith)
        (by norm_cast; exact (Int.floor_le_ceil a).trans (by norm_num)),
        ← Icc_union_Icc_eq_Icc (a := (⌊a⌋ : ℝ)) (b := (⌈a⌉ : ℝ))
        (by norm_cast; exact Int.floor_le_ceil a) (by norm_num),
        inter_union_distrib_left, inter_union_distrib_left]
      refine IsClosed.union ?_ (IsClosed.union ?_ ?_)
      · convert hA 1 (⌊a⌋ - 1)
        simp only [Int.cast_sub, Int.cast_one, sub_add_cancel, mapLTPartial_image,
          mapLT_image_closedBall]
      · by_cases h : ∃ (z : ℤ), z = a
        · obtain ⟨z, hz⟩ := h
          subst a
          rw [Int.ceil_intCast, Int.floor_intCast, Icc_self]
          exact isClosed_inter_singleton
        convert hA 1 ⌊a⌋
        simp only [(Int.ceil_eq_floor_add_one_iff a).2 h, mapLTPartial_image,
          mapLT_image_closedBall]
        norm_cast
      · convert hA 1 ⌈a⌉
        simp only [mapLTPartial_image, mapLT_image_closedBall, add_sub_cancel_left, one_div,
          Fin.isValue]
    rw [← isSeqClosed_iff_isClosed] at hA
    exact (hA htA hta).1)
  (union' := by
    apply subset_antisymm (subset_univ _)
    intro x _
    simp only [mem_iUnion]
    use 1, ⌊x⌋
    simp only [mapLTPartial_image, mapLT_image_closedBall, mem_Icc]
    exact ⟨Int.floor_le x, (Int.le_ceil x).trans (by norm_cast; exact Int.ceil_le_floor_add_one x)⟩)

/- This works now. 🎉-/
example : ClasCWComplex (univ : Set (ℝ × ℝ)) := inferInstance

/-- The CW-structure on the reals is finite dimensional. -/
instance FiniteDimensional_instReal : FiniteDimensional (univ : Set ℝ) where
  eventually_isEmpty_cell := by
    rw [Filter.eventually_atTop]
    use 2
    intro n hn
    simp only [instReal_cell]
    split
    · contradiction
    · contradiction
    · infer_instance

end ClasCWComplex
