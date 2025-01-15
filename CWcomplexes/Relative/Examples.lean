import CWcomplexes.Relative.RelProduct
import Mathlib.Analysis.NormedSpace.HomeomorphBall
import Mathlib.Geometry.Manifold.Instances.Sphere


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

instance Finite_instEmpty : Finite (∅ : Set X) where
  eventually_isEmpty_cell := by
    rw [Filter.eventually_atTop]
    use 0
    exact fun b a ↦ PEmpty.instIsEmpty
  finite_cell := fun n ↦ Finite.of_fintype ((fun _ ↦ PEmpty) n)

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

instance Finite_instFiniteSet (C : Set X) [_root_.Finite C] : Finite C := Finite_mkFinite ..

example (x : X) : ClasCWComplex {x} := inferInstance

@[simps!]
def mapLT {a b : ℝ} (hab : a < b) := (IsometryEquiv.funUnique (Fin 1) ℝ).toHomeomorph.trans
    (affineHomeomorph ((b - a) / 2) ((a + b) / 2) (by linarith))

lemma mapLT_image_closedBall {a b : ℝ} (hab : a < b) : mapLT hab '' closedBall 0 1 = Icc a b := by
  change (((affineHomeomorph ((b - a) / 2) ((a + b) / 2) (by linarith))) ∘
    (IsometryEquiv.funUnique (Fin 1) ℝ)) '' closedBall 0 1 = Icc a b
  rw [image_comp, IsometryEquiv.image_closedBall,
    IsometryEquiv.funUnique_apply, Pi.zero_apply, Real.closedBall_eq_Icc, zero_sub, zero_add,
    affineHomeomorph_image_Icc _ _ _ _ (by linarith)]
  ring_nf

lemma mapLT_image_ball {a b : ℝ} (hab : a < b) : mapLT hab '' ball 0 1 = Ioo a b := by
  change (((affineHomeomorph ((b - a) / 2) ((a + b) / 2) (by linarith))) ∘
    (IsometryEquiv.funUnique (Fin 1) ℝ)) '' ball 0 1 = Ioo a b
  rw [image_comp, IsometryEquiv.image_ball,
    IsometryEquiv.funUnique_apply, Pi.zero_apply, Real.ball_eq_Ioo, zero_sub, zero_add,
    affineHomeomorph_image_Ioo _ _ _ _ (by linarith)]
  ring_nf

lemma mapLT_image_sphere {a b : ℝ} (hab : a < b) : mapLT hab '' sphere 0 1 = {a, b} := by
  rw [← closedBall_diff_ball, image_diff (mapLT hab).injective, mapLT_image_closedBall,
    mapLT_image_ball]
  exact Icc_diff_Ioo_same (le_of_lt hab)

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
  Finite_attachCellFiniteType {a, b} (mapLTPartial hab)
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

@[simps!]
def instIccLT {a b : ℝ} (hab : a < b) : ClasCWComplex (Icc a b : Set ℝ) :=
  let _ := ClasCWComplex.instIccLT' hab
  ofEq (mapLTPartial hab '' closedBall 0 1 ∪ {a, b}) ∅
    (by
      rw [mapLTPartial_image, mapLT_image_closedBall, union_eq_left, pair_subset_iff, left_mem_Icc,
        right_mem_Icc, and_self]
      exact hab.le)
    rfl

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

/-- The interval `Icc a b` in `ℝ` is a CW-complex.-/
instance instIcc {a b : ℝ} : ClasCWComplex (Icc a b : Set ℝ) :=
  if lt1 : a < b then instIccLT lt1
    else if lt2 : b < a then Icc_eq_empty_of_lt lt2 ▸ instEmpty
      else Linarith.eq_of_not_lt_of_not_gt _ _ lt1 lt2 ▸ Icc_self a ▸ instFiniteSet {a}

--write simp lemmas

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
          simp_all only [le_sup_iff, inf_le_iff, add_le_iff_nonpos_right, Int.reduceLE, false_or,
            or_false, ne_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and, or_comm]
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

-- I need some way to automatically recognize the normal `univ`
example : ClasCWComplex (univ : Set (ℝ × ℝ)) := inferInstance

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

instance instSphereZero (x ε : ℝ) (hε : ε ≥ 0) : ClasCWComplex (sphere x ε : Set ℝ) :=
  RelCWComplex.ofEq {x - ε, x + ε} ∅ (by
    ext y
    simp [abs_eq hε]
    rw[or_comm]
    congrm (?_ ∨ ?_)
    · rw [sub_eq_iff_eq_add, add_comm]
    · rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, sub_eq_iff_eq_add,
        zero_add])
    rfl

open Classical in
@[simps]
def PartialEquiv.ofSet {X : Type*} (s : Set X) (hs : s.Nonempty) : PartialEquiv s X :=
  letI := hs.coe_sort
  letI := Classical.inhabited_of_nonempty' (α := s)
  { toFun x := x
    invFun x := if hx : x ∈ s then ⟨x, hx⟩ else default
    source := univ
    target := s
    map_source' x _ := x.prop
    map_target' _ _ := mem_univ _
    left_inv' x _ := by simp
    right_inv' x hx := by simp [hx]}

open Classical in
@[simps]
def PartialHomeomorph.ofSet {X : Type*} [TopologicalSpace X] (s : Set X) (hs : s.Nonempty)
    (hs' : IsOpen s) : PartialHomeomorph s X :=
  letI := hs.coe_sort
  letI := Classical.inhabited_of_nonempty' (α := s)
  { toFun x := x
    invFun x := if hx : x ∈ s then ⟨x, hx⟩ else default
    source := univ
    target := s
    map_source' x _ := x.prop
    map_target' _ _ := mem_univ _
    left_inv' x _ := by simp
    right_inv' x hx := by simp [hx]
    open_source := isOpen_univ
    open_target := hs'
    continuousOn_toFun := continuous_subtype_val.continuousOn
    continuousOn_invFun := by
      simp [continuousOn_iff_continuous_restrict, continuous_inclusion Subset.rfl]}

open Metric in
@[simps!]
def sphereToDisc1 (n : ℕ) :=
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := {
    out := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1)}
  PartialHomeomorph.transHomeomorph
    (stereographic'
      (E := EuclideanSpace ℝ (Fin (n + 1))) n ⟨EuclideanSpace.single (Fin.last n) 1, by simp⟩)
    Homeomorph.unitBall

-- I don't think this is actually what I want
@[simps!]
def sphereToDisc2 (n : ℕ) :=
  PartialHomeomorph.trans' (sphereToDisc1 n)
  (PartialHomeomorph.ofSet (ball 0 1) (Metric.nonempty_ball.2 (Real.zero_lt_one)) isOpen_ball)
  (by simp)

-- need to restrict first PartialEquiv

open Classical in
@[simps]
def sphereToDisc (n : ℕ) :
    PartialEquiv (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin n)) where
  toFun x := if h : x ∈ sphere 0 1 then sphereToDisc1 n ⟨x, h⟩ else 0
  invFun y := if h : y ∈ ball 0 1 then (sphereToDisc1 n).symm ⟨y, h⟩
    else EuclideanSpace.single (Fin.last n) 1
  source := sphere 0 1 \ {EuclideanSpace.single (Fin.last n) 1}
  target := ball 0 1
  map_source' x := by
    intro ⟨hx1, hx2⟩
    simp only [mem_singleton_iff] at hx2
    simp only [hx1, ↓reduceDIte]
    exact Subtype.coe_prop ((sphereToDisc1 n) ⟨x, hx1⟩)
  map_target' y hy := by
    simp only [hy, ↓reduceDIte]
    have hy2 := (sphereToDisc1 n).map_target'
    simp only [sphereToDisc1_source, sphereToDisc1_target, PartialEquiv.invFun_as_coe] at hy2
    specialize hy2 (x := ⟨y, hy⟩) (mem_univ _)
    simp only [PartialHomeomorph.coe_coe_symm, mem_compl_iff, mem_singleton_iff] at hy2
    simp only [mem_diff, mem_singleton_iff]
    constructor
    · exact Subtype.coe_prop ((sphereToDisc1 n).symm ⟨y, of_eq_true (eq_true hy)⟩)
    · exact fun h ↦ hy2 (SetCoe.ext h)
  left_inv' x := by
    intro ⟨hx1, hx2⟩
    have h : ↑((sphereToDisc1 n) ⟨x, hx1⟩) ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      exact Subtype.coe_prop ((sphereToDisc1 n) ⟨x, hx1⟩)
    simp only [hx1, h, ↓reduceDIte, Subtype.eta]
    have : x = (⟨x, hx1⟩ : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := rfl
    nth_rw 4 [this]
    rw [SetCoe.ext_iff]
    apply PartialEquiv.left_inv
    rw [mem_singleton_iff] at hx2
    simp [hx2]
  right_inv' y hy := by
    have h :
        ↑((sphereToDisc1 n).symm ⟨y, hy⟩) ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
      exact Subtype.coe_prop ((sphereToDisc1 n).symm ⟨y, hy⟩)
    simp only [hy, h, ↓reduceDIte]
    have : y = (⟨y, hy⟩ : ball (0 : EuclideanSpace ℝ (Fin n)) 1) := rfl
    conv => rhs; rw [this]
    rw [SetCoe.ext_iff]
    apply PartialEquiv.right_inv
    simp

lemma sphereToDisc_symm_continuousOn (n : ℕ) :
    ContinuousOn (sphereToDisc n).symm (closedBall 0 1) := by
  simp only [← PartialEquiv.invFun_as_coe, sphereToDisc, ← ball_union_sphere, ContinuousOn]
  intro x hx
  rw [continuousWithinAt_union]
  constructor
  · rcases hx with hx | hx
    · refine ContinuousOn.continuousWithinAt ?_ hx
      rw [continuousOn_iff_continuous_restrict]
      apply Continuous.congr (f := Subtype.val ∘ (sphereToDisc1 n).symm)
      · apply continuous_subtype_val.comp
        have := (sphereToDisc1 n).continuousOn_invFun
        simp only [PartialEquiv.invFun_as_coe, PartialHomeomorph.coe_coe_symm,
          sphereToDisc1_target] at this
        exact continuous_iff_continuousOn_univ.mpr this
      · intro ⟨y, hy⟩
        simp only [Function.comp_apply, restrict_apply, hy, ↓reduceDIte]
    · have h : x ∉ ball 0 1 := by
        simp_all only [mem_sphere_iff_norm, sub_zero, mem_ball, dist_zero_right, lt_self_iff_false,
          not_false_eq_true]
      simp only [ContinuousWithinAt, hx, h, ↓reduceDIte]
      -- apply tendsto_nhdsWithin_congr (f := (sphereToDisc1 n).symm)
      sorry
  · rcases hx with hx | hx
    · sorry
    · refine ContinuousOn.continuousWithinAt ?_ hx
      rw [continuousOn_iff_continuous_restrict]
      sorry

-- this is wrong -_-
lemma sphereToDisc_continuousOn (n : ℕ) : ContinuousOn (sphereToDisc n) (closedBall 0 1) := by
  simp only [sphereToDisc, ← ball_union_sphere, ContinuousOn]
  intro x hx
  rw [continuousWithinAt_union]
  constructor
  · rcases hx with hx | hx
    · have h : x ∉ sphere 0 1 := by
        simp_all only [mem_ball, dist_zero_right, mem_sphere_iff_norm, sub_zero]
        exact ne_of_lt hx
      apply ContinuousWithinAt.congr (f := 0) (continuous_zero.continuousWithinAt)
      · intro y hy
        have h : y ∉ sphere 0 1 := by
          simp_all only [mem_ball, dist_zero_right, mem_sphere_iff_norm, sub_zero]
          exact ne_of_lt hy
        simp only [h, ↓reduceDIte, Pi.zero_apply]
      · simp only [h, ↓reduceDIte, Pi.zero_apply]
    · simp only [ContinuousWithinAt, hx, ↓reduceDIte]
      apply tendsto_nhdsWithin_congr (f := 0)
      · intro y hy
        have h : y ∉ sphere 0 1 := by
          simp_all only [mem_ball, dist_zero_right, mem_sphere_iff_norm, sub_zero]
          exact ne_of_lt hy
        simp only [h, ↓reduceDIte, Pi.zero_apply]
      ·
        sorry
  · rcases hx with hx | hx
    · apply ContinuousWithinAt.congr (f := sphereToDisc n)
      · sorry
      · sorry
      · sorry
    · sorry

#check ContinuousOn.union_continuousAt

end ClasCWComplex
