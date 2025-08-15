import Mathlib.Analysis.NormedSpace.HomeomorphBall
import Mathlib.Geometry.Manifold.Instances.Sphere
import CWcomplexes.Auxiliary
import CWcomplexes.RelConstructions

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

namespace Topology.CWComplex

variable {X : Type*} [t : TopologicalSpace X] [T2Space X]

/-! # CW-complex structure on the interval -/

/-- An auxiliary bijection sending the closed unit ball in `Fin 1 → ℝ` to a desired (non-degenerate)
  closed interval. -/
@[simps! -isSimp]
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
@[simps! -isSimp]
def mapLTPartial {a b : ℝ} (hab : a < b) :=
  (mapLT hab).toPartialEquivOfImageEq (ball 0 1) (Ioo a b) (mapLT_image_ball hab)

-- this simp never actually gets used because of the automatically generated simps above
@[simp]
lemma mapLTPartial_image {a b : ℝ} (hab : a < b) {s : Set (Fin 1 → ℝ)} :
    mapLTPartial hab '' s = mapLT hab '' s :=
  rfl

--set_option trace. in
--set_option trace.Meta.Tactic.simp.rewrite true in
/-- A helper definition for `instIccLT` where the set is presented differently. -/
protected def instIccLT' {a b : ℝ} (hab : a < b) :
    CWComplex (mapLTPartial hab '' closedBall 0 1 ∪ {a, b}) :=
  letI := CWComplex.ofFiniteSet (C := {a, b}) (toFinite {a, b})
  letI := CWComplex.finite_ofFiniteSet (C := {a, b}) (toFinite {a, b})
  attachCellFiniteType {a, b}
    (mapLTPartial hab)
    (source_eq' := rfl)
    (continuousOn' := (mapLT hab).continuous.continuousOn)
    (continuousOn_symm' := (mapLT hab).symm.continuous.continuousOn)
    (disjoint' := by
      intro m i
      simp only [mapLTPartial_image, mapLT_image_ball]
      exact match m, i with
        | 0, ⟨i, hi⟩ => by
          simp only [openCell_zero_eq_singleton, ofFiniteSet_map,
            PartialEquiv.single_apply, Function.const_apply, disjoint_singleton_right, mem_Ioo,
            not_and, not_lt]
          intro hai
          apply le_of_eq
          have : i = a ∨ i = b := by simp_all
          rcases this with hi | hi
          · subst i
            exact hai.false.elim
          · exact hi.symm
        | (_ + 1), i => i.elim)
    (mapsTo := by
      simp [closedCell_zero_eq_singleton, mapsTo', mapLT_image_sphere, subset_def, ofFiniteSet_map,
        ofFiniteSet_cell_zero])

/-- A helper lemma for `Finite_IccLT`. -/
protected lemma finite_instIccLT' {a b : ℝ} (hab : a < b) :
    letI := CWComplex.instIccLT' hab
    Finite (mapLTPartial hab '' closedBall 0 1 ∪ {a, b}) :=
  letI := CWComplex.ofFiniteSet (C := {a, b}) (toFinite {a, b})
  letI := CWComplex.finite_ofFiniteSet (C := {a, b}) (toFinite {a, b})
  finite_attachCellFiniteType ..

/-- A (non-degenerate) closed interval is a CW-complex. -/
def instIccLT {a b : ℝ} (hab : a < b) : CWComplex (Icc a b : Set ℝ) :=
  letI := CWComplex.instIccLT' hab
  ofEq (mapLTPartial hab '' closedBall 0 1 ∪ {a, b})
     (by
       rw [mapLTPartial_image, mapLT_image_closedBall, union_eq_left, pair_subset_iff,
         left_mem_Icc,
         right_mem_Icc, and_self]
       exact hab.le)

/-- The CW complex structure on a (non-degenerate) closed interval is finite. -/
lemma finite_instIccLT {a b : ℝ} (hab : a < b) :
    letI := instIccLT hab
    Finite (Icc a b) :=
  let _ := instIccLT hab
  let _ := CWComplex.instIccLT' hab
  let _ := CWComplex.finite_instIccLT' hab
  finite_ofEq (mapLTPartial hab '' closedBall 0 1 ∪ {a, b})
    (by
      rw [mapLTPartial_image, mapLT_image_closedBall, union_eq_left, pair_subset_iff, left_mem_Icc,
        right_mem_Icc, and_self]
      exact hab.le)

/- **ToDo** : Write simp lemmas about `instIcc`. -/

/-- The interval `Icc a b` in `ℝ` is a CW-complex. -/
instance instIcc {a b : ℝ} : CWComplex (Icc a b : Set ℝ) :=
  if lt1 : a < b then instIccLT lt1
    else if lt2 : b < a then Icc_eq_empty_of_lt lt2 ▸ ofFiniteSet finite_empty
      else le_antisymm (le_of_not_gt lt2) (le_of_not_gt lt1) ▸
        Icc_self a ▸ ofFiniteSet (toFinite {a})

/-! # The CW-complex structure on the real numbers -/

/- **Commment**: This reuses the auxiliary definitions and lemmas of the interval. -/

/-- The real numbers are a CW-complex. -/
@[simps (nameStem := "instReal")]
instance instReal : CWComplex (univ : Set ℝ) where
  cell n := match n with
    | 0 => ℤ
    | 1 => ℤ
    | (_ + 2) => PEmpty
  map n i := match n with
    | 0 => PartialEquiv.single ![] i
    | 1 => mapLTPartial (lt_add_one (i : ℝ))
    | (_ + 2) => i.elim
  source_eq n i := match n with
    | 0 => by simp [ball, Matrix.empty_eq, eq_univ_iff_forall]
    | 1 => rfl
    | (_ + 2) => i.elim
  continuousOn n i := match n with
    | 0 => continuousOn_const
    | 1 => (mapLT (lt_add_one (i : ℝ))).continuous.continuousOn
    | (_ + 2) => i.elim
  continuousOn_symm n i := match n with
    | 0 => continuousOn_const
    | 1 => (mapLT (lt_add_one (i : ℝ))).symm.continuous.continuousOn
    | (_ + 2) => i.elim
  pairwiseDisjoint' := by
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
      | (_ + 2) => j.elim
  mapsTo' n i := match n with
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
    | (_ + 2) => i.elim
  closed' := by
    intro A _ hA
    apply SequentialSpace.isClosed_of_seq
    intro s a hs hsa
    have : a ∈ Ioo (⌊a⌋ - 1 : ℝ) (⌈a⌉ + 1) := by
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
        simp only [(Int.ceil_eq_floor_add_one_iff_notMem a).2 h, mapLTPartial_image,
          mapLT_image_closedBall]
        norm_cast
      · convert hA 1 ⌈a⌉
        simp [mapLTPartial_image, mapLT_image_closedBall]
    rw [← isSeqClosed_iff_isClosed] at hA
    exact (hA htA hta).1
  union' := by
    apply subset_antisymm (subset_univ _)
    intro x _
    simp only [mem_iUnion]
    use 1, ⌊x⌋
    simp only [mapLTPartial_image, mapLT_image_closedBall, mem_Icc]
    exact ⟨Int.floor_le x, (Int.le_ceil x).trans (by norm_cast; exact Int.ceil_le_floor_add_one x)⟩

/-- The CW-structure on the reals is finite dimensional. -/
instance finiteDimensional_instReal : FiniteDimensional (univ : Set ℝ) where
  eventually_isEmpty_cell := by
    rw [Filter.eventually_atTop]
    use 2
    intro n hn
    simp only [cell_def, instReal_cell]
    split
    · contradiction
    · contradiction
    · infer_instance

/-! # Spheres in dimensions zero and one -/

/-- The sphere in dimension zero is a CW-complex. -/
def SphereZero (x : EuclideanSpace ℝ (Fin 0)) (ε : ℝ) (h : ε ≠ 0) : CWComplex (sphere x ε) :=
  letI := ofFiniteSet (X := EuclideanSpace ℝ (Fin 0)) finite_empty
  ofEq ∅ (E := (sphere x ε)) (sphere_eq_empty_of_subsingleton h).symm

lemma SphereZero_cell {x : EuclideanSpace ℝ (Fin 0)} {ε : ℝ} {h : ε ≠ 0} (n : ℕ) :
    letI := SphereZero x ε h
    IsEmpty (cell (sphere x ε) n) := by
  rw [SphereZero, cell_def, RelCWComplex.toCWComplex_cell, RelCWComplex.ofEq_cell]
  cases n <;> simp [ofFiniteSet_cell_zero, ofFiniteSet_cell_of_gt_zero, PEmpty.instIsEmpty]

/-- The CW-complex structure on the sphere in dimension zero  is finite. -/
lemma finite_SphereZero (x : EuclideanSpace ℝ (Fin 0)) (ε : ℝ) (h : ε ≠ 0) :
    letI := SphereZero x ε h
    Finite (sphere x ε) :=
  letI := ofFiniteSet (X := EuclideanSpace ℝ (Fin 0)) finite_empty
  letI := finite_ofFiniteSet (X := EuclideanSpace ℝ (Fin 0)) finite_empty
  finite_ofEq ∅ (E := (sphere x ε)) (sphere_eq_empty_of_subsingleton h).symm

/-- The CW-complex structure on the sphere in dimension 0 has no cells. This is an auxiliary lemma
  for `AuxSphereInduct`. -/
lemma isEmpty_cell_SphereZero (x : EuclideanSpace ℝ (Fin 0)) (ε : ℝ) (h : ε ≠ 0)  :
    letI := SphereZero x ε h
    ∀ m, IsEmpty (cell (sphere x ε) m) := by
  intro m
  simp only [RelCWComplex.ofEq_cell]
  cases m <;> (rw [RelCWComplex.mkFinite_cell]; infer_instance)

/-- The sphere in dimension 1 is a CW-complex. -/
def SphereOne (x ε : ℝ) (hε : ε ≥ 0) : CWComplex (sphere x ε) :=
  letI := ofFiniteSet (toFinite {x - ε, x + ε})
  (RelCWComplex.ofEq {x - ε, x + ε} ∅ (by
    ext y
    simp [abs_eq hε]
    rw[or_comm]
    congrm (?_ ∨ ?_)
    · rw [sub_eq_iff_eq_add, add_comm]
    · rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, sub_eq_iff_eq_add,
        zero_add])
    rfl).toCWComplex

lemma SphereOne_cell {x ε : ℝ} {hε : ε ≥ 0} {n : ℕ} :
    letI := SphereOne x ε hε
    cell (sphere x ε) n = (match n with
        | 0 => ({x - ε, x + ε} : Set ℝ)
        | (_ + 1) => PEmpty) := by
  rw [SphereOne, cell_def, RelCWComplex.toCWComplex_cell, RelCWComplex.ofEq_cell]
  rfl

lemma SphereOne_map {x ε : ℝ} {hε : ε ≥ 0}
    {i : ({x - ε, x + ε} : Set ℝ)} :
    letI := SphereOne x ε hε
    map (C := sphere x ε) 0 ↑i = PartialEquiv.single ![] i.1 := by
  simp_rw [map_def, SphereOne, RelCWComplex.toCWComplex, RelCWComplex.ofEq_map]
  rfl

/-- The CW-complex structure on the sphere in dimension 1 in finite. -/
lemma finite_SphereOne (x ε : ℝ) (hε : ε ≥ 0) :
    letI := SphereOne x ε hε
    Finite (sphere x ε) := by
  letI := ofFiniteSet (toFinite {x - ε, x + ε})
  letI := finite_ofFiniteSet (toFinite {x - ε, x + ε})
  rw [RelCWComplex.toCWComplex_eq]
  exact RelCWComplex.finite_ofEq ..

/-- The sphere as a CW-complex in `ℝ` with the euclidean metric. -/
@[simps! -isSimp]
def SphereOneEuclidean (ε : ℝ) (x : EuclideanSpace ℝ (Fin 1)) (hε : ε ≥ 0) :
    CWComplex (sphere x ε) :=
  letI := SphereOne (EuclideanUnique ℝ (Fin 1) x) ε hε
  ofHomeomorph (sphere (EuclideanUnique ℝ (Fin 1) x) ε : Set ℝ) (sphere x ε)
  (EuclideanUnique ℝ (Fin 1)).symm.toHomeomorph (by simp)

/-- The CW-complex structure on the sphere in `ℝ` with he euclidean metric is finite. -/
lemma finite_SphereOneEuclidean (ε : ℝ) (x : EuclideanSpace ℝ (Fin 1)) (hε : ε ≥ 0) :
    letI := SphereOneEuclidean ε x hε
    Finite (sphere x ε) :=
  let _ := SphereOne (EuclideanUnique ℝ (Fin 1) x) ε hε
  let _ := finite_SphereOne (EuclideanUnique ℝ (Fin 1) x) ε hε
  finite_ofHomeomorph ..

/-! # Construction with two cells overall. -/

/-**Comment**:
  We first define (the inverse of) the typical map that wraps the closed ball of dimension `n`
  around the sphere in dimension `n + 1`. There are a few different ways to define this map.
  Here we obt to compose the homeomorphism `ball 0 1 ≃ₜ EuclideanSpace ℝ (Fin n)`
  (more concretely the inverse of `Homeomorph.unitBall`) with the inverse of the
  stereographic projection (`stereographic'`). As these maps are obviously not defined on the
  'edges' of their domains we manually send the sphere to the north pole.
  We get the continuity on the open ball basically for free. The continuity on the whole closed
  ball will need to be shown.

  A similar map could be defined considerably easier using spherical coordinates. Unfortunatly
  spherical coordinates do not seem to be in mathlib yet. This should be redone once they are. -/

open Metric in
/-- A partial homeomorphism sending the sphere in dimension `n + 1` without the north pole to the
  open ball in dimension `n`. This is an auxiliary construction for `sphereToDisc`. -/
@[simps! -isSimp]
def sphereToDisc' (n : ℕ) :=
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := {
    out := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1)}
  PartialHomeomorph.transHomeomorph
    (stereographic'
      (E := EuclideanSpace ℝ (Fin (n + 1))) n ⟨EuclideanSpace.single (Fin.last n) 1, by simp⟩)
    Homeomorph.unitBall

open Classical in
/-- A partial bijection sending the sphere in dimension `n + 1` to the closed ball in dimension
  `n`. -/
@[simps -isSimp]
def sphereToDisc (n : ℕ) :
    PartialEquiv (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin n)) where
  toFun x := if h : x ∈ sphere 0 1 then sphereToDisc' n ⟨x, h⟩ else 0
  invFun y := if h : y ∈ ball 0 1 then (sphereToDisc' n).symm ⟨y, h⟩
    else EuclideanSpace.single (Fin.last n) 1
  source := sphere 0 1 \ {EuclideanSpace.single (Fin.last n) 1}
  target := ball 0 1
  map_source' x := by
    intro ⟨hx1, hx2⟩
    simp only [mem_singleton_iff] at hx2
    simp only [hx1, ↓reduceDIte]
    exact Subtype.coe_prop ((sphereToDisc' n) ⟨x, hx1⟩)
  map_target' y hy := by
    simp only [hy, ↓reduceDIte]
    have hy2 := (sphereToDisc' n).map_target'
    simp only [sphereToDisc'_source, sphereToDisc'_target, PartialEquiv.invFun_as_coe] at hy2
    specialize hy2 (x := ⟨y, hy⟩) (mem_univ _)
    simp only [PartialHomeomorph.coe_coe_symm, mem_compl_iff, mem_singleton_iff] at hy2
    simp only [mem_diff, mem_singleton_iff]
    constructor
    · exact Subtype.coe_prop ((sphereToDisc' n).symm ⟨y, of_eq_true (eq_true hy)⟩)
    · exact fun h ↦ hy2 (SetCoe.ext h)
  left_inv' x := by
    intro ⟨hx1, hx2⟩
    have h : ↑((sphereToDisc' n) ⟨x, hx1⟩) ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      exact Subtype.coe_prop ((sphereToDisc' n) ⟨x, hx1⟩)
    simp only [hx1, h, ↓reduceDIte, Subtype.eta]
    have : x = (⟨x, hx1⟩ : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := rfl
    nth_rw 4 [this]
    rw [SetCoe.ext_iff]
    apply PartialEquiv.left_inv
    rw [mem_singleton_iff] at hx2
    simp [hx2, sphereToDisc'_source]
  right_inv' y hy := by
    have h :
        ↑((sphereToDisc' n).symm ⟨y, hy⟩) ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
      exact Subtype.coe_prop ((sphereToDisc' n).symm ⟨y, hy⟩)
    simp only [hy, h, ↓reduceDIte]
    have : y = (⟨y, hy⟩ : ball (0 : EuclideanSpace ℝ (Fin n)) 1) := rfl
    conv => rhs; rw [this]
    rw [SetCoe.ext_iff]
    apply PartialEquiv.right_inv
    simp [sphereToDisc'_target]

/-- The image of the open ball under the inverse of `sphereToDisc` is the sphere without
  the north pole. -/
lemma sphereToDisc_symm_image_ball (n : ℕ) :
    (sphereToDisc n).symm '' ball 0 1 = sphere 0 1 \ {EuclideanSpace.single (Fin.last n) 1} := by
  simp only [← sphereToDisc_target, PartialEquiv.symm_image_target_eq_source, sphereToDisc_source]

/-- The image of the closed ball under the inverse of `sphereToDisc` is the sphere. -/
lemma sphereToDisc_symm_image_closedBall (n : ℕ) (h : n > 0) :
    (sphereToDisc n).symm '' closedBall 0 1 = sphere 0 1 := by
  rw [← ball_union_sphere, image_union, sphereToDisc_symm_image_ball]
  suffices ↑(sphereToDisc n).symm '' sphere 0 1 = {EuclideanSpace.single (Fin.last n) 1} by
    rw [this, diff_union_self, union_eq_left]
    simp
  apply subset_antisymm
  · simp_rw [subset_singleton_iff, mem_image, sphereToDisc_symm_apply]
    intro y ⟨x, hx, hxy⟩
    simp_all
  · simp only [singleton_subset_iff, mem_image, sphereToDisc_symm_apply]
    use EuclideanSpace.single ⟨0, h⟩ 1
    simp

/-- `sphereToDisc` is the same as `sphereToDisc'` on the ball. -/
lemma sphereToDisc_comp_val {n : ℕ} :
    (sphereToDisc n).symm ∘ (Subtype.val (p := fun x ↦ x ∈ ball 0 1)) =
    Subtype.val ∘ (sphereToDisc' n).symm := by
  ext
  simp [sphereToDisc_symm_apply]

/- **Comment**:
  We can now show that `sphereToDisc` is continuous also on the whole closed ball.
  A substential part of the work is hidden in the auxiliary lemmas
  `Homeomorph.tendsto_norm_comp_unitBall_symm` and `stereographic'_symm_tendsto`. -/

/-- As you approach the sphere in dimension `n` from inside the ball, the inverse of
  `sphereToDisc` approaches the north pole of the sphere in dimension `n + 1`. -/
lemma tendsto_sphereToDisc_symm {n : ℕ} (hn : n > 0) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Filter.Tendsto (sphereToDisc n).symm (nhdsWithin x (ball 0 1))
    (nhds (EuclideanSpace.single (Fin.last n) 1)) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) := {
    exists_pair_ne := by
      use 0, (EuclideanSpace.single (⟨0, Nat.zero_lt_of_lt hn⟩ : Fin n) 1)
      intro h
      replace h := congrFun h ⟨0, Nat.zero_lt_of_lt hn⟩
      simp_all}
  suffices Filter.Tendsto (↑(sphereToDisc n).symm ∘  Subtype.val)
      (Filter.comap (α := ball 0 1) Subtype.val (nhdsWithin x (ball 0 1)))
      (nhds (EuclideanSpace.single (Fin.last n) 1)) by
    rw [Filter.tendsto_comap'_iff] at this
    · exact this
    · rw [Subtype.range_val_subtype]
      exact Filter.mem_inf_of_right (Subset.refl _)
  rw [sphereToDisc_comp_val]
  have : range (Subtype.val (p := fun x ↦ x ∈ ball (0 : (EuclideanSpace ℝ (Fin n))) 1))
      = ball 0 1 := by
    rw [Subtype.range_coe_subtype]
    rfl
  nth_rw 9 [← this]
  rw [comap_nhdsWithin_range]
  simp only [sphereToDisc', PartialHomeomorph.transHomeomorph_symm_apply]
  rw [← Filter.tendsto_comap_iff]
  have : EuclideanSpace.single (Fin.last n) 1 = Subtype.val
      (⟨(EuclideanSpace.single (Fin.last n) 1), by simp⟩ :
      sphere (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1) := rfl
  nth_rw 2 [this]
  rw [← nhds_induced, ← Filter.tendsto_map'_iff]
  apply stereographic'_symm_tendsto
  rw [Filter.tendsto_map'_iff]
  exact Homeomorph.tendsto_norm_comp_unitBall_symm x hx

/-- The inverse of `sphereToDisc` is continuous on the closed ball. -/
lemma sphereToDisc_symm_continuousOn {n : ℕ} (hn : n > 0) :
    ContinuousOn (sphereToDisc n).symm (closedBall 0 1) := by
  simp only [← PartialEquiv.invFun_as_coe, ← ball_union_sphere, ContinuousOn]
  intro x hx
  rw [continuousWithinAt_union]
  constructor
  · rcases hx with hx | hx
    · refine ContinuousOn.continuousWithinAt ?_ hx
      rw [continuousOn_iff_continuous_restrict]
      apply Continuous.congr (f := Subtype.val ∘ (sphereToDisc' n).symm)
      · apply continuous_subtype_val.comp
        have := (sphereToDisc' n).continuousOn_invFun
        simp only [PartialEquiv.invFun_as_coe, PartialHomeomorph.coe_coe_symm,
          sphereToDisc'_target] at this
        exact continuousOn_univ.mp this
      · simp only [sphereToDisc]
        intro ⟨y, hy⟩
        simp only [Function.comp_apply, restrict_apply, hy, ↓reduceDIte]
    · have h : x ∉ ball 0 1 := by
        simp_all only [mem_sphere_iff_norm, sub_zero, mem_ball, dist_zero_right, lt_self_iff_false,
          not_false_eq_true]
      simp only [ContinuousWithinAt]
      have : (sphereToDisc n).invFun x = (EuclideanSpace.single (Fin.last n) 1) := by
        simp only [sphereToDisc, h, ↓reduceDIte]
      rw [this, PartialEquiv.invFun_as_coe]
      exact tendsto_sphereToDisc_symm hn x hx
  · rcases hx with hx | hx
    · apply continuousWithinAt_of_notMem_closure
      rw [closure_sphere]
      intro h
      simp_all
    · refine ContinuousOn.continuousWithinAt ?_ hx
      rw [continuousOn_iff_continuous_restrict]
      have : (sphere 0 1).restrict (sphereToDisc n).invFun =
          fun y ↦ EuclideanSpace.single (Fin.last n) 1 := by
        ext y
        simp [sphereToDisc_symm_apply]
      rw [this]
      exact continuous_const

/-- `sphereToDisc` is continuous on the sphere without the north pole. -/
lemma sphereToDisc_continuousOn (n : ℕ) : ContinuousOn (sphereToDisc n)
    (sphere 0 1 \ {EuclideanSpace.single (Fin.last n) 1}) := by
  simp only [sphereToDisc]
  unfold ContinuousOn
  intro x ⟨hx1, hx2⟩
  rw [continuousWithinAt_diff_singleton]
  rw [continuousWithinAt_iff_continuousAt_restrict _ hx1]
  apply ContinuousAt.congr (f := Subtype.val ∘ sphereToDisc' n)
  · apply continuous_subtype_val.continuousAt.comp
    apply ContinuousOn.continuousAt (s := {⟨EuclideanSpace.single (Fin.last n) 1, by simp⟩}ᶜ)
    · exact sphereToDisc'_source n ▸ (sphereToDisc' n).continuousOn
    simp_all
  · apply Eq.eventuallyEq
    ext
    simp

/- **Comment** :
  We can now move on to defining the actual characteristic map. We need to precompose with
  `toEuclideanNormScale` since we need to map out of `Fin n → ℝ` which has the
  `∞`-metric instead of the euclidean metric we have been using.
  We can then show that the sphere in dimension `≥1` is a CW-complex. -/

/-- This is an auxiliary definition for the characteristic map of the sphere. -/
@[simps!]
def spheremap (n : ℕ) : PartialEquiv (Fin n → ℝ) (EuclideanSpace ℝ (Fin (n + 1))) :=
  (toEuclideanNormScale n).transPartialEquiv (sphereToDisc n).symm

/-- The sphere in dimension at least 1 is a CW-complex. This is an auxiliary version of
  `instSphereGT` where the set is presented in a nicer way. -/
@[simps! -isSimp]
def instSphereGT' (n : ℕ) (h : n > 0) :
    CWComplex ((spheremap n) '' closedBall 0 1 ∪ {EuclideanSpace.single (Fin.last n) 1}) :=
  letI := ofFiniteSet
    (toFinite {(EuclideanSpace.single (Fin.last n) 1 : EuclideanSpace ℝ (Fin (n + 1)))})
  letI := finite_ofFiniteSet
    (toFinite {(EuclideanSpace.single (Fin.last n) 1 : EuclideanSpace ℝ (Fin (n + 1)))})
  attachCellFiniteType {EuclideanSpace.single (Fin.last n) 1}
  (spheremap n)
  (source_eq' := by
    ext x
    simp [sphereToDisc_target])
  (continuousOn' := by
    simp only [spheremap, Equiv.transPartialEquiv, PartialEquiv.coe_trans,
      Equiv.toPartialEquiv_apply, Homeomorph.coe_toEquiv, PartialEquiv.coe_trans_symm,
      Equiv.toPartialEquiv_symm_apply, Homeomorph.coe_symm_toEquiv, PartialEquiv.symm_symm,
      PartialEquiv.symm_source, sphereToDisc_target, PartialEquiv.symm_target, sphereToDisc_source,
      PartialEquiv.copy_apply]
    apply (sphereToDisc_symm_continuousOn h).comp (toEuclideanNormScale n).continuous.continuousOn
    rw [mapsTo', toEuclideanNormScale_image_closedBall])
  (continuousOn_symm' := by
    simp [spheremap, Equiv.transPartialEquiv, sphereToDisc_continuousOn, sphereToDisc_source])
  (disjoint' := by
    intro m i
    exact match m, i with
      | 0, ⟨i, hi⟩ => by
        simp only [spheremap, Equiv.transPartialEquiv_apply, Homeomorph.coe_toEquiv, ← image_image,
          toEuclideanNormScale_image_ball, sphereToDisc_symm_image_ball, openCell_zero_eq_singleton,
          ofFiniteSet_map, PartialEquiv.single_apply, Function.const_apply,
          disjoint_singleton_right]
        exact notMem_diff_of_mem hi
      | (_ + 1), i => i.elim)
  (mapsTo := by
    rw [mapsTo']
    apply subset_iUnion_of_subset 0
    apply subset_iUnion_of_subset h
    simp only [ofFiniteSet_cell_zero, closedCell_zero_eq_singleton]
    apply subset_iUnion_of_subset ⟨EuclideanSpace.single (Fin.last n) 1, rfl⟩
    simp only [spheremap, Equiv.transPartialEquiv_apply, ← image_image, Homeomorph.coe_toEquiv,
      toEuclideanNormScale_image_sphere, subset_singleton_iff]
    intro y hy
    simp only [ofFiniteSet_map, PartialEquiv.single_apply,
      Function.const_apply]
    simp only [mem_image, sphereToDisc_symm_apply] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    simp_all)

/-- The CW-complex structure on the sphere is finite. An auxiliary version of `Finite_instSphereGT`
  where the set is presented in a nicer way. -/
lemma finite_instSphereGT' (n : ℕ) (h : n > 0) :
    letI := instSphereGT' n h
    Finite ((spheremap n) '' closedBall 0 1 ∪ {EuclideanSpace.single (Fin.last n) 1}) :=
  letI := ofFiniteSet
    (toFinite {(EuclideanSpace.single (Fin.last n) 1 : EuclideanSpace ℝ (Fin (n + 1)))})
  letI := finite_ofFiniteSet
    (toFinite {(EuclideanSpace.single (Fin.last n) 1 : EuclideanSpace ℝ (Fin (n + 1)))})
  finite_attachCellFiniteType ..

/-- The sphere in dimension at least 1 is a CW-complex. -/
@[simps! -isSimp]
def instSphereGT (n : ℕ) (h : n > 0) :
    CWComplex (sphere 0 1 : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
  letI := instSphereGT' n h
  ofEq (E := sphere 0 1)
    ((spheremap n) '' closedBall 0 1 ∪ {EuclideanSpace.single (Fin.last n) 1})
    (by
      simp only [spheremap, Equiv.transPartialEquiv_apply, Homeomorph.coe_toEquiv, ← image_image,
        toEuclideanNormScale_image_closedBall, sphereToDisc_symm_image_closedBall n h,
        union_eq_left, singleton_subset_iff, mem_sphere_iff_norm, sub_zero,
        EuclideanSpace.norm_single, norm_one])

/-- The CW-complex structure on the sphere in dimension at least 1 is finite. -/
lemma finite_instSphereGT (n : ℕ) (h : n > 0) :
    letI := instSphereGT n h
    Finite (sphere 0 1 : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
  let _ := instSphereGT' n h
  let _ := finite_instSphereGT' n h
  finite_ofEq ((spheremap n) '' closedBall 0 1 ∪ {EuclideanSpace.single (Fin.last n) 1})
    (by simp [← image_image, sphereToDisc_symm_image_closedBall n h])


/- **Comment**: We can now compile what we have proven so far into nice instances.-/

/-- The unit sphere is a CW-complex. This construction uses two cells in total. For an
  alternative construction see `SphereInduct`. -/
instance instSphere {n : ℕ} : CWComplex (sphere 0 1 : Set (EuclideanSpace ℝ (Fin n))) :=
  match n with
  | 0 => SphereZero 0 1 one_ne_zero
  | 1 => SphereOneEuclidean 1 0 zero_le_one
  | (n + 2) => instSphereGT (n + 1) n.zero_lt_succ

/-- The CW-complex structure on the sphere is finite. -/
instance Finite_instSphere {n : ℕ} : Finite (sphere 0 1 : Set (EuclideanSpace ℝ (Fin n))) :=
  match n with
  | 0 => finite_SphereZero 0 1 one_ne_zero
  | 1 => finite_SphereOneEuclidean 1 0 zero_le_one
  | (n + 2) => finite_instSphereGT (n + 1) n.zero_lt_succ

/- **ToDo** :
  Generalize this to other centre points, radii and metrics. This should be fairly easy using
  `normScale` and some generalization of `affineHomeomorph` (that possibly needs to be defined). -/

/- This works now. 🎉-/
example : CWComplex (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := inferInstance

/- **Comment** : We now even get the CW-structure on the torus for free. -/

/-
example : CWComplex
    (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  inferInstance
-/

/-! # Construction with two cells in every dimension. -/

/-**Comment**:
  We now move onto the second popular construction for the sphere:
  We construct the spheres inductively adding two cells in each dimension.
  While the actual construction is way more difficult, the characteristic maps are a lot
  simpler. -/

/-- A partial bijection sending the open ball in dimension `n` to the upper hemisphere
  (without the equator) of the sphere in dimension `n + 1`. -/
@[simps -isSimp]
def discToSphereUp (n : ℕ) :
    PartialEquiv (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin (n + 1))) where
  toFun := fun x ↦ Fin.snoc x (√(1 - ‖x‖ ^ 2))
  invFun := Fin.init
  source := ball 0 1
  target := sphere 0 1 ∩ {x | x (Fin.last n) > 0}
  map_source' x hx := by
    constructor
    · simp only [mem_ball, dist_zero_right] at hx
      rw [mem_sphere_iff_norm, sub_zero, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow,
        EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)),
        Fin.sum_univ_castSucc]
      simp only [Fin.snoc, Fin.coe_castSucc, Fin.is_lt, ↓reduceDIte, Fin.castLT_castSucc, cast_eq,
        Real.norm_eq_abs, sq_abs, Fin.val_last, lt_self_iff_false]
      rw [Real.sq_sqrt (by simp_all [hx.le]),
        ← Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))]
      simp_rw [← sq_abs (x _), ← Real.norm_eq_abs, ← EuclideanSpace.norm_eq, add_sub_cancel]
    · simp_all
  map_target' y:= by
    intro ⟨hy1, hy2⟩
    simp_all only [mem_sphere_iff_norm, sub_zero, gt_iff_lt, mem_setOf_eq, mem_ball,
      dist_zero_right]
    rw [← hy1]
    apply EuclideanSpace.norm_finInit_lt
    simp_all only [Real.norm_eq_abs, gt_iff_lt, abs_pos]
    exact hy2.ne.symm
  left_inv' x hx := by simp
  right_inv' y := by
    intro ⟨hy1, hy2⟩
    simp_all
    suffices √(1 - norm (Fin.init y) (self := (PiLp.instNorm 2 fun x ↦ ℝ)) ^ 2) = y (Fin.last n) by
      rw [this, Fin.snoc_init_self]
    have : norm (Fin.init y) (self := (PiLp.instNorm 2 fun x ↦ ℝ)) ≤ 1 := by
      rw [← hy1]
      exact EuclideanSpace.norm_finInit_le y
    rw [← sq_eq_sq₀ (Real.sqrt_nonneg _) hy2.le, Real.sq_sqrt (by simp_all), EuclideanSpace.norm_eq,
      ← one_pow (n := 2), ← hy1, EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)),
      Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)), sub_eq_iff_eq_add,
      Fin.sum_univ_castSucc, add_comm, Real.norm_eq_abs, sq_abs]
    rfl

/-- `discToSphereUp` is continuous. -/
lemma continuous_discToSphereUp (n : ℕ) : Continuous (discToSphereUp n) := by
  simp only [discToSphereUp]
  apply Continuous.finSnoc
  · exact continuous_id'
  · continuity

/-- The inverse of `discToSphereUp` is continuous. -/
lemma continuous_discToSphereUp_symm (n : ℕ) : Continuous (discToSphereUp n).symm :=
  continuous_id.finInit

/-- The image of the sphere in dimension `n` under `discToSphereUp` is the 'equator' of the
  sphere in dimension `n + 1`, i.e. the sphere intersected with the hyperplane where the last
  coordinate is zero. -/
@[simp]
lemma discToSphereUp_image_sphere (n : ℕ) :
    (discToSphereUp n) '' sphere 0 1 = (sphere 0 1) ∩ {x | x (Fin.last n) = 0} := by
  ext x
  simp only [mem_image, mem_sphere_iff_norm, sub_zero, mem_inter_iff, mem_setOf_eq]
  constructor
  · intro ⟨y, hy1, hy2⟩
    rw [← hy2]
    simp only [discToSphereUp, gt_iff_lt, hy1, one_pow, sub_self, Real.sqrt_zero, Fin.snoc_last,
      and_true]
    simp only [EuclideanSpace.norm_eq, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      Real.norm_eq_abs (r := 0), sq_abs, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero]
    rw [← EuclideanSpace.norm_eq, hy1]
  · intro ⟨h1, h2⟩
    use Fin.init x
    simp only [EuclideanSpace.norm_eq, Fin.sum_univ_castSucc, h2, Real.norm_eq_abs (r := 0),
      sq_abs, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h1
    simp only [EuclideanSpace.norm_eq, Fin.init, h1, discToSphereUp,
      one_pow, sub_self, Real.sqrt_zero, true_and]
    simp only [← h2, Fin.snoc_init_self]

/-- The image of the closed ball in dimension `n` under `discToSphereUp` is the
  upper hemisphere of the sphere in dimenion `n + 1`. -/
@[simp]
lemma discToSphereUp_image_closedBall (n : ℕ) :
    (discToSphereUp n) '' closedBall 0 1 = (sphere 0 1) ∩ {x | x (Fin.last n) ≥ 0} := by
  simp only [ge_iff_le]
  ext x
  simp only [mem_image, mem_sphere_iff_norm, sub_zero, mem_inter_iff, mem_setOf_eq]
  constructor
  · intro ⟨y, hy1, hy2⟩
    simp only [mem_closedBall, dist_zero_right] at hy1
    constructor
    · simp only [← hy2, discToSphereUp, gt_iff_lt]
      nth_rw 1 [EuclideanSpace.norm_eq]
      simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
        (1 - ‖y‖ ^ 2).sq_sqrt (by simp_all), Real.sqrt_eq_one]
      simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs,
        (∑ x : Fin n, y x ^ 2).sq_sqrt (Finset.sum_nonneg' (fun i ↦ sq_nonneg (y i))),
        add_sub_cancel]
    · simp [← hy2, discToSphereUp_apply]
  · intro ⟨h1, h2⟩
    use Fin.init x
    simp only [EuclideanSpace.norm_eq, Fin.sum_univ_castSucc, Real.sqrt_eq_one] at h1
    symm at h1
    rw [← sub_eq_iff_eq_add', ← Real.sq_sqrt (Finset.sum_nonneg' (fun i ↦ sq_nonneg _)),
      ← EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] at h1
    change 1 - (norm (E := EuclideanSpace ℝ (Fin n)) (Fin.init x)) ^ 2 = x (Fin.last n) ^ 2 at h1
    constructor
    · rw [sub_eq_iff_eq_add', ← sub_eq_iff_eq_add] at h1
      rw [mem_closedBall, dist_zero_right, ← sq_le_sq₀ (norm_nonneg _) zero_le_one, one_pow, ← h1]
      simp [h2]
    · simp [discToSphereUp, gt_iff_lt, h1, Real.sqrt_sq h2]

/-**Comment**:
  In order to not define essentially the same map again but for the lower hemisphere, we
  postcompose `discToSphere` with a linear bijective isometry that flips the last coordinate. -/

/-- A partial bijection sending the open ball in dimension `n` to the lower hemisphere
  (without the equator) of the sphere in dimension `n + 1`. -/
@[simps!]
def discToSphereDown (n : ℕ) :=
  (discToSphereUp n).transEquiv (LinearIsometryEquiv.negLast n).toEquiv

/-- `discToSphereDown` is continuous. -/
lemma continuous_discToSphereDown (n : ℕ) : Continuous (discToSphereDown n) := by
  simp [discToSphereDown, PartialEquiv.transEquiv, continuous_discToSphereUp]

/- The inverse of `discToSphereDown` is continuous. -/
lemma continuous_discToSphereDown_symm (n : ℕ) : Continuous (discToSphereDown n).symm := by
  simp [discToSphereDown, PartialEquiv.transEquiv]
  exact (continuous_discToSphereUp_symm n).comp (LinearIsometryEquiv.negLast n).symm.continuous

/- **Comment** :
  We can now move on to defining the actual characteristic maps. We need to precompose with
  `toEuclideanNormScale` since we need to map out of `Fin n → ℝ` which has the
  `∞`-metric instead of the euclidean metric we have been using. -/

/-- This is an auxiliary definition for the upper characteristic map of the sphere. -/
@[simps!]
def spheremapup (n : ℕ) := (toEuclideanNormScale n).transPartialEquiv (discToSphereUp n)

/-- The image of the closed ball in dimension `n` under `spheremapup` is the upper hemisphere of
  the sphere in dimension `n + 1`. -/
lemma spheremapup_image_closedBall (n : ℕ) :
    spheremapup n '' closedBall 0 1 = sphere 0 1 ∩ {x | x (Fin.last n) ≥ 0} := by
  simp [← image_image]

/-- This is an auxiliary definition for the lower characteristic map of the sphere. -/
@[simps!]
def spheremapdown (n : ℕ) := (toEuclideanNormScale n).transPartialEquiv (discToSphereDown n)

/-- The image of the closed ball in dimension `n` under `spheremapup` is the lower hemisphere of
  the sphere in dimension `n + 1`. -/
lemma spheremapdown_image_closedBall (n : ℕ) :
    spheremapdown n '' closedBall 0 1 = sphere 0 1 ∩ {x | x (Fin.last n) ≤ 0} := by
  simp only [spheremapdown_apply, ← image_image, toEuclideanNormScale_image_closedBall,
    discToSphereUp_image_closedBall, ge_iff_le,
    image_inter (LinearIsometryEquiv.negLast n).injective, LinearIsometryEquiv.image_sphere,
    map_zero]
  congr
  · ext x
    simp [mem_image, mem_setOf_eq]
    constructor
    · intro ⟨y, hy1, hy2⟩
      rw [← hy2]
      unfold LinearIsometryEquiv.negLast Function.update
      simp [hy1]
    · intro hx
      use (LinearIsometryEquiv.negLast n) x
      simp only [LinearIsometryEquiv.negLast_idempotent, and_true]
      unfold LinearIsometryEquiv.negLast Function.update
      simp [hx]

/-- We bundle the characterstic maps `spheremapup` and `spheremapdown` to make the statements of
  later definitions easier. -/
def spheremaps (n : ℕ) (i : Fin 2) : PartialEquiv (Fin n → ℝ) (EuclideanSpace ℝ (Fin (n + 1))) :=
  match i with
  | 0 => spheremapup n
  | 1 => spheremapdown n

/-- The source of both characteristic maps is the open ball. -/
lemma spheremaps_source (n : ℕ) (i : Fin 2) : (spheremaps n i).source = ball 0 1 :=
  match i with
  | 0 => by
    simp only [spheremaps, spheremapup_source, ← Homeomorph.coe_toEquiv,
      Equiv.preimage_eq_iff_eq_image, discToSphereUp_source]
    simp only [Homeomorph.coe_toEquiv, toEuclideanNormScale_image_ball]
  | 1 => by
    simp only [spheremaps, spheremapdown_source, ← Homeomorph.coe_toEquiv,
      Equiv.preimage_eq_iff_eq_image, discToSphereUp_source]
    simp only [Homeomorph.coe_toEquiv, toEuclideanNormScale_image_ball]

/-- The image of the sphere in dimension `n` under both characteristic maps is the 'equator' of
  the sphere in dimension `n + 1`. -/
lemma spheremaps_image_sphere (n : ℕ) (i : Fin 2) :
    (spheremaps n i) '' sphere 0 1 = (sphere 0 1) ∩ {x | x (Fin.last n) = 0} :=
  match i with
  | 0 => by simp [spheremaps, ← image_image]
  | 1 => by
    simp only [spheremaps, spheremapdown_apply, ← image_image, toEuclideanNormScale_image_sphere,
      discToSphereUp_image_sphere]
    ext x
    simp only [mem_image, mem_inter_iff, mem_sphere_iff_norm, sub_zero, mem_setOf_eq]
    constructor
    · intro ⟨y, ⟨h1, h2⟩, h3⟩
      rw [← h3, LinearIsometryEquiv.norm_map, h1]
      simp [LinearIsometryEquiv.negLast, h2]
    · intro ⟨h1, h2⟩
      use x
      simp only [h1, h2, and_self, LinearIsometryEquiv.negLast, LinearIsometryEquiv.coe_mk,
        LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, neg_zero, true_and]
      rw [← h2, Function.update_eq_self]

/-- Both characterstic maps are continuous. -/
lemma continuous_spheremaps (n : ℕ) (i : Fin 2) : Continuous (spheremaps n i) :=
  match i with
  | 0 => by simp [spheremaps, spheremapup, Equiv.transPartialEquiv, continuous_discToSphereUp]
  | 1 => by simp [spheremaps, spheremapdown, Equiv.transPartialEquiv, continuous_discToSphereDown]

/-- The inverse of both characteristic maps is continuous. -/
lemma continuous_spheremaps_symm (n : ℕ) (i : Fin 2) : Continuous (spheremaps n i).symm :=
  match i with
  | 0 => by
    simp [spheremaps, spheremapup, Equiv.transPartialEquiv, continuous_discToSphereUp_symm]
  | 1 => by
    simp [spheremaps, spheremapdown, Equiv.transPartialEquiv, continuous_discToSphereDown_symm]

/-**Comment**:
  There is one last hurdle to get through: During the inductive construction we need to lift the
  CW-complex structure on the sphere in dimension `n` to a CW-complex structure on the 'equator'
  of the sphere in dimension `n + 1`. Most of the work here was in proving
  `RelCWComplex.ofPartialEquiv.`-/

/-- The 'equator' of the sphere in dimension `n + 1` receives a natural CW-complex structure from
  a CW-complex structure on the sphere in dimension `n`. -/
--@[simps!]
def sphereEmbed (n : ℕ) [CWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)] :
    CWComplex (sphere 0 1 ∩ {x | x (Fin.last n) = 0} : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
  ofPartialEquiv (X := EuclideanSpace ℝ (Fin n)) (Y := EuclideanSpace ℝ (Fin (n + 1)))
    (sphere 0 1) (sphere 0 1 ∩ {x | x (Fin.last n) = 0})
    (isClosed_sphere.inter (isClosed_plane n))
    ((PartialEquiv.EuclideanSpaceSucc n).restr (sphere 0 1))
    (by simp)
    (by rw [← PartialEquiv.image_source_eq_target];
        simp [PartialEquiv.EuclideanSpaceSucc_image_sphere])
    (PartialEquiv.continuous_EuclideanSpaceSucc n).continuousOn
    (PartialEquiv.continuous_EuclideanSpaceSucc_symm n).continuousOn

/-- If the CW-complex structure on the sphere in dimension `n` is fintite than so is the
  the CW-complex structure on the 'equator' of the sphere in dimension `n + 1`. -/
lemma finite_sphereEmbed (n : ℕ) [CWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    [Finite (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)] :
    letI := sphereEmbed n
    Finite (sphere 0 1 ∩ {x | x (Fin.last n) = 0} : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
  let _ := sphereEmbed n
  finite_ofPartialEquiv ..

/-- If the Cw-complex structure on the sphere in dimension `n` has no cells in dimension
  `n` or higher then the CW-complex structure on the 'equator' of the sphere in dimension
  `n + 1` does not either. -/
lemma isEmpty_cell_sphereEmbed (n : ℕ) [CWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    (h : ∀ m ≥ n, IsEmpty (cell (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) m)) :
    letI := sphereEmbed n
    ∀ m ≥ n, IsEmpty
      (cell (sphere 0 1 ∩ {x | x (Fin.last n) = 0} : Set (EuclideanSpace ℝ (Fin (n + 1)))) m) := by
  simp only [ge_iff_le, sphereEmbed]
  exact h

/-**Comment**: We can now show that the actual induction step works. -/

/-- An auxiliary version of `SphereInductStep` where the set is presented in a nicer way. -/
@[simps! -isSimp]
def SphereInductStep' (n : ℕ) [CWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    [Finite (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    (h : ∀ m ≥ n, IsEmpty (cell (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) m)) :
    CWComplex ((⋃ (i : Fin 2), spheremaps n i '' (closedBall 0 1)) ∪
      (sphere 0 1 ∩ {x | x (Fin.last n) = 0})) :=
  letI := sphereEmbed n
  letI := finite_sphereEmbed n
  attachCellsFiniteType (sphere 0 1 ∩ {x | x (Fin.last n) = 0}) (ι := Fin 2)
    (spheremaps n)
    (fun i ↦ match i with
      | 0 => spheremaps_source n 0
      | 1 => spheremaps_source n 1)
    (fun i ↦ match i with
      | 0 => (continuous_spheremaps n 0).continuousOn
      | 1 => (continuous_spheremaps n 1).continuousOn)
    (fun i ↦ match i with
      | 0 => (continuous_spheremaps_symm n 0).continuousOn
      | 1 => (continuous_spheremaps_symm n 1).continuousOn)
    (fun i ↦ match i with
      | 0 => by
        intro m j
        apply Disjoint.mono_right (c := (sphere 0 1 ∩ {x | x (Fin.last n) = 0}))
        · exact openCell_subset_complex _ _
        · simp_rw [← spheremaps_source n 0, spheremaps, (spheremapup n).image_source_eq_target,
            spheremapup_target]
          apply Disjoint.mono inter_subset_right inter_subset_right
          simp only [disjoint_iff_inter_eq_empty, ← setOf_and]
          suffices ∀ (a : EuclideanSpace ℝ (Fin (n + 1))),
              ¬ (0 < a (Fin.last n) ∧ a (Fin.last n) = 0) by
            simp [this]
          intro a ha
          linarith
      | 1 => by
        intro m j
        apply Disjoint.mono_right (c := (sphere 0 1 ∩ {x | x (Fin.last n) = 0}))
        · exact openCell_subset_complex _ _
        · simp_rw [← spheremaps_source n 1, spheremaps, (spheremapdown n).image_source_eq_target,
            spheremapdown_target, discToSphereUp_target]
          simp_all only [ge_iff_le, cell_def, gt_iff_lt, preimage_inter,
            LinearIsometryEquiv.preimage_sphere, LinearIsometryEquiv.symm_symm, map_zero,
            preimage_setOf_eq]
          apply Disjoint.mono inter_subset_right inter_subset_right
          simp only [LinearIsometryEquiv.symm, LinearIsometryEquiv.negLast,
            LinearIsometryEquiv.coe_mk, LinearEquiv.coe_symm_mk, disjoint_iff_inter_eq_empty]
          suffices ∀ (a : EuclideanSpace ℝ (Fin (n + 1))),
              ¬ (0 > a (Fin.last n) ∧ a (Fin.last n) = 0) by
            simp [eq_empty_iff_forall_notMem, this]
          intro a ha
          linarith)
    (fun i j ↦ match i,j with
      | 0, 0 => fun h ↦ (h rfl).elim
      | 0, 1 => by
        intro h
        nth_rw 1 [← spheremaps_source n 0, ← spheremaps_source n 1]
        simp_rw [spheremaps, (spheremapdown n).image_source_eq_target,
          (spheremapup n).image_source_eq_target, spheremapdown_target, spheremapup_target,
          discToSphereUp_target, gt_iff_lt, preimage_inter, LinearIsometryEquiv.preimage_sphere,
          LinearIsometryEquiv.symm_symm, map_zero, preimage_setOf_eq]
        apply Disjoint.mono inter_subset_right inter_subset_right
        simp only [LinearIsometryEquiv.symm, LinearIsometryEquiv.negLast,
          LinearIsometryEquiv.coe_mk, LinearEquiv.coe_symm_mk, Function.update_self,
          Left.neg_pos_iff, disjoint_iff_inter_eq_empty, ← setOf_and]
        suffices ∀ (a : EuclideanSpace ℝ (Fin (n + 1))),
            ¬ (0 < a (Fin.last n) ∧ a (Fin.last n) < 0) by
          simp [this]
        intro a ha
        linarith
      | 1, 0 => by
        intro h
        nth_rw 1 [← spheremaps_source n 1, ← spheremaps_source n 0]
        simp_rw [spheremaps, (spheremapdown n).image_source_eq_target,
          (spheremapup n).image_source_eq_target, spheremapdown_target, spheremapup_target,
          discToSphereUp_target]
        simp_all only [ge_iff_le, cell_def, ne_eq, one_ne_zero, not_false_eq_true,
          gt_iff_lt, preimage_inter, LinearIsometryEquiv.preimage_sphere,
          LinearIsometryEquiv.symm_symm, map_zero, preimage_setOf_eq]
        apply Disjoint.mono inter_subset_right inter_subset_right
        simp only [LinearIsometryEquiv.symm, LinearIsometryEquiv.negLast,
          LinearIsometryEquiv.coe_mk, LinearEquiv.coe_symm_mk, Function.update_self,
          Left.neg_pos_iff, disjoint_iff_inter_eq_empty, ← setOf_and]
        suffices ∀ (a : EuclideanSpace ℝ (Fin (n + 1))),
            ¬ (0 > a (Fin.last n) ∧ a (Fin.last n) > 0) by
          simp [this]
        intro a ha
        linarith
      | 1, 1 => fun h ↦ (h rfl).elim)
    (by
      intro i
      simp_rw [mapsTo', spheremaps_image_sphere n i,
        ← union (C := (sphere 0 1 ∩ {x : EuclideanSpace ℝ (Fin (n + 1)) | x (Fin.last n) = 0}))]
      apply iUnion_subset fun l ↦ ?_
      apply iUnion_subset fun j ↦ ?_
      apply subset_iUnion_of_subset l
      refine subset_iUnion_of_subset ?_ (subset_iUnion _ j)
      by_contra hl
      rw [not_lt] at hl
      exact (isEmpty_cell_sphereEmbed n h l hl).false j)

/-- An auxiliary version of `Finite_SphereInductStep` where the set is presented in a nicer way. -/
lemma finite_SphereInductStep' (n : ℕ) [CWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    [Finite (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    (h : ∀ m ≥ n, IsEmpty (cell (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) m)) :
    letI := SphereInductStep' n h
    Finite ((⋃ (i : Fin 2), spheremaps n i '' (closedBall 0 1)) ∪
      (sphere 0 1 ∩ {x | x (Fin.last n) = 0})) :=
  letI := sphereEmbed n
  letI := finite_sphereEmbed n
  letI := SphereInductStep' n
  finite_attachCellsFiniteType ..

/-- An auxiliary version of `isEmpty_cell_SphereInductStep` where the set is presented in a nicer
  way. -/
lemma isEmpty_cell_SphereInductStep' (n : ℕ)
    [CWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    [Finite (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    (h : ∀ m ≥ n, IsEmpty (cell (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) m)) :
    letI := SphereInductStep' n h
    ∀ m ≥ n + 1, IsEmpty
      (cell ((⋃ (i : Fin 2), spheremaps n i '' (closedBall 0 1)) ∪
      (sphere 0 1 ∩ {x | x (Fin.last n) = 0})) m) := by
  let _ := SphereInductStep' n h
  intro m hm
  rw [SphereInductStep', cell_def]
  simp only [attachCellsFiniteType_cell, RelCWComplex.attachCells_cell,
    (Nat.lt_of_succ_le hm).ne.symm, isEmpty_sum, isEmpty_pprod, not_isEmpty_of_nonempty,
    isEmpty_Prop, not_false_eq_true, false_or, and_true]
  exact h m (Nat.le_of_succ_le hm)

/-- If the sphere in dimension `n` is a finite CW-complex that has no cells in dimension
  `n` or higher, then the sphere in dimension `n + 1` is a CW-complex. -/
@[simps! -isSimp]
def SphereInductStep (n : ℕ) [CWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    [Finite (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    (h : ∀ m ≥ n, IsEmpty (cell (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) m)) :
    CWComplex (sphere 0 1 : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
  letI := SphereInductStep' n h
  ofEq
    ((⋃ (i : Fin 2),
      spheremaps n i '' (closedBall 0 1)) ∪ (sphere 0 1 ∩ {x | x (Fin.last n) = 0}))
    (E := sphere 0 1)
    (by
      apply subset_antisymm
      · apply union_subset
        · apply iUnion_subset
          exact fun i ↦ match i with
            | 0 => by
              simp only [spheremaps, spheremapup_image_closedBall]
              exact inter_subset_left
            | 1 => by
              simp only [spheremaps, spheremapdown_image_closedBall]
              exact inter_subset_left
        · exact inter_subset_left
      · intro x hx
        left
        rw [mem_iUnion]
        by_cases hx' : x (Fin.last n) ≥ 0
        · use 0
          simp only [spheremaps, spheremapup_image_closedBall, ge_iff_le, mem_inter_iff, hx,
            mem_setOf_eq, hx', and_self]
        · use 1
          simp only [ge_iff_le, not_le] at hx'
          simp only [spheremaps, spheremapdown_image_closedBall, mem_inter_iff, hx, mem_setOf_eq,
            hx'.le, and_self])

/-- If the sphere in dimension `n` is a finite CW-complex that has no cells in dimension
  `n` or higher, then the CW-complex structure on the sphere in dimension `n + 1` is finite. -/
lemma finite_SphereInductStep (n : ℕ)
    [CWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    [Finite (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    (h : ∀ m ≥ n, IsEmpty (cell (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) m)) :
    letI := SphereInductStep n h
    Finite (sphere 0 1 : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
  let _ := SphereInductStep' n h
  letI := SphereInductStep n h
  let _ := finite_SphereInductStep'
  finite_ofEq ..

/-- If the sphere in dimension `n` is a finite CW-complex that has no cells in dimension
  `n` or higher, then the CW-complex structure on the sphere in dimension `n + 1` has no cell in
  dimension `n + 1` or higher. -/
lemma isEmpty_cell_SphereInductStep (n : ℕ)
    [CWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    [Finite (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    (h : ∀ m ≥ n, IsEmpty (cell (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) m)) :
    letI := SphereInductStep n h
    ∀ m ≥ n + 1, IsEmpty (cell (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) := by
  letI := SphereInductStep n h
  intro m hm
  simp only [SphereInductStep, RelCWComplex.ofEq_cell]
  exact isEmpty_cell_SphereInductStep' n h m hm

/-**Comment**:
  We can now put all that we have proved together into an induction.
  We need to carry the two properties (finiteness and no cells in high dimensions) through the
  induction. -/

/-- An auxiliary induction for the CW-complex structure on the sphere. -/
def SphereInduct' (n : ℕ) :
  {_C : CWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) //
    Finite (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
    (∀ m ≥ n, IsEmpty (cell (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) m))} :=
  match n with
  | 0 => ⟨SphereZero 0 1 (one_ne_zero), finite_SphereZero 0 1 (one_ne_zero),
    fun m _ ↦ isEmpty_cell_SphereZero 0 1 (one_ne_zero) m⟩
  | (m + 1) =>
    letI := (SphereInduct' m).1
    letI := (SphereInduct' m).2.1
    letI h := (SphereInduct' m).2.2
    ⟨SphereInductStep m h, finite_SphereInductStep m h, isEmpty_cell_SphereInductStep m h⟩

/-- The unit sphere is a CW-complex. This construction uses two cells in each dimension. See
  `instSphere` for an alternative construction. -/
def SphereInduct (n : ℕ) : CWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  SphereInduct' n

/-- The CW-complex structure on the sphere is finite. -/
lemma Finite_SphereInduct (n : ℕ) :
    letI := SphereInduct n
    Finite (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  (SphereInduct' n).2.1

/-**Comment**: I chose to not make this definition an instance as then the two different
  instances would interfere and I think that the other construction is to be preferred in
  the case that the construction does not matter.
  But we can still this use this construction. -/

/- This also works. 🎉-/
example : CWComplex (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := SphereInduct 2

/- **ToDo** :
  Generalize this to other centre points, radii and metrics. This should be fairly easy using
  `normScale` and some generalization of `affineHomeomorph` (that possibly needs to be defined). -/

end Topology.CWComplex
