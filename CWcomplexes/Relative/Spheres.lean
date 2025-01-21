import CWcomplexes.Relative.SpheresAux
import Mathlib.Topology.Constructions

noncomputable section

open Metric Set

namespace ClasCWComplex

variable {X : Type*} [t : TopologicalSpace X] [T2Space X]

def SphereZero (x : EuclideanSpace ℝ (Fin 0)) (ε : ℝ) (h : ε ≠ 0) : ClasCWComplex (sphere x ε) :=
  ofEq ∅ ∅ (E := (sphere x ε)) (sphere_eq_empty_of_subsingleton h).symm rfl

lemma Finite_SphereZero (x : EuclideanSpace ℝ (Fin 0)) (ε : ℝ) (h : ε ≠ 0) :
    letI := SphereZero x ε h
    Finite (sphere x ε) :=
  finite_ofEq ..

def SphereOne (x ε : ℝ) (hε : ε ≥ 0) : ClasCWComplex (sphere x ε) :=
  RelCWComplex.ofEq {x - ε, x + ε} ∅ (by
    ext y
    simp [abs_eq hε]
    rw[or_comm]
    congrm (?_ ∨ ?_)
    · rw [sub_eq_iff_eq_add, add_comm]
    · rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, sub_eq_iff_eq_add,
        zero_add])
    rfl

lemma Finite_SphereOne (x ε : ℝ) (hε : ε ≥ 0) :
    letI := SphereOne x ε hε
    Finite (sphere x ε) :=
  finite_ofEq ..

def SphereOneEuclidean (ε : ℝ) (x : EuclideanSpace ℝ (Fin 1)) (hε : ε ≥ 0) :
    ClasCWComplex (sphere x ε) :=
  letI := SphereOne (EuclideanUnique ℝ (Fin 1) x) ε hε
  ofHomeomorph (sphere (EuclideanUnique ℝ (Fin 1) x) ε : Set ℝ) (sphere x ε)
  (EuclideanUnique ℝ (Fin 1)).symm.toHomeomorph (by simp)

lemma Finite_SphereOneEuclidean (ε : ℝ) (x : EuclideanSpace ℝ (Fin 1)) (hε : ε ≥ 0) :
    letI := SphereOneEuclidean ε x hε
    Finite (sphere x ε) :=
  let _ := SphereOne (EuclideanUnique ℝ (Fin 1) x) ε hε
  let _ := Finite_SphereOne (EuclideanUnique ℝ (Fin 1) x) ε hε
  Finite_ofHomeomorph ..

/-! # Construction with two cells overall. -/

open Metric in
@[simps!]
def sphereToDisc1 (n : ℕ) :=
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := {
    out := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1)}
  PartialHomeomorph.transHomeomorph
    (stereographic'
      (E := EuclideanSpace ℝ (Fin (n + 1))) n ⟨EuclideanSpace.single (Fin.last n) 1, by simp⟩)
    Homeomorph.unitBall

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

lemma sphereToDisc_symm_image_ball (n : ℕ) :
    (sphereToDisc n).symm '' ball 0 1 = sphere 0 1 \ {EuclideanSpace.single (Fin.last n) 1} := by
  simp only [← sphereToDisc_target, PartialEquiv.symm_image_target_eq_source, sphereToDisc_source]

lemma sphereToDisc_symm_image_closedBall (n : ℕ) (h : n > 0) :
    (sphereToDisc n).symm '' closedBall 0 1 = sphere 0 1 := by
  rw [← ball_union_sphere, image_union, sphereToDisc_symm_image_ball]
  suffices ↑(sphereToDisc n).symm '' sphere 0 1 = {EuclideanSpace.single (Fin.last n) 1} by
    rw [this, diff_union_self, union_eq_left]
    simp
  apply subset_antisymm
  · simp_rw [subset_singleton_iff, mem_image]
    intro y ⟨x, hx, hxy⟩
    simp_all
  · simp only [singleton_subset_iff, mem_image]
    use EuclideanSpace.single ⟨0, h⟩ 1
    simp

lemma sphereToDisc_comp_val {n : ℕ} :
    (sphereToDisc n).symm ∘ (Subtype.val (p := fun x ↦ x ∈ ball 0 1)) =
    Subtype.val ∘ (sphereToDisc1 n).symm := by
  ext
  simp

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
  simp only [sphereToDisc1, ← PartialEquiv.invFun_as_coe,
    PartialHomeomorph.transHomeomorph_symm_apply]
  rw [← Filter.tendsto_comap_iff]
  have : EuclideanSpace.single (Fin.last n) 1 = Subtype.val
      (⟨(EuclideanSpace.single (Fin.last n) 1), by simp⟩ :
      sphere (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1) := rfl
  nth_rw 2 [this]
  rw [← nhds_induced, ← Filter.tendsto_map'_iff]
  apply stereographic'_symm_tendsto
  rw [Filter.tendsto_map'_iff]
  exact Homeomorph.tendsto_norm_comp_unitBall_symm x hx

lemma sphereToDisc_symm_continuousOn {n : ℕ} (hn : n > 0) :
    ContinuousOn (sphereToDisc n).symm (closedBall 0 1) := by
  simp only [← PartialEquiv.invFun_as_coe, ← ball_union_sphere, ContinuousOn]
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
    · apply continuousWithinAt_of_not_mem_closure
      rw [closure_sphere]
      intro h
      simp_all
    · refine ContinuousOn.continuousWithinAt ?_ hx
      rw [continuousOn_iff_continuous_restrict]
      have : (sphere 0 1).restrict (sphereToDisc n).invFun =
          fun y ↦ EuclideanSpace.single (Fin.last n) 1 := by
        ext y
        simp
      rw [this]
      exact continuous_const

lemma sphereToDisc_continuousOn (n : ℕ) : ContinuousOn (sphereToDisc n)
    (sphere 0 1 \ {EuclideanSpace.single (Fin.last n) 1}) := by
  simp only [sphereToDisc]
  unfold ContinuousOn
  intro x ⟨hx1, hx2⟩
  rw [continuousWithinAt_diff_singleton]
  rw [continuousWithinAt_iff_continuousAt_restrict _ hx1]
  apply ContinuousAt.congr (f := Subtype.val ∘ sphereToDisc1 n)
  · apply continuous_subtype_val.continuousAt.comp
    apply ContinuousOn.continuousAt (s := {⟨EuclideanSpace.single (Fin.last n) 1, by simp⟩}ᶜ)
    · exact sphereToDisc1_source n ▸ (sphereToDisc1 n).continuousOn
    simp_all
  · apply Eq.eventuallyEq
    ext
    simp

@[simps!]
def spheremap (n : ℕ) : PartialEquiv (Fin n → ℝ) (EuclideanSpace ℝ (Fin (n + 1))) :=
  (toEuclideanNormScale n).transPartialEquiv (sphereToDisc n).symm

@[simps!]
def instSphereGT' (n : ℕ) (h : n > 0) :
    ClasCWComplex ((spheremap n) '' closedBall 0 1 ∪ {EuclideanSpace.single (Fin.last n) 1}) :=
  attachCellFiniteType {EuclideanSpace.single (Fin.last n) 1}
  (spheremap n)
  (source_eq' := by
    ext x
    simp)
  (continuousOn' := by
    simp only [spheremap, Equiv.transPartialEquiv, PartialEquiv.coe_trans,
      Equiv.toPartialEquiv_apply, Homeomorph.coe_toEquiv, PartialEquiv.coe_trans_symm,
      Equiv.toPartialEquiv_symm_apply, Homeomorph.coe_symm_toEquiv, PartialEquiv.symm_symm,
      PartialEquiv.symm_source, sphereToDisc_target, PartialEquiv.symm_target, sphereToDisc_source,
      PartialEquiv.copy_apply]
    apply (sphereToDisc_symm_continuousOn h).comp (toEuclideanNormScale n).continuous.continuousOn
    rw [mapsTo', toEuclideanNormScale_image_closedBall])
  (continuousOn_symm' := by
    simp [spheremap, Equiv.transPartialEquiv, sphereToDisc_continuousOn])
  (disjoint' := by
    intro m i
    exact match m, i with
      | 0, ⟨i, hi⟩ => by
        simp only [spheremap, Equiv.transPartialEquiv_apply, Homeomorph.coe_toEquiv, ← image_image,
          toEuclideanNormScale_image_ball, sphereToDisc_symm_image_ball, openCell_zero_eq_singleton,
          instFiniteSet_map, PartialEquiv.single_apply, Function.const_apply,
          disjoint_singleton_right]
        exact not_mem_diff_of_mem hi
      | (_ + 1), i => i.elim)
  (mapsto' := by
    rw [mapsTo']
    apply subset_iUnion_of_subset 0
    apply subset_iUnion_of_subset h
    simp only [instFiniteSet_cell, closedCell_zero_eq_singleton]
    apply subset_iUnion_of_subset ⟨EuclideanSpace.single (Fin.last n) 1, rfl⟩
    simp only [spheremap, Equiv.transPartialEquiv_apply, ← image_image, Homeomorph.coe_toEquiv,
      toEuclideanNormScale_image_sphere, subset_singleton_iff]
    intro y hy
    simp only [instFiniteSet_map, PartialEquiv.single_apply, Function.const_apply]
    simp only [mem_image, sphereToDisc_symm_apply] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    simp_all)

def Finite_instSphereGT' (n : ℕ) (h : n > 0) :
    letI := instSphereGT' n h
    Finite ((spheremap n) '' closedBall 0 1 ∪ {EuclideanSpace.single (Fin.last n) 1}) :=
  Finite_attachCellFiniteType ..

@[simps!]
def instSphereGT (n : ℕ) (h : n > 0) :
    ClasCWComplex (sphere 0 1 : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
  let _ := instSphereGT' n h
  ofEq (E := sphere 0 1)
  ((spheremap n) '' closedBall 0 1 ∪ {EuclideanSpace.single (Fin.last n) 1}) ∅
  (by
    simp only [spheremap, Equiv.transPartialEquiv_apply, Homeomorph.coe_toEquiv, ← image_image,
      toEuclideanNormScale_image_closedBall, sphereToDisc_symm_image_closedBall n h, union_eq_left,
      singleton_subset_iff, mem_sphere_iff_norm, sub_zero, EuclideanSpace.norm_single, norm_one])
  rfl

lemma Finite_instSphereGT (n : ℕ) (h : n > 0) :
    letI := instSphereGT n h
    Finite (sphere 0 1 : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
  let _ := instSphereGT' n h
  let _ := Finite_instSphereGT' n h
  finite_ofEq ((spheremap n) '' closedBall 0 1 ∪ {EuclideanSpace.single (Fin.last n) 1}) ∅
  (by
    simp only [spheremap, Equiv.transPartialEquiv_apply, Homeomorph.coe_toEquiv, ← image_image,
      toEuclideanNormScale_image_closedBall, sphereToDisc_symm_image_closedBall n h, union_eq_left,
      singleton_subset_iff, mem_sphere_iff_norm, sub_zero, EuclideanSpace.norm_single, norm_one])
  rfl

/-! # Construction with two cells in every dimension. -/

@[simps]
def discToSphereUp (n : ℕ) :
    PartialEquiv (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin (n + 1))) where
  toFun := fun x ↦ Fin.snoc x (√(1 - ‖x‖ ^ 2))
  invFun := Fin.init
  source := closedBall 0 1
  target := sphere 0 1 ∩ {x | x (Fin.last n) ≥ 0}
  map_source' x hx := by
    constructor
    · rw [mem_sphere_iff_norm, sub_zero, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow,
        EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)),
        Fin.sum_univ_castSucc]
      simp only [Fin.snoc, Fin.coe_castSucc, Fin.is_lt, ↓reduceDIte, Fin.castLT_castSucc, cast_eq,
        Real.norm_eq_abs, sq_abs, Fin.val_last, lt_self_iff_false]
      rw [Real.sq_sqrt (by simp_all), ← Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))]
      simp_rw [← sq_abs (x _), ← Real.norm_eq_abs, ← EuclideanSpace.norm_eq, add_sub_cancel]
    · simp
  map_target' y:= by
    intro ⟨hy, _⟩
    simp_all only [mem_sphere_iff_norm, sub_zero, ge_iff_le, mem_setOf_eq, mem_closedBall,
      dist_zero_right]
    rw [← hy]
    exact EuclideanSpace.norm_finInit_le _
  left_inv' x hx := by simp
  right_inv' y := by
    intro ⟨hy1, hy2⟩
    simp_all
    suffices √(1 - norm (Fin.init y) (self := (PiLp.instNorm 2 fun x ↦ ℝ)) ^ 2) = y (Fin.last n) by
      rw [this, Fin.snoc_init_self]
    have : norm (Fin.init y) (self := (PiLp.instNorm 2 fun x ↦ ℝ)) ≤ 1 := by
      rw [← hy1]
      exact EuclideanSpace.norm_finInit_le y
    rw [← sq_eq_sq₀ (Real.sqrt_nonneg _) hy2, Real.sq_sqrt (by simp_all), EuclideanSpace.norm_eq,
      ← one_pow (n := 2), ← hy1, EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)),
      Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)), sub_eq_iff_eq_add,
      Fin.sum_univ_castSucc, add_comm, Real.norm_eq_abs, sq_abs]
    rfl

lemma continuous_discToSphereUp (n : ℕ) : Continuous (discToSphereUp n) := by
  simp only [discToSphereUp]
  apply Continuous.finSnoc
  · exact continuous_id'
  · continuity

lemma continuous_discToSphereUp_symm (n : ℕ) : Continuous (discToSphereUp n).symm :=
  Continuous.finInit

@[simps!]
def discToSphereDown (n : ℕ) := (discToSphereUp n).transEquiv (Homeomorph.negLast n).toEquiv

lemma continuous_discToSphereDown (n : ℕ) : Continuous (discToSphereDown n) := by
  simp [discToSphereDown, PartialEquiv.transEquiv, continuous_discToSphereUp]

lemma continuous_discToSphereDown_symm (n : ℕ) : Continuous (discToSphereDown n).symm := by
  simp [discToSphereDown, PartialEquiv.transEquiv, continuous_discToSphereUp_symm]

def spheremapup (n : ℕ) := (toEuclideanNormScale n).transPartialEquiv (discToSphereUp n)

def spheremapdown (n : ℕ) := (toEuclideanNormScale n).transPartialEquiv (discToSphereDown n)


-- we first need to make sense of embedding a CW-complex
def sphereInductStep' (n : ℕ) [ClasCWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    [Finite (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)] :
    ClasCWComplex (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  sorry


/-! # Compiled Instances-/

instance instSphere {n : ℕ} : ClasCWComplex (sphere 0 1 : Set (EuclideanSpace ℝ (Fin n))) :=
  match n with
  | 0 => SphereZero 0 1 one_ne_zero
  | 1 => SphereOneEuclidean 1 0 zero_le_one
  | (n + 2) => instSphereGT (n + 1) n.zero_lt_succ

-- see above
instance Finite_instSphere {n : ℕ} : Finite (sphere 0 1 : Set (EuclideanSpace ℝ (Fin n))) :=
  match n with
  | 0 => Finite_SphereZero 0 1 one_ne_zero
  | 1 => Finite_SphereOneEuclidean 1 0 zero_le_one
  | (n + 2) => Finite_instSphereGT (n + 1) n.zero_lt_succ

example : ClasCWComplex
    (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 ×ˢ sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
  inferInstance

end ClasCWComplex
