import CWcomplexes.Relative.Project.SpheresAux
import CWcomplexes.Relative.Project.Homeomorph
import Mathlib.Topology.Constructions

/-!
# Spheres are CW-complexes
In this file we provide two different CW-complex structures on the sphere.
## Main definitions
* `instSphere`: The unit sphere is a CW-complex. This construction uses two cells in total.
* `SphereInduct`: The unit sphere is a CW-complex. This construction uses two cells in each
  dimension.
-/

noncomputable section

open Metric Set

namespace ClasCWComplex

variable {X : Type*} [t : TopologicalSpace X] [T2Space X]

/-! # Spheres in dimensions zero and one -/

/-- The sphere in dimension zero is a CW-complex. -/
@[simps!]
def SphereZero (x : EuclideanSpace ℝ (Fin 0)) (ε : ℝ) (h : ε ≠ 0) : ClasCWComplex (sphere x ε) :=
  ofEq ∅ ∅ (E := (sphere x ε)) (sphere_eq_empty_of_subsingleton h).symm rfl

/-- The CW-complex structure on the sphere in dimension zero  is finite. -/
lemma Finite_SphereZero (x : EuclideanSpace ℝ (Fin 0)) (ε : ℝ) (h : ε ≠ 0) :
    letI := SphereZero x ε h
    Finite (sphere x ε) :=
  finite_ofEq ..

/-- The CW-complex structure on the sphere in dimension 0 has no cells. This is an auxiliary lemma
  for `AuxSphereInduct`. -/
lemma isEmpty_cell_SphereZero (x : EuclideanSpace ℝ (Fin 0)) (ε : ℝ) (h : ε ≠ 0)  :
    letI := SphereZero x ε h
    ∀ m, IsEmpty (cell (sphere x ε) m) := by
  intro m
  simp only [RelCWComplex.ofEq_cell, instEmpty_cell]
  infer_instance

/-- The sphere in dimension 1 is a CW-complex. -/
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

/-- The CW-complex structure on the sphere in dimension 1 in finite. -/
lemma Finite_SphereOne (x ε : ℝ) (hε : ε ≥ 0) :
    letI := SphereOne x ε hε
    Finite (sphere x ε) :=
  finite_ofEq ..

/-- The sphere as a CW-complex in `ℝ` with the euclidean metric. -/
def SphereOneEuclidean (ε : ℝ) (x : EuclideanSpace ℝ (Fin 1)) (hε : ε ≥ 0) :
    ClasCWComplex (sphere x ε) :=
  letI := SphereOne (EuclideanUnique ℝ (Fin 1) x) ε hε
  ofHomeomorph (sphere (EuclideanUnique ℝ (Fin 1) x) ε : Set ℝ) (sphere x ε)
  (EuclideanUnique ℝ (Fin 1)).symm.toHomeomorph (by simp)

/-- The CW-complex structure on the sphere in `ℝ` with he euclidean metric is finite. -/
lemma Finite_SphereOneEuclidean (ε : ℝ) (x : EuclideanSpace ℝ (Fin 1)) (hε : ε ≥ 0) :
    letI := SphereOneEuclidean ε x hε
    Finite (sphere x ε) :=
  let _ := SphereOne (EuclideanUnique ℝ (Fin 1) x) ε hε
  let _ := Finite_SphereOne (EuclideanUnique ℝ (Fin 1) x) ε hε
  Finite_ofHomeomorph ..

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
@[simps!]
def sphereToDisc' (n : ℕ) :=
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := {
    out := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1)}
  PartialHomeomorph.transHomeomorph
    (stereographic'
      (E := EuclideanSpace ℝ (Fin (n + 1))) n ⟨EuclideanSpace.single (Fin.last n) 1, by simp⟩)
    Homeomorph.unitBall

open Classical in
/-- A partial bijection sending the sphere in dimension `n + 1` to the closed ball in dimension
  `n`.-/
@[simps]
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
    simp [hx2]
  right_inv' y hy := by
    have h :
        ↑((sphereToDisc' n).symm ⟨y, hy⟩) ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
      exact Subtype.coe_prop ((sphereToDisc' n).symm ⟨y, hy⟩)
    simp only [hy, h, ↓reduceDIte]
    have : y = (⟨y, hy⟩ : ball (0 : EuclideanSpace ℝ (Fin n)) 1) := rfl
    conv => rhs; rw [this]
    rw [SetCoe.ext_iff]
    apply PartialEquiv.right_inv
    simp

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
  · simp_rw [subset_singleton_iff, mem_image]
    intro y ⟨x, hx, hxy⟩
    simp_all
  · simp only [singleton_subset_iff, mem_image]
    use EuclideanSpace.single ⟨0, h⟩ 1
    simp

/-- `sphereToDisc` is the same as `sphereToDisc'` on the ball. -/
lemma sphereToDisc_comp_val {n : ℕ} :
    (sphereToDisc n).symm ∘ (Subtype.val (p := fun x ↦ x ∈ ball 0 1)) =
    Subtype.val ∘ (sphereToDisc' n).symm := by
  ext
  simp

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
  simp only [sphereToDisc', ← PartialEquiv.invFun_as_coe,
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

/-- The CW-complex structure on the sphere is finite. An auxiliary version of `Finite_instSphereGT`
  where the set is presented in a nicer way. -/
lemma Finite_instSphereGT' (n : ℕ) (h : n > 0) :
    letI := instSphereGT' n h
    Finite ((spheremap n) '' closedBall 0 1 ∪ {EuclideanSpace.single (Fin.last n) 1}) :=
  Finite_attachCellFiniteType ..

/-- The sphere in dimension at least 1 is a CW-complex. -/
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

/-- The CW-complex structure on the sphere in dimension at least 1 is finite. -/
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

/- **Comment**: We can now compile what we have proven so far into nice instances.-/

/-- The unit sphere is a CW-complex. This construction uses two cells in total. For an
  alternative construction see `SphereInduct`. -/
instance instSphere {n : ℕ} : ClasCWComplex (sphere 0 1 : Set (EuclideanSpace ℝ (Fin n))) :=
  match n with
  | 0 => SphereZero 0 1 one_ne_zero
  | 1 => SphereOneEuclidean 1 0 zero_le_one
  | (n + 2) => instSphereGT (n + 1) n.zero_lt_succ

/-- The CW-complex structure on the sphere is finite. -/
instance Finite_instSphere {n : ℕ} : Finite (sphere 0 1 : Set (EuclideanSpace ℝ (Fin n))) :=
  match n with
  | 0 => Finite_SphereZero 0 1 one_ne_zero
  | 1 => Finite_SphereOneEuclidean 1 0 zero_le_one
  | (n + 2) => Finite_instSphereGT (n + 1) n.zero_lt_succ

/- **ToDo** :
  Generalize this to other centre points, radii and metrics. This should be fairly easy using
  `normScale` and some generalization of `affineHomeomorph` (that possibly needs to be defined). -/

/- This works now. 🎉-/
example : ClasCWComplex (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) := inferInstance

/- **Comment** : We now even get the CW-structure on the torus for free. -/

example : ClasCWComplex
    (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 ×ˢ sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
  inferInstance

/-! # Construction with two cells in every dimension. -/

/-**Comment**:
  We now move onto the second popular construction for the sphere:
  We construct the spheres inductively adding two cells in each dimension.
  While the actual construction is way more difficult, the characteristic maps are a lot
  simpler. -/

/-- A partial bijection sending the open ball in dimension `n` to the upper hemisphere
  (without the equator) of the sphere in dimension `n + 1`. -/
@[simps]
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

/-- `discToSphereUp` is continuous.-/
lemma continuous_discToSphereUp (n : ℕ) : Continuous (discToSphereUp n) := by
  simp only [discToSphereUp]
  apply Continuous.finSnoc
  · exact continuous_id'
  · continuity

/-- The inverse of `discToSphereUp` is continuous. -/
lemma continuous_discToSphereUp_symm (n : ℕ) : Continuous (discToSphereUp n).symm :=
  Continuous.finInit

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
  upper hemisphere of the sphere in dimenion `n + 1`.-/
@[simp]
lemma discToSphereUp_image_closedBall (n : ℕ) :
    (discToSphereUp n) '' closedBall 0 1 = (sphere 0 1) ∩ {x | x (Fin.last n) ≥ 0} := by
  simp [← image_image]
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
    · simp [← hy2]
  · intro ⟨h1, h2⟩
    use Fin.init x
    simp only [EuclideanSpace.norm_eq, Fin.sum_univ_castSucc, h2, Real.norm_eq_abs (r := 0),
      sq_abs, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      sq_abs, Real.sqrt_eq_one] at h1
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
  simp [← image_image, image_inter (LinearIsometryEquiv.negLast n).injective]
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
      Equiv.preimage_eq_iff_eq_image]
    simp only [Homeomorph.coe_toEquiv, toEuclideanNormScale_image_ball]
  | 1 => by
    simp only [spheremaps, spheremapdown_source, ← Homeomorph.coe_toEquiv,
      Equiv.preimage_eq_iff_eq_image]
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
        LinearEquiv.coe_mk, neg_zero, true_and]
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
  a CW-complex structure on the sphere in dimension `n`.-/
@[simps!]
def sphereEmbed (n : ℕ) [ClasCWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)] :
    ClasCWComplex (sphere 0 1 ∩ {x | x (Fin.last n) = 0} : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
  ofPartialEquiv (X := EuclideanSpace ℝ (Fin n)) (Y := EuclideanSpace ℝ (Fin (n + 1)))
    (sphere 0 1) (sphere 0 1 ∩ {x | x (Fin.last n) = 0}) isClosed_sphere
    (isClosed_sphere.inter (isClosed_plane n))
    ((PartialEquiv.EuclideanSpaceSucc n).restr (sphere 0 1))
    (by simp)
    (by rw [← PartialEquiv.image_source_eq_target];
        simp [PartialEquiv.EuclideanSpaceSucc_image_sphere])
    (PartialEquiv.continuous_EuclideanSpaceSucc n).continuousOn
    (PartialEquiv.continuous_EuclideanSpaceSucc_symm n).continuousOn

/-- If the CW-complex structure on the sphere in dimension `n` is fintite than so is the
  the CW-complex structure on the 'equator' of the sphere in dimension `n + 1`.-/
lemma Finite_sphereEmbed (n : ℕ) [ClasCWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    [Finite (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)] :
    letI := sphereEmbed n
    Finite (sphere 0 1 ∩ {x | x (Fin.last n) = 0} : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
  let _ := sphereEmbed n
  Finite_ofPartialEquiv ..

/-- If the Cw-complex structure on the sphere in dimension `n` has no cells in dimension
  `n` or higher then the CW-complex structure on the 'equator' of the sphere in dimension
  `n + 1` does not either. -/
lemma isEmpty_cell_sphereEmbed (n : ℕ) [ClasCWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    (h : ∀ m ≥ n, IsEmpty (cell (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) m)) :
    letI := sphereEmbed n
    ∀ m ≥ n, IsEmpty
      (cell (sphere 0 1 ∩ {x | x (Fin.last n) = 0} : Set (EuclideanSpace ℝ (Fin (n + 1)))) m) := by
  simp only [ge_iff_le, sphereEmbed_cell]
  exact h

/-**Comment**: We can now show that the actual induction step works. -/

/-- An auxiliary version of `SphereInductStep` where the set is presented in a nicer way. -/
@[simps! -isSimp]
def SphereInductStep' (n : ℕ) [ClasCWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    [Finite (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    (h : ∀ m ≥ n, IsEmpty (cell (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) m)) :
    ClasCWComplex ((⋃ (i : Fin 2), spheremaps n i '' (closedBall 0 1)) ∪
      (sphere 0 1 ∩ {x | x (Fin.last n) = 0})) :=
  letI := sphereEmbed n
  letI := Finite_sphereEmbed n
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
            spheremapdown_target]
          apply Disjoint.mono inter_subset_right inter_subset_right
          simp only [LinearIsometryEquiv.symm, LinearIsometryEquiv.negLast,
            LinearIsometryEquiv.coe_mk, LinearEquiv.coe_symm_mk, Function.update_self,
            Left.neg_pos_iff, disjoint_iff_inter_eq_empty, ← setOf_and]
          suffices ∀ (a : EuclideanSpace ℝ (Fin (n + 1))),
              ¬ (0 > a (Fin.last n) ∧ a (Fin.last n) = 0) by
            simp [this]
          intro a ha
          linarith)
    (fun i j ↦ match i,j with
      | 0, 0 => fun h ↦ (h rfl).elim
      | 0, 1 => by
        intro h
        nth_rw 1 [← spheremaps_source n 0, ← spheremaps_source n 1]
        simp_rw [spheremaps, (spheremapdown n).image_source_eq_target,
          (spheremapup n).image_source_eq_target, spheremapdown_target, spheremapup_target]
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
          (spheremapup n).image_source_eq_target, spheremapdown_target, spheremapup_target]
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

/-- An auxiliary version of `Finite_SphereInductStep` where the set is presented in a nicer way.-/
lemma Finite_SphereInductStep' (n : ℕ) [ClasCWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    [Finite (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    (h : ∀ m ≥ n, IsEmpty (cell (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) m)) :
    letI := SphereInductStep' n h
    Finite ((⋃ (i : Fin 2), spheremaps n i '' (closedBall 0 1)) ∪
      (sphere 0 1 ∩ {x | x (Fin.last n) = 0})) :=
  letI := sphereEmbed n
  letI := Finite_sphereEmbed n
  letI := SphereInductStep' n
  Finite_attachCellsFiniteType ..

/-- An auxiliary version of `isEmpty_cell_SphereInductStep` where the set is presented in a nicer
  way.-/
lemma isEmpty_cell_SphereInductStep' (n : ℕ)
    [ClasCWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    [Finite (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    (h : ∀ m ≥ n, IsEmpty (cell (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) m)) :
    letI := SphereInductStep' n h
    ∀ m ≥ n + 1, IsEmpty
      (cell ((⋃ (i : Fin 2), spheremaps n i '' (closedBall 0 1)) ∪
      (sphere 0 1 ∩ {x | x (Fin.last n) = 0})) m) := by
  let _ := SphereInductStep' n h
  intro m hm
  simp only [SphereInductStep'_cell, (Nat.lt_of_succ_le hm).ne.symm, isEmpty_sum, isEmpty_pprod,
    not_isEmpty_of_nonempty, isEmpty_Prop, not_false_eq_true, or_true, and_true]
  exact h m (Nat.le_of_succ_le hm)

/-- If the sphere in dimension `n` is a finite CW-complex that has no cells in dimension
  `n` or higher, then the sphere in dimension `n + 1` is a CW-complex. -/
def SphereInductStep (n : ℕ) [ClasCWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    [Finite (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    (h : ∀ m ≥ n, IsEmpty (cell (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) m)) :
    ClasCWComplex (sphere 0 1 : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
  letI := SphereInductStep' n h
  ofEq
    ((⋃ (i : Fin 2), spheremaps n i '' (closedBall 0 1)) ∪ (sphere 0 1 ∩ {x | x (Fin.last n) = 0}))
    ∅
    (E := sphere 0 1)
    (by
      apply subset_antisymm
      · apply union_subset
        · apply iUnion_subset
          exact fun i ↦ match i with
            | 0 => by
              simp only [Fin.isValue, spheremaps, spheremapup_image_closedBall]
              exact inter_subset_left
            | 1 => by
              simp only [Fin.isValue, spheremaps, spheremapdown_image_closedBall]
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
          simp only [spheremaps, spheremapdown_image_closedBall, ge_iff_le, mem_inter_iff, hx,
            mem_setOf_eq, hx'.le, and_self])
    rfl

/-- If the sphere in dimension `n` is a finite CW-complex that has no cells in dimension
  `n` or higher, then the CW-complex structure on the sphere in dimension `n + 1` is finite. -/
lemma Finite_SphereInductStep (n : ℕ)
    [ClasCWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    [Finite (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
    (h : ∀ m ≥ n, IsEmpty (cell (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) m)) :
    letI := SphereInductStep n h
    Finite (sphere 0 1 : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
  let _ := SphereInductStep' n h
  letI := SphereInductStep n h
  let _ := Finite_SphereInductStep'
  finite_ofEq ..

/-- If the sphere in dimension `n` is a finite CW-complex that has no cells in dimension
  `n` or higher, then the CW-complex structure on the sphere in dimension `n + 1` has no cell in
  dimension `n + 1` or higher. -/
lemma isEmpty_cell_SphereInductStep (n : ℕ)
    [ClasCWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)]
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
  {_C : ClasCWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) //
    Finite (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
    (∀ m ≥ n, IsEmpty (cell (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) m))} :=
  match n with
  | 0 => ⟨SphereZero 0 1 (one_ne_zero), Finite_SphereZero 0 1 (one_ne_zero),
    fun m _ ↦ isEmpty_cell_SphereZero 0 1 (one_ne_zero) m⟩
  | (m + 1) =>
    letI := (SphereInduct' m).1
    letI := (SphereInduct' m).2.1
    letI h := (SphereInduct' m).2.2
    ⟨SphereInductStep m h, Finite_SphereInductStep m h, isEmpty_cell_SphereInductStep m h⟩

/-- The unit sphere is a CW-complex. This construction uses two cells in each dimension. See
  `instSphere` for an alternative construction. -/
def SphereInduct (n : ℕ) : ClasCWComplex (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
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
example : ClasCWComplex (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) := SphereInduct 1

/- **ToDo** :
  Generalize this to other centre points, radii and metrics. This should be fairly easy using
  `normScale` and some generalization of `affineHomeomorph` (that possibly needs to be defined). -/

end ClasCWComplex
