import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Polynomial.Basic

/-!
# Auxiliary lemmas and definitions

In this file we have auxiliary lemmas that are not in mathlib but do not have any direct relation
to CW-complexes.
They are sorted by topics.
-/

noncomputable section

/-! ### Basic logic and set theory-/

/-! ### Topology -/

/-! ### PartialEquiv-/

--**PR**
-- needed in this file
/-- A partial bijection that is continuous on the source and the target restricts to a
homeomorphism. -/
@[simps]
def PartialEquiv.toHomeomorph {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (e : PartialEquiv α β) (he1 : ContinuousOn e e.source)
    (he2 : ContinuousOn e.symm e.target) : e.source ≃ₜ e.target where
  toFun := e.toEquiv
  invFun := e.toEquiv.symm
  left_inv := e.toEquiv.symm_apply_apply
  right_inv := e.toEquiv.apply_symm_apply
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (e.source.restrict e)
    rw [← continuousOn_iff_continuous_restrict]
    exact he1
  continuous_invFun := by
    apply Continuous.subtype_mk
    change Continuous (e.target.restrict e.symm)
    rw [← continuousOn_iff_continuous_restrict]
    exact he2

--**PR**
-- needed in constructions file
open Set in
/-- A partial bijection that is continuous on both source and target and where the source and
the target are closed is a closed map when restricting to the source. -/
lemma PartialEquiv.isClosed_of_isClosed_preimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : PartialEquiv X Y) (h1 : ContinuousOn e e.source)
    (h2 : ContinuousOn e.symm e.target) (he1 : IsClosed e.target) (he2 : IsClosed e.source)
    (A : Set Y) (hAe : A ⊆ e.target) (hA : IsClosed (e.source ∩ e ⁻¹' A)) : IsClosed A := by
  rw [← inter_eq_right.2 hAe, ← he1.inter_preimage_val_iff,
    ← (e.toHomeomorph h1 h2).isClosed_preimage,
    he2.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed]
  convert hA
  ext
  simp [PartialEquiv.toEquiv, and_comm]

/-! ### Random-/

/-! ### Auxiliary stuff for spheres-/

open Metric Set

/-! # Lemmas needed for the continuity of `sphereToDisc` on the sphere. -/

/-**Comment**:
  The map `sphereToDisc` is made up of (the inverses of) two maps:
  `Homeomorph.unitBall` and `stereographic'`. On the sphere these maps are not defined.
  We define `sphereToDisc` to map the sphere to the relevant unit vector.
  In order to show that ``sphereToDisc` is continuous on the sphere we need to study how
  (the inverses of) `Homeomorph.unitBall` and `stereographic'` behave as we approach the edge of
  their domain.-/

lemma sqrt_one_sub_sq_image_ico : (fun x ↦ √(1 - x ^ 2)) '' (Ico 0 1) = Ioc 0 1 := by
  ext y
  simp only [mem_Ioc, mem_image, mem_Ioo]
  constructor
  · intro ⟨z, ⟨hz1, hz2⟩, hz3⟩
    rw [← hz3]
    constructor
    · rw [Real.sqrt_pos, sub_pos, sq_lt_one_iff_abs_lt_one, abs_lt]
      exact ⟨lt_of_lt_of_le neg_one_lt_zero hz1, hz2⟩
    · rw [Real.sqrt_le_iff, one_pow]
      refine ⟨zero_le_one, ?_⟩
      apply sub_le_self
      exact sq_nonneg z
  · intro ⟨hy1, hy2⟩
    use √(1 - y ^ 2)
    refine ⟨⟨(1 - y ^ 2).sqrt_nonneg, ?_⟩, ?_⟩
    · rw [← Real.sqrt_one, Real.sqrt_lt_sqrt_iff]
      · rw [Real.sqrt_one]
        apply sub_lt_self
        exact sq_pos_of_pos hy1
      · rw [sub_nonneg, Real.sqrt_one, ← one_pow 2, sq_le_sq]
        simp [abs_le, (lt_trans neg_one_lt_zero hy1).le, hy2]
    · suffices √(1 - y ^ 2) ^ 2 = 1 - y ^ 2 by rw [this, sub_sub_cancel, Real.sqrt_sq hy1.le]
      apply Real.sq_sqrt
      rw [sub_nonneg, ← one_pow 2, sq_le_sq]
      simp [abs_le, (lt_trans neg_one_lt_zero hy1).le, hy2]

lemma Filter.Tendsto.inv_sqrt_one_sub_sq_mul :
    Filter.Tendsto (fun r ↦ (√(1 - r ^ 2))⁻¹ * r) (nhdsWithin 1 (Ico 0 1)) Filter.atTop := by
  refine Filter.Tendsto.atTop_mul_pos Real.zero_lt_one ?_
    (Filter.Tendsto.mono_left (continuous_id.continuousAt.tendsto) nhdsWithin_le_nhds)
  apply Filter.Tendsto.comp tendsto_inv_nhdsGT_zero
  refine Filter.Tendsto.mono_right (y := (nhdsWithin 0 (Ioc 0 1))) ?_
    (nhdsWithin_mono 0 Ioc_subset_Ioi_self)
  have h1 : 0 = (fun x ↦ √(1 - x ^ 2)) 1 := by simp
  nth_rw 2 [h1]
  nth_rw 1 [← sqrt_one_sub_sq_image_ico]
  apply ContinuousWithinAt.tendsto_nhdsWithin_image
  apply Continuous.continuousWithinAt
  apply Real.continuous_sqrt.comp ((continuous_sub_left 1).comp (continuous_pow 2))

lemma norm_image_ball_eq_ico {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] : norm '' ball (0 : E) 1 = Ico 0 1 := by
  ext y
  simp only [mem_Ioo, mem_image, mem_ball, dist_zero_right]
  refine ⟨fun ⟨z, hz1, hz2⟩ ↦ by simp [← hz2, hz1], ?_⟩
  intro ⟨hy1, hy2⟩
  obtain ⟨r, hr⟩ := NormedSpace.exists_lt_norm ℝ E 0
  use (y / ‖r‖) • r
  suffices ‖(y / ‖r‖) • r‖ = y by simp [this, hy2]
  simp [norm_smul, div_mul_cancel₀ _ hr.ne.symm, hy1]

/-- As we approach the sphere from inside the ball the inverse of `Homeomorph.unitBall` tends to
  infinity in its norm. -/
/- **Comment**: The proof of this statement just unfolds the definition of `Homeomorph.unitBall`
  and then applies basic facts about convergence.-/
lemma Homeomorph.tendsto_norm_comp_unitBall_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] (x : E) (hx : x ∈ sphere (0 : E) 1) :
    Filter.Tendsto (norm ∘ Homeomorph.unitBall.symm)
    (Filter.comap Subtype.val (nhds x)) Filter.atTop := by
  simp only [Homeomorph.unitBall, Homeomorph.trans, Equiv.trans, Homeomorph.coe_toEquiv,
    Homeomorph.coe_symm_toEquiv, Homeomorph.symm_symm, Homeomorph.Set.univ_apply,
    Homeomorph.homeomorph_mk_coe_symm, Equiv.coe_fn_symm_mk]
  change Filter.Tendsto
    (norm ∘ (PartialHomeomorph.univUnitBall (E := E)).symm ∘ (Subtype.val : ball (0 : E) 1 → E))
      (Filter.comap Subtype.val (nhds x)) Filter.atTop
  rw [← Function.comp_assoc, ← Filter.tendsto_map'_iff, Filter.subtype_coe_map_comap,
    PartialHomeomorph.univUnitBall, PartialHomeomorph.mk_coe_symm, PartialEquiv.coe_symm_mk]
  suffices Filter.Tendsto ((fun r ↦ (√(1 - r ^ 2))⁻¹ * r) ∘ norm)
      (nhds x ⊓ Filter.principal (ball 0 1)) Filter.atTop by
    convert this
    ext y
    simp [norm_smul]
  apply Filter.Tendsto.inv_sqrt_one_sub_sq_mul.comp
  rw [← norm_image_ball_eq_ico (E := E), (by simp_all : 1 = ‖x‖)]
  exact continuous_norm.continuousWithinAt.tendsto_nhdsWithin_image

open Polynomial Filter Topology

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] (P Q : 𝕜[X]) [OrderTopology 𝕜]

theorem div_tendsto_leadingCoeff_div_of_degree_eq (hdeg : P.degree ≤ Q.degree) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 <| P.coeff (natDegree Q) / Q.leadingCoeff) := by
  sorry

-- add lemma for polynomials ≤

-- is this actually better?
open Set Filter Polynomial in
theorem tendsto_add_mul_sq_div_add_mul_atTop_nhds' {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] (a b c d e : 𝕜) {f : 𝕜} (hf : f ≠ 0) :
    Tendsto
      (fun k : 𝕜 ↦ (a + c * k + e * k ^ 2) / (b + d * k +  f * k ^ 2)) atTop (nhds (e / f)) := by
  suffices Tendsto (fun k ↦ ((C a + C c * X + C e * X ^ 2).eval k) /
      ((C b + C d * X + C f * X ^ 2).eval k)) atTop (nhds (e / f)) by
    simp_all
  by_cases he : e = 0
  · rw [he, zero_div, Polynomial.C_0, zero_mul, add_zero]
    apply div_tendsto_zero_of_degree_lt
    have h1 : (C a + C c * X).degree ≤ 1 := by compute_degree
    have h2 :  (C b + C d * X + C f * X ^ 2).degree = 2 := by compute_degree!
    exact h2 ▸  h1.trans_lt Nat.one_lt_ofNat
  · have h1 : (C a + C c * X + C e * X ^ 2).degree = 2 := by compute_degree!
    have h2 : (C a + C c * X + C e * X ^ 2).leadingCoeff = e := by
      rw [← coeff_natDegree, natDegree_eq_of_degree_eq_some h1]
      compute_degree!
    have h3 : (C b + C d * X + C f * X ^ 2).degree = 2 := by compute_degree!
    have h4 : (C b + C d * X + C f * X ^ 2).leadingCoeff = f := by
      rw [← coeff_natDegree, natDegree_eq_of_degree_eq_some h3]
      compute_degree!
    nth_rw 2 [← h2, ← h4]
    apply Polynomial.div_tendsto_leadingCoeff_div_of_degree_eq
    rw [h1, h3]

open Set Filter in
theorem tendsto_add_mul_sq_div_add_mul_atTop_nhds {𝕜 : Type*}
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] (a b c d e : 𝕜) {f : 𝕜} (hf : f ≠ 0) :
    Tendsto
      (fun k : 𝕜 ↦ (a + c * k + e * k ^ 2) / (b + d * k +  f * k ^ 2)) atTop (nhds (e / f)) := by
  apply Filter.Tendsto.congr'
  case f₁ => exact fun k ↦ (a * (↑k ^ 2)⁻¹ + c * ↑k⁻¹ + e) / (b * (↑k ^ 2)⁻¹ + d * ↑k⁻¹ + f)
  · refine (eventually_ne_atTop 0).mp (Eventually.of_forall ?_)
    intro x hx
    simp only
    rw [← mul_div_mul_left _ _ (pow_ne_zero 2 hx)]
    congrm ?_ / ?_
    · field_simp
      ring
    · field_simp
      ring
  · apply Filter.Tendsto.div _ _ hf
    all_goals
      apply zero_add (_ : 𝕜) ▸ Filter.Tendsto.add_const  _ _
      apply zero_add (_ : 𝕜) ▸ Filter.Tendsto.add _ _
      · apply mul_zero (_ : 𝕜) ▸ Filter.Tendsto.const_mul _ _
        exact (Filter.tendsto_pow_atTop two_ne_zero).inv_tendsto_atTop
      · apply mul_zero (_ : 𝕜) ▸ Filter.Tendsto.const_mul _ _
        exact tendsto_inv_atTop_zero

/-- As we approach infinite norm the inverse of hte stereographic projection `stereographic`
  approaches the center of the projection. -/
/- **Comment**: Again, this proof is a basic convergence proof. -/
lemma stereographic_symm_tendsto {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {v : E}
    (hv : ‖v‖ = 1) (α : Filter (↥(Submodule.span ℝ {v})ᗮ))
    (h : Filter.Tendsto norm α Filter.atTop) :
    Filter.Tendsto (stereographic hv).symm α (nhds ⟨v, by simp [hv]⟩) := by
  simp only [stereographic, PartialHomeomorph.mk_coe_symm, PartialEquiv.coe_symm_mk]
  rw [nhds_subtype, Filter.tendsto_comap_iff]
  have : Subtype.val ∘ (stereoInvFun hv) = fun (w : ↥(Submodule.span ℝ {v})ᗮ) ↦
      (4 * (‖w‖ ^ 2 + 4)⁻¹) • w + ((‖w‖ ^ 2 - 4) * (‖w‖ ^ 2 + 4)⁻¹) • v := by
    ext w
    simp only [Function.comp_apply, stereoInvFun_apply, AddSubgroupClass.coe_norm, smul_add,
      smul_smul]
    ring_nf
  simp_rw [this, AddSubgroupClass.coe_norm]
  nth_rw 8 [← zero_add (a := v)]
  apply Filter.Tendsto.add
  · rw [← comap_norm_nhds_zero, Filter.tendsto_comap_iff]
    have : (norm ∘ fun (x : ↥(Submodule.span ℝ {v})ᗮ) ↦ (4 * (‖(x : E)‖ ^ 2 + 4)⁻¹) • (x : E)) =
        (fun x ↦ 4 * x * (x ^ 2 + 4)⁻¹) ∘ (norm : ↥(Submodule.span ℝ {v})ᗮ → ℝ) := by
      ext x
      simp only [AddSubgroupClass.coe_norm, Function.comp_apply, norm_smul, norm_mul,
        Real.norm_ofNat, norm_inv, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (sq_nonneg ‖(x : E)‖) zero_le_four)]
      ring
    rw [this]
    refine Filter.Tendsto.comp ?_ h
    simp_rw [← div_eq_mul_inv]
    simpa [add_comm] using tendsto_add_mul_sq_div_add_mul_atTop_nhds (0 : ℝ) 4 4 0 0 one_ne_zero
  · nth_rw 6 [← one_smul (M := ℝ) (b := v)]
    apply Filter.Tendsto.smul_const
    change Filter.Tendsto ((fun y ↦ (y ^ 2 - 4) * (y ^ 2 + 4)⁻¹) ∘ norm) α (nhds 1)
    refine Filter.Tendsto.comp ?_ h
    simp_rw [← div_eq_mul_inv]
    simpa [add_comm, ← sub_eq_add_neg] using
      tendsto_add_mul_sq_div_add_mul_atTop_nhds (-4 : ℝ) 4 0 0 1 one_ne_zero

/-- As we approach infinite norm the inverse of the stereographic projection `stereographic'`
  approaches the centre of the projection. -/
lemma stereographic'_symm_tendsto {n : ℕ} (α : Filter (EuclideanSpace ℝ (Fin n)))
    (h : Filter.Tendsto norm α Filter.atTop) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := {
      out := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1)}
    Filter.Tendsto (stereographic' (E := EuclideanSpace ℝ (Fin (n + 1))) n
    ⟨EuclideanSpace.single (Fin.last n) 1, by simp⟩).symm α
    (nhds ⟨EuclideanSpace.single (Fin.last n) 1, by simp⟩) := by
  simp only [stereographic', Real.norm_eq_abs, PartialHomeomorph.coe_trans_symm,
    Homeomorph.toPartialHomeomorph_symm_apply, LinearIsometryEquiv.toHomeomorph_symm,
    LinearIsometryEquiv.coe_toHomeomorph, ← Filter.tendsto_map'_iff]
  apply stereographic_symm_tendsto
  rw [Filter.tendsto_map'_iff]
  convert h
  ext
  simp

/-! # Scaling to a different norm-/

/-**Comment**:
  The domains of the characterstic maps of a CW-complex (in our definition) are cubes in
  `Fin n → ℝ` (with the `∞`-metric).
  But the most convenient characteristic maps for spheres have closed balls in
  `EuclideanSpace ℝ (Fin n)` as their domain.
  We therefore need a map from cubes to closed balls.
  We define this map in a little more generality. -/


/-- This is just a preliminary lemma showing the continuity of the map we are about to define. -/
lemma continuous_normScale {E F : Type*}  [SeminormedAddCommGroup E] [T1Space E]
    [NormedAddCommGroup F] [MulActionWithZero ℝ F]
    {f : E → F} (hf : Continuous f) [ContinuousSMul ℝ F] [NormSMulClass ℝ F]
    (hf0 : ∀ x, f x = 0 ↔ x = 0) :
    Continuous fun x ↦ (‖x‖ * ‖f x‖⁻¹) • (f x) := by
  rw [continuous_iff_continuousOn_univ, ← diff_union_of_subset (subset_univ {0})]
  rw [(compl_eq_univ_diff {0}).symm]
  apply ContinuousOn.union_continuousAt
  · rw [isOpen_compl_iff]
    exact isClosed_singleton
  · apply ContinuousOn.smul
    · apply continuous_norm.continuousOn.mul
      apply ContinuousOn.inv₀
      · exact (continuous_norm.comp hf).continuousOn
      · intros
        simp_all
    · exact hf.continuousOn
  · intro x hx
    rw [mem_singleton_iff] at hx
    subst x
    simp only [ContinuousAt, norm_zero, zero_mul, zero_smul]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_smul, norm_mul, norm_inv, norm_norm, mul_assoc]
    have : (fun x ↦ ‖x‖ * (‖f x‖⁻¹ * ‖f x‖)) = fun x ↦ ‖x‖ := by
      ext x
      by_cases h : x = 0
      · simp [h]
      · have hfx : ‖f x‖ ≠ 0 := by
          intro s
          simp_all
        rw [inv_mul_cancel₀ hfx, mul_one]
    rw [this, ← norm_zero (E := E)]
    exact continuous_norm.continuousAt

/-- A homeomorphism from one normed group to another that preserves norms and the zero. -/
/- **Comment**:
  Unfortunatly this does not preserve distances so this is not an isometry
  (in fact such an isometry generally does not exist). -/
def normScale {E F : Type*}  [NormedAddCommGroup E] [T1Space E] [Module ℝ E]
    [ContinuousSMul ℝ E] [NormSMulClass ℝ E] [NormedAddCommGroup F] [Module ℝ F] [T1Space F]
    [ContinuousSMul ℝ F] [NormSMulClass ℝ F] (f : E ≃L[ℝ] F) : E ≃ₜ F where
  toFun x := (‖x‖ * ‖f x‖⁻¹) • (f x)
  invFun y := (‖y‖ * ‖f.symm y‖⁻¹) • (f.symm y)
  left_inv x := by
    by_cases h : x = 0
    · simp only [h, norm_zero, zero_mul, zero_smul]
    · simp only [norm_smul, norm_mul, norm_norm, norm_inv, map_smul,
        ContinuousLinearEquiv.symm_apply_apply, mul_inv_rev, inv_inv, smul_smul]
      suffices ‖x‖ * ‖f x‖⁻¹ * ‖f x‖ * (‖x‖⁻¹ * (‖f x‖ * ‖x‖⁻¹)) * (‖x‖ * ‖f x‖⁻¹) = 1 by
        rw [this, one_smul]
      have h1 : ‖x‖ ≠ 0 := by
        intro hx
        apply h
        exact norm_eq_zero.mp hx
      have h2 : ‖f x‖ ≠ 0 := by
        intro hx
        apply h
        simp_all only [ne_eq, norm_eq_zero, not_false_eq_true, EmbeddingLike.map_eq_zero_iff]
      field_simp [h1, h2]
      ring
  right_inv y := by
    by_cases h : y = 0
    · simp only [h, norm_zero, map_zero, inv_zero, mul_zero, smul_zero]
    · simp only [norm_smul, norm_mul, norm_norm, norm_inv, map_smul,
        ContinuousLinearEquiv.apply_symm_apply, mul_inv_rev, inv_inv, smul_smul]
      suffices ‖y‖ * ‖f.symm y‖⁻¹ * ‖f.symm y‖ *
          (‖y‖⁻¹ * (‖f.symm y‖ * ‖y‖⁻¹)) * (‖y‖ * ‖f.symm y‖⁻¹) = 1 by
        rw [this, one_smul]
      have h1 : ‖y‖ ≠ 0 := by
        intro hy
        apply h
        exact norm_eq_zero.mp hy
      have h2 : ‖f.symm y‖ ≠ 0 := by
        intro hy
        apply h
        simp_all only [ne_eq, norm_eq_zero, not_false_eq_true, EmbeddingLike.map_eq_zero_iff]
      field_simp [h1, h2]
      ring
  continuous_toFun := continuous_normScale f.continuous (fun _ ↦ f.map_eq_zero_iff)
  continuous_invFun := continuous_normScale f.symm.continuous (fun _ ↦ f.symm.map_eq_zero_iff)

/-- `normScale` preserves the zero. -/
@[simp]
lemma normScale_zero {E F : Type*}  [NormedAddCommGroup E] [T1Space E] [Module ℝ E]
    [ContinuousSMul ℝ E] [NormSMulClass ℝ E] [NormedAddCommGroup F] [Module ℝ F] [T1Space F]
    [ContinuousSMul ℝ F] [NormSMulClass ℝ F] (f : E ≃L[ℝ] F) :
    normScale f 0 = 0 := by
  simp [normScale]

/-- `normScale` is norm-preserving. -/
@[simp]
lemma norm_normScale {E F : Type*}  [NormedAddCommGroup E] [T1Space E] [Module ℝ E]
    [ContinuousSMul ℝ E] [NormSMulClass ℝ E] [NormedAddCommGroup F] [Module ℝ F] [T1Space F]
    [ContinuousSMul ℝ F] [NormSMulClass ℝ F] (f : E ≃L[ℝ] F) {x : E} : ‖normScale f x‖ = ‖x‖ := by
  simp [normScale, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, norm_smul, norm_mul,
    Real.norm_eq_abs, abs_norm, norm_inv, mul_assoc]
  by_cases h : x = 0
  · simp [h]
  · have hfx : ‖f x‖ ≠ 0 := by
      intro s
      simp_all
    rw [inv_mul_cancel₀ hfx, mul_one]

/-- The inverse of `normScale` of the continuous linear bijection `f` is just
  `normScale` of the inverse of `f`. -/
lemma normScale_symm_eq {E F : Type*}  [NormedAddCommGroup E] [T1Space E] [Module ℝ E]
    [ContinuousSMul ℝ E] [NormSMulClass ℝ E] [NormedAddCommGroup F] [Module ℝ F] [T1Space F]
    [ContinuousSMul ℝ F] [NormSMulClass ℝ F] (f : E ≃L[ℝ] F) :
    (normScale f).symm = normScale f.symm := by
  ext
  simp [normScale]

/-- `normScale` preserves closed balls. -/
@[simp]
lemma normScale_image_closedBall {E F : Type*}  [NormedAddCommGroup E] [T1Space E] [Module ℝ E]
    [ContinuousSMul ℝ E] [NormSMulClass ℝ E] [NormedAddCommGroup F] [Module ℝ F] [T1Space F]
    [ContinuousSMul ℝ F] [NormSMulClass ℝ F] (f : E ≃L[ℝ] F) (r : ℝ) :
    normScale f '' closedBall 0 r = closedBall 0 r := by
  ext x
  simp only [mem_image, mem_closedBall, dist_zero_right]
  constructor
  · intro ⟨y, hy1, hy2⟩
    rw [← hy2]
    rw [norm_normScale]
    exact hy1
  · intro hx
    use (normScale f).symm x
    rw [Homeomorph.apply_symm_apply, normScale_symm_eq, norm_normScale]
    exact ⟨hx, rfl⟩

/-- `normScale` preserves balls. -/
@[simp]
lemma normScale_image_ball {E F : Type*}  [NormedAddCommGroup E] [T1Space E] [Module ℝ E]
    [ContinuousSMul ℝ E] [NormSMulClass ℝ E] [NormedAddCommGroup F] [Module ℝ F] [T1Space F]
    [ContinuousSMul ℝ F] [NormSMulClass ℝ F] (f : E ≃L[ℝ] F) (r : ℝ) :
    normScale f '' ball 0 r = ball 0 r := by
  ext x
  simp only [mem_image, mem_ball, dist_zero_right]
  constructor
  · intro ⟨y, hy1, hy2⟩
    rw [← hy2]
    rw [norm_normScale]
    exact hy1
  · intro hx
    use (normScale f).symm x
    rw [Homeomorph.apply_symm_apply, normScale_symm_eq, norm_normScale]
    exact ⟨hx, rfl⟩

/-- `normScale` preserves spheres. -/
@[simp]
lemma normScale_image_sphere {E F : Type*}  [NormedAddCommGroup E] [T1Space E] [Module ℝ E]
    [ContinuousSMul ℝ E] [NormSMulClass ℝ E] [NormedAddCommGroup F] [Module ℝ F] [T1Space F]
    [ContinuousSMul ℝ F] [NormSMulClass ℝ F] (f : E ≃L[ℝ] F) (r : ℝ) :
    normScale f '' sphere 0 r = sphere 0 r := by
  ext x
  simp only [mem_image, mem_sphere, dist_zero_right]
  constructor
  · intro ⟨y, hy1, hy2⟩
    rw [← hy2]
    rw [norm_normScale]
    exact hy1
  · intro hx
    use (normScale f).symm x
    rw [Homeomorph.apply_symm_apply, normScale_symm_eq, norm_normScale]
    exact ⟨hx, rfl⟩

/-- An specification of `normScale` that scales between the `∞`- and the euclidean metric. -/
def toEuclideanNormScale (n : ℕ) : (Fin n → ℝ) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (normScale (toEuclidean (E := Fin n → ℝ))).trans
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (Module.finrank_fin_fun ℝ))).toHomeomorph

/-- `toEuclideanNormScale` preserves the zero. -/
@[simp]
lemma toEuclideanNormScale_zero (n : ℕ) : toEuclideanNormScale n 0 = 0 := by
  simp [toEuclideanNormScale, map_zero]

/-- `toEuclideanNormScale` is norm-preserving. -/
@[simp]
lemma norm_toEuclideanNormScale (n : ℕ) (x : Fin n → ℝ) : ‖toEuclideanNormScale n x‖ = ‖x‖ := by
  simp only [toEuclideanNormScale, Homeomorph.trans_apply, LinearIsometryEquiv.coe_toHomeomorph,
    LinearIsometryEquiv.norm_map, norm_normScale]

/-- `toEuclideanNormScale` preserves closed balls. -/
@[simp]
lemma toEuclideanNormScale_image_closedBall (n : ℕ) (r : ℝ) :
    toEuclideanNormScale n '' closedBall 0 r = closedBall 0 r := by
  simp only [toEuclideanNormScale, Homeomorph.trans_apply, LinearIsometryEquiv.coe_toHomeomorph, ←
    image_image, normScale_image_closedBall, LinearIsometryEquiv.image_closedBall, map_zero]

/-- `toEuclideanNormScale` preserves balls. -/
@[simp]
lemma toEuclideanNormScale_image_ball (n : ℕ) (r : ℝ) :
    toEuclideanNormScale n '' ball 0 r = ball 0 r := by
  simp only [toEuclideanNormScale, Homeomorph.trans_apply, LinearIsometryEquiv.coe_toHomeomorph, ←
    image_image, normScale_image_ball, LinearIsometryEquiv.image_ball, map_zero]

/-- `toEuclideanNormScale` preserves spheres. -/
@[simp]
lemma toEuclideanNormScale_image_sphere (n : ℕ) (r : ℝ) :
    toEuclideanNormScale n '' sphere 0 r = sphere 0 r := by
  simp only [toEuclideanNormScale, Homeomorph.trans_apply, LinearIsometryEquiv.coe_toHomeomorph, ←
    image_image, normScale_image_sphere, LinearIsometryEquiv.image_sphere, map_zero]

/-! # A Homeomorphism that flips the last coordinate-/

/-**Comment**:
  For the inductive construction of the sphere we pricipally need two maps:
  One that maps from the closed ball in dimension `n` to the upper hemisphere of the sphere in
  dimension `n + 1`, and one that does the same for the lower hemisphere.
  In order to not define essentially the same map twice, we define a linear bijective isometry
  that reflects the space on the hyperplane where the last coordinate is zero. -/

/-- A specialized version of `LinearIsometryEquiv.reflection` reflecting
  `EuclideanSpace ℝ (Fin (n + 1))` on the hyperplane where the last coordinate is zero. -/
def LinearIsometryEquiv.negLast (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) where
  toFun x := Function.update x (Fin.last n) (-(x (Fin.last n)))
  map_add' x y := by
    ext i
    by_cases h : i = Fin.last n
    · subst i
      simp [add_comm]
    · unfold Function.update
      simp [h]
  map_smul' m x := by
    ext i
    by_cases h : i = Fin.last n
    · subst i
      simp [add_comm]
    · unfold Function.update
      simp [h]
  invFun y := Function.update y (Fin.last n) (-(y (Fin.last n)))
  left_inv x := by simp
  right_inv y := by simp
  norm_map' x := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_castSucc, fun i ↦ (Fin.castSucc_lt_last i).ne]

/-- `LinearIsometryEquiv.negLast` is idempotent. -/
@[simp]
lemma LinearIsometryEquiv.negLast_idempotent (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    negLast n (negLast n x) = x := by
  ext i
  unfold negLast Function.update
  by_cases h : i = Fin.last n
  · subst h
    simp
  · simp [h]

/-! # Openness/Closedness of the plane and half-planes-/

/- **Comment**:
  We need the closedness of the plane to show that the sphere in dimension `n` is still closed
  when embedded into dimension `n + 1`. -/

/-- The upper half-plane is open. -/
lemma isOpen_UpperHalfPlane (n : ℕ) :
    IsOpen {(x : EuclideanSpace ℝ (Fin (n + 1)) )| x (Fin.last n) > 0} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  simp_all only [gt_iff_lt, mem_setOf_eq]
  use ball x (x (Fin.last n))
  refine ⟨?_, isOpen_ball, mem_ball_self hx⟩
  intro y hy
  simp_all only [mem_ball, mem_setOf_eq]
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_castSucc, ← sq_lt_sq₀ (Real.sqrt_nonneg _) hx.le,
    Real.sq_sqrt (add_nonneg (Finset.sum_nonneg (fun i a ↦ sq_nonneg _)) (sq_nonneg _))] at hy
  have := lt_of_add_lt_of_nonneg_right hy (Finset.sum_nonneg (fun i a ↦ sq_nonneg _))
  rw [Real.dist_eq, sq_lt_sq₀ (abs_nonneg _) hx.le] at this
  replace this := sub_lt_of_abs_sub_lt_left this
  simp_all only [sub_self]

/-- The lower half plane is open. -/
lemma isOpen_LowerHalfPlane (n : ℕ) :
    IsOpen {(x : EuclideanSpace ℝ (Fin (n + 1)) )| x (Fin.last n) < 0} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  simp_all only [gt_iff_lt, mem_setOf_eq]
  use ball x |(x (Fin.last n))|
  refine ⟨?_, isOpen_ball, mem_ball_self (abs_pos_of_neg hx)⟩
  intro y hy
  simp_all only [mem_ball, mem_setOf_eq]
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_castSucc,
    ← sq_lt_sq₀ (Real.sqrt_nonneg _) (abs_nonneg _),
    Real.sq_sqrt (add_nonneg (Finset.sum_nonneg (fun i a ↦ sq_nonneg _)) (sq_nonneg _))] at hy
  have := lt_of_add_lt_of_nonneg_right hy (Finset.sum_nonneg (fun i a ↦ sq_nonneg _))
  rw [Real.dist_eq, sq_lt_sq₀ (abs_nonneg _) (abs_nonneg _), abs_sub_lt_iff] at this
  replace this := this.1
  simp_all [abs_of_neg hx, lt_neg_iff_add_neg]

/-- The hyperplane is closed. -/
lemma isClosed_plane (n : ℕ) :
    IsClosed {(x : EuclideanSpace ℝ (Fin (n + 1)) )| x (Fin.last n) = 0} := by
  rw [← isOpen_compl_iff, compl_setOf]
  simp_rw [ne_iff_lt_or_gt, setOf_or]
  exact (isOpen_LowerHalfPlane n).union (isOpen_UpperHalfPlane n)

/-! # Statements about `Fin.init`-/

/-**Comment**:
  We use `Fin.init` to construct the map `discToSphereUp` and therefore need some more information
  about it. -/

-- I am not sure where the next three would go

/-- The euclidean norm of `Fin.init` is less then or equal to the euclidean norm of the element. -/
lemma EuclideanSpace.norm_finInit_le {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (q : EuclideanSpace 𝕜 (Fin (n + 1))) :
    norm (Fin.init q : EuclideanSpace 𝕜 (Fin n)) (self := (PiLp.instNorm 2 fun _ ↦ 𝕜)) ≤ ‖q‖ := by
  simp_rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)), Fin.sum_univ_castSucc, Fin.init,
    le_add_iff_nonneg_right]
  exact sq_nonneg ‖q (Fin.last n)‖

/-- If the last coordinate of an element `q` is greater than zero in norm then the euclidean norm
  of `Fin.init q` is strictly less than the euclidean norm of `q`. -/
lemma EuclideanSpace.norm_finInit_lt {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (q : EuclideanSpace 𝕜 (Fin (n + 1))) (hq : ‖q (Fin.last n)‖ > 0):
    norm (Fin.init q : EuclideanSpace 𝕜 (Fin n)) (self := (PiLp.instNorm 2 fun _ ↦ 𝕜)) < ‖q‖ := by
  simp_rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)), Fin.sum_univ_castSucc, Fin.init,
    lt_add_iff_pos_right]
  exact sq_pos_of_pos hq

/-- The norm of `Fin.init` is less than or equal to the norm of the original element. -/
lemma Fin.norm_init_le {n : ℕ} {α : Type*} [SeminormedAddGroup α] (q : (Fin (n + 1)) → α) :
    ‖Fin.init q‖ ≤ ‖q‖ := by
  simp only [Pi.norm_def, NNReal.coe_le_coe, Finset.sup_le_iff, Finset.mem_univ, forall_const]
  intro b
  exact Finset.le_sup (Finset.mem_univ b.castSucc) (f := fun x ↦ ‖q x‖₊)

/-! # Embedding the euclidean space of dimension `n` into dimension `n + 1` -/

/-**Comment**:
  We need this to embed the sphere in dimension `n` into the space of dimension `n + 1` while
  maintaining that it is a CW-complex. -/

/-- A partial bijection between `EuclideanSpace ℝ (Fin n)` and the hyperplane with last
  coordinate zero in `EuclideanSpace ℝ (Fin (n + 1))`. -/
@[simps!]
def PartialEquiv.EuclideanSpaceSucc (n : ℕ) :
    PartialEquiv (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin (n + 1))) where
  toFun x := Fin.snoc x 0
  invFun := Fin.init
  source := univ
  target := {y | y (Fin.last n) = 0}
  map_source' := by simp
  map_target' := by simp
  left_inv' x _ := by simp
  right_inv' y hy := by
    simp_all only [mem_setOf_eq]
    rw [← hy]
    exact Fin.snoc_init_self _

/-- `PartialEquiv.EuclideanSpaceSucc` is continuous. -/
lemma PartialEquiv.continuous_EuclideanSpaceSucc (n : ℕ) :
    Continuous (EuclideanSpaceSucc n) := by
  simp only [EuclideanSpaceSucc]
  apply Continuous.finSnoc
  · exact continuous_id'
  · exact continuous_const

/-- The inverse of `PartialEquiv.EuclideanSpaceSucc` is continuous. -/
lemma PartialEquiv.continuous_EuclideanSpaceSucc_symm (n : ℕ) :
    Continuous (EuclideanSpaceSucc n).symm := by
  simp only [EuclideanSpaceSucc, PartialEquiv.coe_symm_mk]
  exact Continuous.finInit continuous_id'

/-- The image of the sphere under `PartialEquiv.EuclideanSpaceSucc` is the sphere intersected
  with the hyperplane with last coordinate zero. -/
lemma PartialEquiv.EuclideanSpaceSucc_image_sphere (n : ℕ) :
    EuclideanSpaceSucc n '' sphere 0 1 = sphere 0 1 ∩ {x | x (Fin.last n) = 0} := by
  ext x
  constructor
  · simp only [mem_image, mem_sphere_iff_norm, sub_zero, mem_inter_iff, mem_setOf_eq,
    forall_exists_index, and_imp]
    intro y hy hyx
    constructor
    · rw [EuclideanSpace.norm_eq, Fin.sum_univ_castSucc, ← hyx]
      simp only [EuclideanSpaceSucc_apply, Fin.snoc_castSucc, Fin.snoc_last,
        Real.norm_eq_abs (r := 0), sq_abs, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        add_zero]
      rw [← EuclideanSpace.norm_eq, hy]
    · rw [← hyx]
      simp
  · simp only [mem_inter_iff, mem_sphere_iff_norm, sub_zero, mem_setOf_eq, mem_image, and_imp]
    intro hx hx0
    use Fin.init x
    constructor
    · rw [EuclideanSpace.norm_eq, Fin.sum_univ_castSucc, hx0] at hx
      simp only [Real.norm_eq_abs (r := 0), sq_abs, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, add_zero] at hx
      rw [EuclideanSpace.norm_eq]
      simp only [Fin.init]
      exact hx
    · simp only [EuclideanSpaceSucc]
      rw [← hx0]
      exact Fin.snoc_init_self _

/-! # Isometry between different metrics on ℝ-/

/- **Comment**:
  We need this to show that the sphere in the euclidean space of dimension one is a CW-complex. -/

/-- The isometry between the euclidean and the `∞`-metric on `ℝ`. -/
def EuclideanFunUnique (n 𝕜 : Type*) [RCLike 𝕜] [Unique n] [Fintype n] :
    EuclideanSpace 𝕜 n ≃ᵢ (n → 𝕜) where
  toFun := id
  invFun := id
  left_inv := by intro; rfl
  right_inv := by intro; rfl
  isometry_toFun := by
    intro x y
    simp [edist_pi_def, EuclideanSpace.edist_eq, ← ENNReal.rpow_natCast_mul]

/-- The isometry between the euclidean and the usual metric on `ℝ`. -/
def EuclideanUnique (𝕜 n : Type*) [RCLike 𝕜] [Unique n] [Fintype n] : EuclideanSpace 𝕜 n ≃ᵢ 𝕜 :=
  (EuclideanFunUnique n 𝕜).trans (IsometryEquiv.funUnique n 𝕜)
