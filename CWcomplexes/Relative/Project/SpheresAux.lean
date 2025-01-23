import CWcomplexes.Relative.Project.Examples
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Auxiliary Lemmas and Constructions for the CW-complex structures on spheres
-/

noncomputable section

open Metric Set

/-! # Lemmas needed for the continuity of `sphereToDisc` on the sphere. -/

/- The map `sphereToDisc` is made up of (the inverses of) two maps:
  `Homeomorph.unitBall` and `stereographic'`. On the sphere these maps are not defined.
  We define `sphereToDisc` to map the sphere to the relevant unit vector.
  In order to show that ``sphereToDisc` is continuous on the sphere we need to study how
  (the inverses of) `Homeomorph.unitBall` and `stereographic'` behave as we approach the edge of
  their domain.-/

/-- As we approach the sphere from inside the ball the inverse of `Homeomorph.unitBall` tends to
  infinity in its norm.-/
/- The proof of this statement just unnfolds the definition of `Homeomorph.unitBall` and then
  applies basic facts about convergence.-/
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
  rw [← Function.comp_assoc, ← Filter.tendsto_map'_iff, Filter.subtype_coe_map_comap]
  simp only [PartialHomeomorph.univUnitBall, PartialHomeomorph.mk_coe_symm,
    PartialEquiv.coe_symm_mk]
  have : norm ∘ (fun y ↦ (√(1 - ‖y‖ ^ 2))⁻¹ • y)
      = (fun r ↦ (√(1 - r ^ 2))⁻¹ * r) ∘ (norm : E → ℝ) := by
    ext y
    simp only [Function.comp_apply, norm_smul, norm_inv, Real.norm_eq_abs, mul_eq_mul_right_iff,
      inv_inj, abs_eq_self, Real.sqrt_nonneg, norm_eq_zero, true_or]
  rw [this]
  apply Filter.Tendsto.comp (y := nhdsWithin 1 (Ico 0 1))
  · apply Filter.Tendsto.atTop_mul Real.zero_lt_one
    · apply Filter.Tendsto.comp (y := nhdsWithin 0 (Set.Ioi 0))
      · exact tendsto_inv_nhdsGT_zero
      · refine Filter.Tendsto.mono_right (y := (nhdsWithin 0 (Ioc 0 1))) ?_
          (nhdsWithin_mono 0 Ioc_subset_Ioi_self)
        have h1 : 0 = (fun x ↦ √(1 - x ^ 2)) 1 := by simp
        have h2 : Ioc 0 1 = (fun x ↦ √(1 - x ^ 2)) '' (Ico 0 1) := by
          ext y
          simp only [mem_Ioc, mem_image, mem_Ioo]
          constructor
          · intro ⟨hy1, hy2⟩
            use √(1 - y ^ 2)
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · exact Real.sqrt_nonneg (1 - y ^ 2)
            · rw [← Real.sqrt_one]
              apply Real.sqrt_lt_sqrt
              · rw [sub_nonneg, Real.sqrt_one, (by norm_num : (1 : ℝ) = 1 ^ 2), sq_le_sq]
                simp only [abs_one, abs_le, (lt_trans neg_one_lt_zero hy1).le, hy2, and_self]
              · rw [Real.sqrt_one]
                apply sub_lt_self
                exact sq_pos_of_pos hy1
            · suffices √(1 - y ^ 2) ^ 2 = 1 - y ^ 2 by
                rw [this, sub_sub_cancel, Real.sqrt_sq hy1.le]
              apply Real.sq_sqrt
              rw [sub_nonneg, (by norm_num : (1 : ℝ) = 1 ^ 2), sq_le_sq]
              simp only [abs_one, abs_le, (lt_trans neg_one_lt_zero hy1).le, hy2, and_self]
          · intro ⟨z, ⟨hz1, hz2⟩, hz3⟩
            rw [← hz3]
            constructor
            · rw [Real.sqrt_pos, sub_pos, sq_lt_one_iff_abs_lt_one, abs_lt]
              exact ⟨lt_of_lt_of_le neg_one_lt_zero hz1, hz2⟩
            · rw [Real.sqrt_le_iff, one_pow]
              refine ⟨zero_le_one, ?_⟩
              apply sub_le_self
              exact sq_nonneg z
        nth_rw 2 [h1]
        nth_rw 1 [h2]
        apply ContinuousWithinAt.tendsto_nhdsWithin_image
        apply Continuous.continuousWithinAt
        apply Real.continuous_sqrt.comp
        exact (continuous_sub_left 1).comp (continuous_pow 2)
    · refine Filter.Tendsto.mono_left (x := nhds 1) ?_ nhdsWithin_le_nhds
      apply ContinuousAt.tendsto
      exact continuous_id.continuousAt
  · have h1 : Ico 0 1 = norm '' ball (0 : E) 1 := by
      ext y
      simp only [mem_Ioo, mem_image, mem_ball, dist_zero_right]
      constructor
      · intro ⟨hy1, hy2⟩
        rcases NormedSpace.exists_lt_norm ℝ E 0 with ⟨r, hr⟩
        use (y / ‖r‖) • r
        suffices ‖(y / ‖r‖) • r‖ = y by simp [this, hy2]
        simp [norm_smul, div_mul_cancel₀ _ hr.ne.symm, hy1]
      · intro ⟨z, hz1, hz2⟩
        rw [← hz2]
        simp only [mem_Ico, norm_nonneg, hz1, and_self]
    have : 1 = ‖x‖ := by simp_all only [mem_sphere_iff_norm, sub_zero]
    rw [h1, this]
    apply ContinuousWithinAt.tendsto_nhdsWithin_image
    exact continuous_norm.continuousWithinAt

/-- As we approach infinite norm the inverse of hte stereographic projection `stereographic`
  approaches the center of the projection. -/
/- Again, this proof is a basic convergence proof. -/
lemma stereographic_symm_tendsto {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {v : E}
    (hv : ‖v‖ = 1) (α : Filter (↥(Submodule.span ℝ {v})ᗮ))
    (h : Filter.Tendsto norm α Filter.atTop) :
    Filter.Tendsto (stereographic hv).symm α (nhds ⟨v, by simp [hv]⟩) := by
  simp only [stereographic, PartialHomeomorph.mk_coe_symm, PartialEquiv.coe_symm_mk]
  rw [nhds_subtype, Filter.tendsto_comap_iff]
  have : Subtype.val ∘ (stereoInvFun hv) =
      fun (w : ↥(Submodule.span ℝ {v})ᗮ) ↦
      (4 * (‖w‖ ^ 2 + 4)⁻¹) • w + ((‖w‖ ^ 2 - 4) * (‖w‖ ^ 2 + 4)⁻¹) • v := by
    ext w
    simp only [Function.comp_apply, stereoInvFun_apply, AddSubgroupClass.coe_norm, smul_add,
      smul_smul]
    ring_nf
  rw [this]
  simp only [AddSubgroupClass.coe_norm]
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
    rw [← mul_zero (a := 4)]
    simp_rw [mul_assoc]
    apply Filter.Tendsto.const_mul
    have : (fun (k : ℝ) ↦ k * (k ^ 2 + 4)⁻¹) = fun k ↦ (k + 4 * k⁻¹)⁻¹ := by
      ext k
      nth_rw 1 [← inv_inv (a := k), ← mul_inv, mul_add, pow_two, ← mul_assoc, inv_mul_mul_self,
        mul_comm]
    rw [this]
    apply Filter.Tendsto.inv_tendsto_atTop
    apply Filter.Tendsto.atTop_add (C := 0) (fun _ a ↦ a)
    change Filter.Tendsto (fun x ↦ 4 * x⁻¹) Filter.atTop (nhds 0)
    rw [← mul_zero (a := 4)]
    apply Filter.Tendsto.const_mul
    exact tendsto_inv_atTop_zero
  · nth_rw 6 [← one_smul (M := ℝ) (b := v)]
    apply Filter.Tendsto.smul_const
    have : (fun (x : ↥(Submodule.span ℝ {v})ᗮ) ↦ (‖(x : E)‖ ^ 2 - 4) * (‖(x : E)‖ ^ 2 + 4)⁻¹) =
        (fun y ↦ (y ^ 2 - 4) * (y ^ 2 + 4)⁻¹) ∘ (norm : ↥(Submodule.span ℝ {v})ᗮ → ℝ) := by
      ext
      simp
    rw [this]
    refine Filter.Tendsto.comp ?_ h
    have : (fun (y : ℝ) ↦ (y ^ 2 - 4) * (y ^ 2 + 4)⁻¹) = fun y ↦ 1 + -8 * (y ^ 2 + 4)⁻¹ := by
      ext y
      field_simp
      rw [sub_eq_add_neg, add_assoc]
      norm_num
    rw [this]
    nth_rw 2 [← add_zero (a := 1)]
    apply Filter.Tendsto.const_add
    rw [← mul_zero (a := -8)]
    apply Filter.Tendsto.const_mul
    apply Filter.Tendsto.inv_tendsto_atTop
    apply Filter.tendsto_atTop_add_const_right
    exact Filter.tendsto_pow_atTop two_ne_zero

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
    LinearIsometryEquiv.coe_toHomeomorph]
  rw [← Filter.tendsto_map'_iff]
  apply stereographic_symm_tendsto
  rw [Filter.tendsto_map'_iff]
  convert h
  ext
  simp

/-! # Scaling to a different norm-/

/- The domain of the characterstic maps of a CW-complex (in our definition) are cubes in
  `Fin n → ℝ` (with the `∞`-metric).
  But the most convenient characteristic maps for spheres have closed balls in
  `EuclideanSpace ℝ (Fin n)` as their domain.
  We therefore need a map from cubes to closed balls.
  We define this map in a little more generality. -/


-- This is just a preliminary lemma showing the continuity of the map we are about to define.
lemma continuous_normScale {E F : Type*}  [SeminormedAddCommGroup E] [T1Space E]
    [NormedAddCommGroup F] [MulActionWithZero ℝ F]
    {f : E → F} (hf : Continuous f) [ContinuousSMul ℝ F] [BoundedSMul ℝ F]
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

/-- A homeomorphism from one normed group to another that preserves norms and the zero.-/
/- Unfortunatly this does not preserve distances so this is not an isometry
  (in fact such an isometry generally does not exist). -/
def normScale {E F : Type*}  [NormedAddCommGroup E] [T1Space E] [Module ℝ E]
    [ContinuousSMul ℝ E] [BoundedSMul ℝ E] [NormedAddCommGroup F] [Module ℝ F] [T1Space F]
    [ContinuousSMul ℝ F] [BoundedSMul ℝ F] (f : E ≃L[ℝ] F) : E ≃ₜ F where
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
    [ContinuousSMul ℝ E] [BoundedSMul ℝ E] [NormedAddCommGroup F] [Module ℝ F] [T1Space F]
    [ContinuousSMul ℝ F] [BoundedSMul ℝ F] (f : E ≃L[ℝ] F) :
    normScale f 0 = 0 := by
  simp [normScale]

/-- `normScale` is norm-preserving. -/
@[simp]
lemma norm_normScale {E F : Type*}  [NormedAddCommGroup E] [T1Space E] [Module ℝ E]
    [ContinuousSMul ℝ E] [BoundedSMul ℝ E] [NormedAddCommGroup F] [Module ℝ F] [T1Space F]
    [ContinuousSMul ℝ F] [BoundedSMul ℝ F] (f : E ≃L[ℝ] F) {x : E} : ‖normScale f x‖ = ‖x‖ := by
  simp only [normScale, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, norm_smul, norm_mul,
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
    [ContinuousSMul ℝ E] [BoundedSMul ℝ E] [NormedAddCommGroup F] [Module ℝ F] [T1Space F]
    [ContinuousSMul ℝ F] [BoundedSMul ℝ F] (f : E ≃L[ℝ] F) :
    (normScale f).symm = normScale f.symm := by
  ext
  simp [normScale]

/-- `normScale` preserves closed balls.-/
@[simp]
lemma normScale_image_closedBall {E F : Type*}  [NormedAddCommGroup E] [T1Space E] [Module ℝ E]
    [ContinuousSMul ℝ E] [BoundedSMul ℝ E] [NormedAddCommGroup F] [Module ℝ F] [T1Space F]
    [ContinuousSMul ℝ F] [BoundedSMul ℝ F] (f : E ≃L[ℝ] F) (r : ℝ) :
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
    [ContinuousSMul ℝ E] [BoundedSMul ℝ E] [NormedAddCommGroup F] [Module ℝ F] [T1Space F]
    [ContinuousSMul ℝ F] [BoundedSMul ℝ F] (f : E ≃L[ℝ] F) (r : ℝ) :
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
    [ContinuousSMul ℝ E] [BoundedSMul ℝ E] [NormedAddCommGroup F] [Module ℝ F] [T1Space F]
    [ContinuousSMul ℝ F] [BoundedSMul ℝ F] (f : E ≃L[ℝ] F) (r : ℝ) :
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

/- For the inductive construction of the sphere we pricipally need two maps:
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
  · simp only [eq_rec_constant, dite_eq_ite, coe_mk, LinearEquiv.coe_mk, h, ↓reduceIte, neg_neg]
    rw [← h]
  · simp [h]

/-! # Miscellaneous-/

/-- The isometry between the euclidean and the `∞`-metric on `ℝ`.-/
def EuclideanFunUnique (n 𝕜 : Type*) [RCLike 𝕜] [Unique n] [Fintype n] :
    EuclideanSpace 𝕜 n ≃ᵢ (n → 𝕜) where
  toFun := id
  invFun := id
  left_inv := by intro; rfl
  right_inv := by intro; rfl
  isometry_toFun := by
    intro x y
    simp [edist_pi_def, EuclideanSpace.edist_eq, ← ENNReal.rpow_natCast_mul]

/-- The isometry between the euclidean and the usual metric on `ℝ`.-/
def EuclideanUnique (𝕜 n : Type*) [RCLike 𝕜] [Unique n] [Fintype n] : EuclideanSpace 𝕜 n ≃ᵢ 𝕜 :=
  (EuclideanFunUnique n 𝕜).trans (IsometryEquiv.funUnique n 𝕜)

/-- `Fin.init` is continuous. -/
/- This still needs to be generalized. -/
lemma Continuous.finInit {n : ℕ} {α : Type*} [PseudoMetricSpace α] :
    Continuous (Fin.init : (Fin (n + 1) → α) → (Fin n → α)) := by
  rw [Metric.continuous_iff]
  intro b ε hε
  use ε, hε
  intro a hab
  suffices dist (Fin.init a) (Fin.init b) ≤ dist a b from lt_of_le_of_lt this hab
  simp only [dist_pi_def, Fin.init, NNReal.coe_le_coe, Finset.sup_le_iff, Finset.mem_univ,
    forall_const]
  intro c
  exact Finset.le_sup (Finset.mem_univ c.castSucc) (f := fun x ↦ nndist (a x) (b x))

/-- The euclidean norm of `Fin.init` is less then or equal to the euclidean norm of the element. -/
lemma EuclideanSpace.norm_finInit_le {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (q : EuclideanSpace 𝕜 (Fin (n + 1))) :
    norm (Fin.init q : EuclideanSpace 𝕜 (Fin n)) (self := (PiLp.instNorm 2 fun x ↦ 𝕜)) ≤ ‖q‖ := by
  simp_rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)), Fin.sum_univ_castSucc, Fin.init,
    le_add_iff_nonneg_right]
  exact sq_nonneg ‖q (Fin.last n)‖

/-- If the last coordinate of an element `q` is greater than zero in norm then the euclidean norm
  of `Fin.init q` is strictly less than the euclidean norm of `q`. -/
/- The hypthesis `hq` should be generalised. -/
lemma EuclideanSpace.norm_finInit_lt {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (q : EuclideanSpace 𝕜 (Fin (n + 1))) (hq : ‖q (Fin.last n)‖ > 0):
    norm (Fin.init q : EuclideanSpace 𝕜 (Fin n)) (self := (PiLp.instNorm 2 fun x ↦ 𝕜)) < ‖q‖ := by
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
