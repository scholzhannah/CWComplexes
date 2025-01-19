import CWcomplexes.Relative.Examples
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

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

def EuclideanFunUnique (n 𝕜 : Type*) [RCLike 𝕜] [Unique n] [Fintype n] :
    EuclideanSpace 𝕜 n ≃ᵢ (n → 𝕜) where
  toFun := id
  invFun := id
  left_inv := by intro; rfl
  right_inv := by intro; rfl
  isometry_toFun := by
    intro x y
    simp [edist_pi_def, EuclideanSpace.edist_eq, ← ENNReal.rpow_natCast_mul]

def EuclideanUnique (𝕜 n : Type*) [RCLike 𝕜] [Unique n] [Fintype n] : EuclideanSpace 𝕜 n ≃ᵢ 𝕜 :=
  (EuclideanFunUnique n 𝕜).trans (IsometryEquiv.funUnique n 𝕜)

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

lemma Homeomorph.tendsto_norm_comp_unitBall_symm {E : Type u_1} [NormedAddCommGroup E]
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

lemma stereographic'_symm_tendsto {n : ℕ} (α : Filter (EuclideanSpace ℝ (Fin n)))
    (h : Filter.Tendsto norm α Filter.atTop) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := {
      out := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1)}
    Filter.Tendsto (stereographic' (E := EuclideanSpace ℝ (Fin (n + 1))) n
    ⟨EuclideanSpace.single (Fin.last n) 1, by simp⟩).symm α
    (nhds ⟨EuclideanSpace.single (Fin.last n) 1, by simp⟩) := by
  simp [stereographic']
  rw [← Filter.tendsto_map'_iff]
  apply stereographic_symm_tendsto
  rw [Filter.tendsto_map'_iff]
  convert h
  ext
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

@[simp]
lemma normScale_zero {E F : Type*}  [NormedAddCommGroup E] [T1Space E] [Module ℝ E]
    [ContinuousSMul ℝ E] [BoundedSMul ℝ E] [NormedAddCommGroup F] [Module ℝ F] [T1Space F]
    [ContinuousSMul ℝ F] [BoundedSMul ℝ F] (f : E ≃L[ℝ] F) :
    normScale f 0 = 0 := by
  simp [normScale]

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

lemma normScale_symm_eq {E F : Type*}  [NormedAddCommGroup E] [T1Space E] [Module ℝ E]
    [ContinuousSMul ℝ E] [BoundedSMul ℝ E] [NormedAddCommGroup F] [Module ℝ F] [T1Space F]
    [ContinuousSMul ℝ F] [BoundedSMul ℝ F] (f : E ≃L[ℝ] F) :
    (normScale f).symm = normScale f.symm := by
  ext
  simp [normScale]

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

def toEuclideanNormScale (n : ℕ) : (Fin n → ℝ) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (normScale (toEuclidean (E := Fin n → ℝ))).trans
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (Module.finrank_fin_fun ℝ))).toHomeomorph

@[simp]
lemma toEuclideanNormScale_zero (n : ℕ) : toEuclideanNormScale n 0 = 0 := by
  simp [toEuclideanNormScale, map_zero]

@[simp]
lemma norm_toEuclideanNormScale (n : ℕ) (x : Fin n → ℝ) : ‖toEuclideanNormScale n x‖ = ‖x‖ := by
  simp only [toEuclideanNormScale, Homeomorph.trans_apply, LinearIsometryEquiv.coe_toHomeomorph,
    LinearIsometryEquiv.norm_map, norm_normScale]

@[simp]
lemma toEuclideanNormScale_image_closedBall (n : ℕ) (r : ℝ) :
    toEuclideanNormScale n '' closedBall 0 r = closedBall 0 r := by
  simp only [toEuclideanNormScale, Homeomorph.trans_apply, LinearIsometryEquiv.coe_toHomeomorph, ←
    image_image, normScale_image_closedBall, LinearIsometryEquiv.image_closedBall, map_zero]

@[simp]
lemma toEuclideanNormScale_image_ball (n : ℕ) (r : ℝ) :
    toEuclideanNormScale n '' ball 0 r = ball 0 r := by
  simp only [toEuclideanNormScale, Homeomorph.trans_apply, LinearIsometryEquiv.coe_toHomeomorph, ←
    image_image, normScale_image_ball, LinearIsometryEquiv.image_ball, map_zero]

@[simp]
lemma toEuclideanNormScale_image_sphere (n : ℕ) (r : ℝ) :
    toEuclideanNormScale n '' sphere 0 r = sphere 0 r := by
  simp only [toEuclideanNormScale, Homeomorph.trans_apply, LinearIsometryEquiv.coe_toHomeomorph, ←
    image_image, normScale_image_sphere, LinearIsometryEquiv.image_sphere, map_zero]

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

instance instSphere {n : ℕ} : ClasCWComplex (sphere 0 1 : Set (EuclideanSpace ℝ (Fin n))) :=
  match n with
  | 0 => SphereZero 0 1 one_ne_zero
  | 1 => SphereOneEuclidean 1 0 zero_le_one
  | (n + 2) => instSphereGT (n + 1) n.zero_lt_succ

instance Finite_instSphere {n : ℕ} : Finite (sphere 0 1 : Set (EuclideanSpace ℝ (Fin n))) :=
  match n with
  | 0 => Finite_SphereZero 0 1 one_ne_zero
  | 1 => Finite_SphereOneEuclidean 1 0 zero_le_one
  | (n + 2) => Finite_instSphereGT (n + 1) n.zero_lt_succ

example : ClasCWComplex
    (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 ×ˢ sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
  inferInstance

end ClasCWComplex
