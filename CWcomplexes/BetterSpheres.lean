import CWcomplexes.SpheresAux

noncomputable section

open Metric Set

namespace Topology.CWComplex

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

abbrev Hyperplane (n m : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i (h1 : i ≥  m) (h2 : i < n), x ⟨i, by simp [h2]⟩ = 0}

@[simps]
def embedHyperplane (n m : ℕ) : PartialEquiv
    (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin (n + m))) where
  toFun x := Fin.append x (fun y ↦ 0)
  invFun y := Fin.take n (n.le_add_right m) y
  source := univ
  target := Hyperplane (n + m) n
  map_source' x hx := by
    intro i hi1 hi2
    simp [Fin.append, Fin.addCases, hi1]
  map_target' y hy := mem_univ _
  left_inv'  x _ := by simp [Fin.take_append_left _ n.le_refl]
  right_inv' y hy := by
    ext i
    by_cases hi : i < n
    · simp_all only [mem_setOf_eq, ge_iff_le, Fin.append, Fin.addCases, ↓reduceDIte,
        Fin.take_apply]
      rfl
    · simp_all [Fin.append, Fin.addCases]

/-- Not used anymore -/
lemma Fin.injective_append_right {n m : ℕ} {α : Sort*} (b : Fin n → α) :
    Function.Injective (fun x ↦ Fin.append (m := m) x b) := by
  intro a1 a2 ha
  ext x
  replace ha := funext_iff.1 ha (Fin.castAdd n x)
  simp_all

lemma injective_embedHyperplane (n m : ℕ) : Function.Injective (embedHyperplane n m) :=
  PartialEquiv.injective_of_source_eq_univ _ rfl

lemma embedHyperplane_image (n m : ℕ) (u : Set (EuclideanSpace ℝ (Fin n)))
    (v : Set (EuclideanSpace ℝ (Fin (n + m)))) :
  embedHyperplane n m '' u = v ∩ Hyperplane (n + m) n ↔
    (embedHyperplane n m).symm '' v = u := by
  constructor
  · intro h

    sorry
  · intro h
    rw [PartialEquiv.symm_image_eq_source_inter_preimage, embedHyperplane_source, univ_inter] at h
    ·
      rw [← h]

      sorry
    · sorry

@[simp]
def discToSphereEmbed (n m : ℕ) :
    PartialEquiv (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin ((n + 1) + m))) :=
  (discToSphereUp n).transEmbedding ((Fin.castAddEmb m).euclidean (𝕜 := ℝ))

@[simp]
lemma discToSphereEmbed_image_sphere (n m : ℕ) :
    (discToSphereEmbed n m) '' sphere 0 1 = (sphere 0 1) ∩ Hyperplane ((n + 1) + m) n  := by
  rw [discToSphereEmbed, PartialEquiv.coe_transEmbedding, Set.image_comp,
    discToSphereUp_image_sphere]
  apply subset_antisymm
  · apply subset_inter _
    · sorry
    · sorry
  · sorry


/-This is an attempt to already go up all the dimensions at once. This seems too complicated to me.
-/

/-- A partial bijection sending the open ball in dimension `n` to the upper hemisphere
  (without the equator) of the sphere in dimension `n + 1`. -/
@[simps -isSimp]
def discToSphereUp' (n m : ℕ) :
    PartialEquiv (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin (n + (m + 1)))) where
  toFun := fun x ↦ Fin.append x (Fin.cons (√(1 - ‖x‖ ^ 2)) (fun y ↦ 0: Fin m → ℝ))
  invFun := fun x ↦ Fin.take n (n.le_add_right (m + 1)) x
  source := ball 0 1
  target := sphere 0 1 ∩ {x | x ⟨n , by simp⟩ > 0} ∩ Hyperplane (n + (m + 1)) (n + 1)
  map_source' x hx := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · sorry
    · sorry
    · simp
      intro i hi1 hi2
      have : ¬ i < n := by sorry
      simp [Fin.append, Fin.addCases, this, Fin.cons]
      sorry
  map_target' y:= sorry
  left_inv' x hx := by rw [Fin.take_append_left _ n.le_refl, Fin.take_eq_self]
  right_inv' y := sorry

end Topology.CWComplex
