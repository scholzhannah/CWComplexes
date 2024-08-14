import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.Normed.Group.Basic

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

lemma biUnion_lt_eq_iUnion {X : Type*} (I : ℕ → Set X) :
    ⋃ (n : ℕ) (m : ℕ) (_ : m < n), I m  = ⋃ (n : ℕ), I n := by
  ext x
  simp_rw [Set.mem_iUnion]
  exact ⟨fun ⟨_, m, _, xmem⟩ ↦ ⟨m, xmem⟩, fun ⟨n, xmem⟩ ↦  ⟨n + 1, n, lt_add_one n, xmem⟩⟩

-- are these useful? Or is there a more general version?
lemma Set.iUnion_sum {X Y Z: Type*} {f : X ⊕ Y → Set Z} :
    ⋃ x : X ⊕ Y, f x = (⋃ x : X, f (.inl x)) ∪ ⋃ x : Y, f (.inr x) := by
  ext; simp

--this seems to be in mathlib under this name. I might just not have the newest version or something
lemma ENat.coe_lt_top {n : ℕ} : ↑n < (⊤ : ℕ∞) := Ne.lt_top (ENat.coe_ne_top n)

-- is this needed?
lemma ENat.coe_lt_of_lt {n m : ℕ} : n < m → (n : ℕ∞) < m := by simp

lemma ENat.add_one_pos {n : ℕ∞} : 0 < n + 1 := by
  rw [← ENat.one_le_iff_pos]
  exact le_add_self

lemma ENat.exists_eq_add_one_of_ne_zero {n : ℕ∞} (nzero : n ≠ 0) : ∃ (k : ℕ∞), n = k + 1 := by
  by_cases h : n = ⊤
  · use ⊤
    simp only [h, top_add]
  rw [← ne_eq, WithTop.ne_top_iff_exists] at h
  rcases h with ⟨m, rfl⟩
  rcases Nat.exists_eq_succ_of_ne_zero (n := m) (by intro h; apply nzero; simp only [h,
    WithTop.coe_zero]) with ⟨l, rfl⟩
  use l
  norm_cast

lemma ENat.add_coe_lt_add_coe_right {n m : ℕ∞} {k : ℕ} : n + k < m + k ↔ n < m := by
  cases' n with n
  · simp
  cases' m with m
  · norm_cast; simp [ENat.coe_lt_top, -Nat.cast_add]
  · norm_cast; simp_all

lemma IsOpen_le_iff_isClosed_le {α : Type*} {t : TopologicalSpace α} {s : TopologicalSpace α} :
    @IsOpen _ s ≤ @IsOpen _ t ↔ @IsClosed _ s  ≤ @IsClosed _ t := by
  constructor
  · intro le a closeda
    rw [← compl_compl a, @isClosed_compl_iff] at closeda ⊢
    exact le _ closeda
  · intro le a opena
    rw [← @isClosed_compl_iff] at opena ⊢
    exact le _ opena

lemma TopologicalSpace.le_iff_IsClosed {α : Type*} {t : TopologicalSpace α} {s : TopologicalSpace α} :
    t ≤ s ↔ @IsClosed _ s  ≤ @IsClosed _ t := by
  rw [← IsOpen_le_iff_isClosed_le]
  exact TopologicalSpace.le_def

lemma closedBall_zero_dim_singleton {X : Type*} {h : PseudoMetricSpace (Fin 0 → X)} :
    (Metric.closedBall ![] 1 : Set (Fin 0 → X)) = {![]} := by
  ext
  simp only [Matrix.empty_eq, Metric.mem_closedBall, dist_self, zero_le_one, Set.mem_singleton_iff]

lemma sphere_zero_dim_empty {X : Type*} {h : PseudoMetricSpace (Fin 0 → X)} :
    (Metric.sphere ![] 1 : Set (Fin 0 → X)) = ∅ := by
  simp only [Metric.sphere, Matrix.empty_eq, dist_self, zero_ne_one, Set.setOf_false]

lemma closed_in_finite {X : Type*} [t : TopologicalSpace X] {ι : Type*} [Finite ι] (A : Set X)
    (B : ι → Set X) (closed : ∀ i, IsClosed (B i))
    (closedini : (∀ (i : ι), ∃ (C : t.Closeds), A ∩ B i = C.1 ∩ B i)) :
    ∃ (C : t.Closeds), A ∩ ⋃ i, B i = C.1 ∩ ⋃ i, B i := by
  choose C₀ hC₀ using closedini
  let C' i := B i ∩ C₀ i
  let C := ⋃ i, C' i
  have closedC : IsClosed C := by
    simp only [C, C']
    apply isClosed_iUnion_of_finite
    exact fun i ↦ IsClosed.inter (closed i) (C₀ i).2
  use ⟨C, closedC⟩
  simp only [C, C']
  rw [Set.inter_iUnion, Set.iUnion_inter]
  apply Set.iUnion_congr
  intro i
  rw [Set.inter_comm (B i), Set.inter_assoc, Set.inter_eq_left.2 (Set.subset_iUnion _ i), hC₀]
  rfl

lemma inter_eq_inter_iff_compl {X : Type*} {A B C : Set X} : A ∩ B = C ∩ B ↔ Aᶜ ∩ B = Cᶜ ∩ B := by
  constructor <;> (intro; simp_all [Set.ext_iff, not_iff_not])

lemma open_in_iff_compl_closed_in {X : Type*} [TopologicalSpace X] (A B : Set X) :
    (∃ (C: TopologicalSpace.Opens X), A ∩ B = C.1 ∩ B) ↔
    ∃ (C: TopologicalSpace.Closeds X), Aᶜ ∩ B = C.1 ∩ B := by
  constructor
  · intro ⟨C, hC⟩
    use ⟨Cᶜ, isClosed_compl_iff.2 C.2⟩
    rw [inter_eq_inter_iff_compl]
    simp_rw [compl_compl]
    exact hC
  · intro ⟨C, hC⟩
    use ⟨Cᶜ, isOpen_compl_iff.2 C.2⟩
    rw [inter_eq_inter_iff_compl]
    simp_rw [compl_compl]
    exact hC

-- look up if this exists
def PartialEquiv.const {X Y : Type*} (x : X) (y : Y) : PartialEquiv X Y where
  toFun := Function.const X y
  invFun := Function.const Y x
  source := {x}
  target := {y}
  map_source' := fun _ _ ↦ by rfl
  map_target' := fun _ _ ↦ by rfl
  left_inv' := fun x' x'mem  ↦ by rw [Set.eq_of_mem_singleton x'mem]; rfl
  right_inv' := fun y' y'mem ↦ by rw [Set.eq_of_mem_singleton y'mem]; rfl

lemma PartialEquiv.const_continuousOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) : ContinuousOn (PartialEquiv.const x y) {x}
  := continuousOn_singleton (PartialEquiv.const x y) x

def EquivFinMap {X : Type*} (m n : ℕ) : (Fin m → X) × (Fin n → X) ≃ (Fin (m + n) → X) :=
  Equiv.trans (Equiv.sumArrowEquivProdArrow _ _ _).symm (Equiv.arrowCongr finSumFinEquiv (Equiv.refl _))

def HomeomorphFinMap1 {X: Type*} [TopologicalSpace X] (m n : ℕ) :
    (Fin m → X) × (Fin n → X) ≃ₜ (Fin m ⊕ Fin n → X) where
  toEquiv := (Equiv.sumArrowEquivProdArrow _ _ _).symm
  continuous_toFun := by
    simp_rw [Equiv.sumArrowEquivProdArrow, Equiv.toFun_as_coe, Equiv.coe_fn_symm_mk]
    apply continuous_pi
    intro i
    rcases i with i1 | i2
    · suffices Continuous ((fun b ↦ b i1) ∘ (fun (a : (Fin m → X) × (Fin n → X)) ↦ a.1)) by simpa only
      apply Continuous.comp' (continuous_apply _) continuous_fst
    · suffices Continuous ((fun b ↦ b i2) ∘ (fun (a : (Fin m → X) × (Fin n → X)) ↦ a.2)) by simpa only
      apply Continuous.comp' (continuous_apply _) continuous_snd
  continuous_invFun := by
    simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_mk, continuous_prod_mk]
    continuity --is it better to leave this or replace it by an explicit proof

-- Homeomorph.piCongrLeft
def HomeomorphFinMap2 {X: Type*} [TopologicalSpace X] (m n : ℕ) :
    (Fin m ⊕ Fin n → X) ≃ₜ (Fin (m + n) → X) where
  toEquiv := Equiv.arrowCongr finSumFinEquiv (Equiv.refl _)

def HomeomorphFinMap {X: Type*} [TopologicalSpace X] (m n : ℕ) :
    (Fin m → X) × (Fin n → X) ≃ₜ (Fin (m + n) → X) :=
  (HomeomorphFinMap1 _ _).trans (HomeomorphFinMap2 _ _)

def IsometryEquivFinMap1 {X: Type*} [PseudoEMetricSpace X] (m n : ℕ) :
    (Fin m → X) × (Fin n → X) ≃ᵢ (Fin m ⊕ Fin n → X) where
  toFun := (Equiv.sumArrowEquivProdArrow _ _ _).symm
  invFun := Equiv.sumArrowEquivProdArrow _ _ _
  left_inv := (Equiv.sumArrowEquivProdArrow _ _ _).right_inv
  right_inv := (Equiv.sumArrowEquivProdArrow _ _ _).left_inv
  isometry_toFun := by
    simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk, Isometry]
    intro ⟨a, b⟩ ⟨c, d⟩
    simp only [PseudoEMetricSpace.toEDist, pseudoEMetricSpacePi, Prod.pseudoEMetricSpaceMax,
      ENNReal.sup_eq_max]
    apply le_antisymm
    · apply Finset.sup_le
      intro p pmem
      rw [le_max_iff]
      rcases p with p1 | p2
      · left
        apply Finset.le_sup (Finset.mem_univ p1)
      · right
        apply Finset.le_sup (Finset.mem_univ p2)
    · rw [max_le_iff]
      constructor
      · apply Finset.sup_le
        intro p1 p1mem
        suffices (fun b_1 ↦ edist (Sum.elim a b b_1) (Sum.elim c d b_1)) (.inl p1) ≤
          edist (Sum.elim a b) (Sum.elim c d) by simpa only
        exact @Finset.le_sup _ _ _ _ (Finset.univ : Finset (Fin m ⊕ Fin n))
          (fun b_1 ↦ edist (Sum.elim a b b_1) (Sum.elim c d b_1)) (.inl p1) (Finset.mem_univ (Sum.inl p1))
      · apply Finset.sup_le
        intro p2 p2mem
        suffices (fun b_1 ↦ edist (Sum.elim a b b_1) (Sum.elim c d b_1)) (.inr p2) ≤
          edist (Sum.elim a b) (Sum.elim c d) by simpa only
        exact @Finset.le_sup _ _ _ _ (Finset.univ : Finset (Fin m ⊕ Fin n))
          (fun b_1 ↦ edist (Sum.elim a b b_1) (Sum.elim c d b_1)) (.inr p2) (Finset.mem_univ (Sum.inr p2))

def IsometryEquivFinMap2 {X: Type*} [PseudoEMetricSpace X] (m n : ℕ) :
    (Fin m ⊕ Fin n → X) ≃ᵢ (Fin (m + n) → X) where
  toFun := Equiv.arrowCongr finSumFinEquiv (Equiv.refl _)
  invFun := (Equiv.arrowCongr finSumFinEquiv (Equiv.refl _)).symm
  left_inv := (Equiv.arrowCongr finSumFinEquiv (Equiv.refl _)).left_inv
  right_inv := (Equiv.arrowCongr finSumFinEquiv (Equiv.refl _)).right_inv
  isometry_toFun := by
    simp only [Equiv.arrowCongr, Equiv.coe_refl, finSumFinEquiv, Equiv.coe_fn_symm_mk,
      CompTriple.comp_eq, Equiv.refl_symm, Equiv.coe_fn_mk, Isometry]
    intro x1 x2
    simp only [PseudoEMetricSpace.toEDist, pseudoEMetricSpacePi]
    apply le_antisymm
    · apply Finset.sup_le
      intro b bmem
      unfold Fin.addCases
      by_cases hb : b < m
      · simp only [eq_rec_constant, Function.comp_apply, hb, ge_iff_le]
        exact @Finset.le_sup _ _ _ _ (Finset.univ : Finset (Fin m ⊕ Fin n)) (fun b ↦ edist (x1 b) (x2 b)) (Sum.inl (Fin.castLT b hb)) (Finset.mem_univ (Sum.inl (Fin.castLT b hb)))
      · simp only [eq_rec_constant, Function.comp_apply, hb]
        exact @Finset.le_sup _ _ _ _ (Finset.univ : Finset (Fin m ⊕ Fin n)) (fun b ↦ edist (x1 b) (x2 b)) (Sum.inr (@Fin.subNat n m (Fin.cast (Nat.add_comm m n) b) (not_lt.1 hb))) (Finset.mem_univ (Sum.inr (@Fin.subNat n m (Fin.cast (Nat.add_comm m n) b) (not_lt.1 hb))))
    · apply Finset.sup_le
      intro b bmem
      rcases b with b1 | b2
      · suffices (fun b ↦ edist (x1 (Fin.addCases Sum.inl Sum.inr b)) (x2 (Fin.addCases Sum.inl Sum.inr b))) ⟨(b1 : Nat), lt_of_lt_of_le b1.2 (Nat.le_add_right _ _)⟩
            ≤ edist (x1 ∘ fun i => Fin.addCases Sum.inl Sum.inr i) (x2 ∘ fun i => Fin.addCases Sum.inl Sum.inr i) by
          simpa only [Fin.addCases, eq_rec_constant, ge_iff_le, Fin.is_lt,
            Fin.castLT_mk, Fin.eta]
        exact @Finset.le_sup _ _ _ _ (Finset.univ : Finset (Fin (m + n))) (fun b ↦ edist (x1 (Fin.addCases Sum.inl Sum.inr b)) (x2 (Fin.addCases Sum.inl Sum.inr b))) ⟨(b1 : Nat), lt_of_lt_of_le b1.2 (Nat.le_add_right _ _)⟩ (Finset.mem_univ _)
      · suffices (fun b ↦ edist (x1 (Fin.addCases Sum.inl Sum.inr b)) (x2 (Fin.addCases Sum.inl Sum.inr b))) ⟨(m + b2: Nat), add_lt_add_left b2.2 _⟩ ≤
            edist (x1 ∘ fun i => Fin.addCases Sum.inl Sum.inr i) (x2 ∘ fun i => Fin.addCases Sum.inl Sum.inr i) by
          simpa only [Fin.addCases,
            eq_rec_constant, ge_iff_le, add_lt_iff_neg_left, not_lt_zero',
            Fin.cast_mk, Fin.subNat_mk, Fin.natAdd_mk, add_tsub_cancel_left, Fin.eta]
        exact @Finset.le_sup _ _ _ _ (Finset.univ : Finset (Fin (m + n))) (fun b ↦ edist (x1 (Fin.addCases Sum.inl Sum.inr b)) (x2 (Fin.addCases Sum.inl Sum.inr b))) ⟨(m + b2: Nat), add_lt_add_left b2.2 _⟩ (Finset.mem_univ _)

def IsometryEquivFinMap {X : Type*} [PseudoEMetricSpace X] (m n : ℕ) : (Fin m → X) × (Fin n → X) ≃ᵢ (Fin (m + n) → X) := IsometryEquiv.trans (IsometryEquivFinMap1 _ _) (IsometryEquivFinMap2 _ _)

lemma IsometryEquivFinMapR_zero_eq_zero (m n : ℕ) : @IsometryEquivFinMap ℝ _ m n 0 = 0 := by
  unfold IsometryEquivFinMap IsometryEquivFinMap1 IsometryEquivFinMap2 Equiv.sumArrowEquivProdArrow Equiv.arrowCongr
  simp

lemma IsometryEquivFinMap_symmR_zero_eq_zero (m n : ℕ) : (@IsometryEquivFinMap ℝ _ m n).symm 0 = 0 := by
  rw [IsometryEquiv.symm_apply_eq]
  exact (IsometryEquivFinMapR_zero_eq_zero m n).symm

lemma IsometryEquivFinMapR_image_ball (m n : ℕ) : (IsometryEquivFinMap m n).symm '' Metric.ball 0 1 = (Metric.ball 0 1 : Set (Fin m → ℝ)) ×ˢ (Metric.ball 0 1 : Set (Fin n → ℝ)) := by
  ext x
  simp only [IsometryEquiv.image_ball, IsometryEquivFinMap_symmR_zero_eq_zero, Metric.mem_ball,
    Set.mem_prod]
  unfold PseudoMetricSpace.toDist Prod.pseudoMetricSpaceMax
  simp [dist]

lemma IsometryEquivFinMapR_image_closedball (m n : ℕ) : (IsometryEquivFinMap m n).symm '' Metric.closedBall 0 1 = (Metric.closedBall 0 1 : Set (Fin m → ℝ)) ×ˢ (Metric.closedBall 0 1 : Set (Fin n → ℝ)) := by
  ext
  simp only [IsometryEquiv.image_closedBall, IsometryEquivFinMap_symmR_zero_eq_zero,
    Metric.mem_closedBall, Set.mem_prod]
  unfold PseudoMetricSpace.toDist Prod.pseudoMetricSpaceMax
  simp [dist]

lemma IsometryEquivFinMapR_image_sphere (m n : ℕ) : (IsometryEquivFinMap m n).symm '' Metric.sphere 0 1 = (Metric.sphere 0 1 : Set (Fin m → ℝ)) ×ˢ (Metric.closedBall 0 1 : Set (Fin n → ℝ)) ∪ (Metric.closedBall 0 1 : Set (Fin m → ℝ)) ×ˢ (Metric.sphere 0 1 : Set (Fin n → ℝ)) := by
  rw [IsometryEquiv.image_sphere, IsometryEquivFinMap_symmR_zero_eq_zero, sphere_prod]
  rfl

--this name should be reworked
--does this already exist?
def IsometryEquiv.arrowCongrleft {X Y : Type*} [Fintype X] [Fintype Y] (Z : Type*) [EMetricSpace Z]
    (equiv : X ≃ Y) : (X → Z) ≃ᵢ (Y → Z) :=
  IsometryEquiv.mk (equiv.arrowCongr (Equiv.refl Z))
  (
  by
    intro x1 x2
    simp [pseudoEMetricSpacePi, PseudoMetricSpace.toDist, instEDistForall]
    apply le_antisymm
    · apply Finset.sup_le
      intro b bmem
      by_cases h: edist (x1 (equiv.symm b)) (x2 (equiv.symm b)) = 0
      · rw [h]
        simp only [zero_le]
      · rw [Finset.le_sup_iff (by aesop)]
        use equiv.symm b
        simp only [Finset.mem_univ, le_refl, and_self]
    · apply Finset.sup_le
      intro b bmem
      by_cases h: edist (x1 b) (x2 b) = 0
      · rw [h]
        simp only [zero_le]
      · rw [Finset.le_sup_iff (by aesop)]
        use equiv b
        simp only [Finset.mem_univ, Equiv.symm_apply_apply, le_refl, and_self]
  )

-- does this really not exist?
lemma ContinuousOn.image_comp_continuous {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] {g : β → γ} {f : α → β} {s : Set α} (cont : Continuous f)
    (conton : ContinuousOn g (f '' s)) : ContinuousOn (g ∘ f) s :=
  conton.comp cont.continuousOn (s.mapsTo_image f)

#check IsometryEquiv.trans

-- these should not exists, take them out
lemma Equiv.transPartialEquiv_image {α β γ : Type*} (e : α ≃ β) (f : PartialEquiv β γ) (s : Set α) :
    (e.transPartialEquiv f) '' s = f '' (e '' s) := by
  simp [Set.image_image]

lemma IsometryEquiv.trans_image {α β γ : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    [PseudoEMetricSpace γ] (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (s : Set α) :
    (h₁.trans h₂) '' s = h₂ '' (h₁ '' s) := by
  aesop

-- does this not exist???
lemma Set.subset_product {α β : Type*} {s : Set (α × β)} :
    s ⊆ Set.image Prod.fst s ×ˢ Set.image Prod.snd s :=
  fun _ hp ↦ mem_prod.2 ⟨mem_image_of_mem _ hp, mem_image_of_mem _ hp⟩

def T2Space.mono {X : Type*} {s t : TopologicalSpace X}
    (le : t ≤ s) [t2 : @T2Space X s] : @T2Space X t where
  t2 := by
    intro i j ne
    rw [t2Space_iff] at t2
    obtain ⟨u, v, openu, openv, huv⟩ := t2 ne
    use u, v
    exact ⟨le _ openu, le _ openv, huv⟩
