import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.MetricSpace.Isometry

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

-- I feel like this proof should be wayyy shorter. Correct usage of protected?
lemma aux1 (l : ℕ) {X : Type*} {s : ℕ →  Type*} (Y : (m : ℕ) → s m → Set X):
    ⋃ m, ⋃ (_ : m < Nat.succ l), ⋃ j, Y m j = (⋃ (j : s l), Y l j) ∪ ⋃ m, ⋃ (_ : m < l), ⋃ j, Y m j := by
  ext x
  simp only [Set.mem_iUnion, exists_prop, Set.mem_union]
  constructor
  · intro ⟨i, ⟨iltsuccl, h⟩⟩
    apply Order.le_of_lt_succ at iltsuccl
    by_cases h' : i = l
    · left
      rw [h'] at h
      exact h
    · push_neg at h'
      have := LE.le.lt_of_ne iltsuccl h'
      right
      use i
  · intro h
    rcases h with h | h
    · use l
      exact ⟨Nat.lt_succ_self l, h⟩
    · rcases h with ⟨i, iltl, h⟩
      use i
      exact ⟨lt_trans iltl (Nat.lt_succ_self l), h⟩

lemma ENat.coe_lt_top {n : ℕ} : ↑n < (⊤ : ℕ∞) := Ne.lt_top (ENat.coe_ne_top n)

lemma isClosed_inter_singleton {X : Type*} [TopologicalSpace X] [T1Space X] {A : Set X} {a : X} : IsClosed (A ∩ {a}) := by
  by_cases h : a ∈ A
  · have : A ∩ {a} = {a} := by simp only [Set.inter_eq_right, Set.singleton_subset_iff, h]
    rw [this]
    exact isClosed_singleton
  · have : A ∩ {a} = ∅ := by simp only [Set.inter_singleton_eq_empty, h, not_false_eq_true]
    rw [this]
    exact isClosed_empty

lemma sphere_zero_dim_empty {X : Type*} {h : PseudoMetricSpace (Fin 0 → X)}: (Metric.sphere ![] 1 : Set (Fin 0 → X)) = ∅ := by
  simp [Metric.sphere, Matrix.empty_eq]


def kification (X : Type*) := X

instance instkification {X : Type*} [t : TopologicalSpace X] : TopologicalSpace (kification X) where
  IsOpen A := ∀ (B : t.Compacts), ∃ (C: t.Opens), A ∩ B.1 = C.1 ∩ B.1
  isOpen_univ := fun B ↦ (by use ⟨Set.univ, isOpen_univ⟩)
  isOpen_inter := by
    intro A1 A2 h1 h2 B
    rcases h1 B with ⟨C1, g1⟩
    rcases h2 B with ⟨C2, g2⟩
    use ⟨C1.1 ∩ C2.1, IsOpen.inter C1.2 C2.2⟩
    simp
    calc
      A1 ∩ A2 ∩ B.1 = (A1 ∩ B.1) ∩ (A2 ∩ B.1) := by simp [Set.inter_assoc, Set.inter_comm]
      _ = (C1.1 ∩ B.1) ∩ (C2.1 ∩ B.1) := by rw [g1, g2]
      _ = C1.1 ∩ C2.1 ∩ B.1 := by simp [← Set.inter_assoc, Set.inter_comm]
  isOpen_sUnion := by
    intro s h B
    simp at h
    let f := fun (t1 : s) ↦ Classical.choose (h t1 (by simp only [Subtype.coe_prop]) B)
    use ⟨⋃ (t : s), (f t).1 , isOpen_iUnion (fun t ↦ (f t).2)⟩
    simp_rw [Set.sUnion_eq_iUnion, Set.iUnion_inter]
    apply Set.iUnion_congr
    intro i
    simp [f]
    exact Classical.choose_spec (h i (by simp only [Subtype.coe_prop]) B)

def tokification (X : Type*) : X ≃ kification X := ⟨fun x ↦ x, fun x ↦ x, fun _ ↦ rfl, fun _ ↦ rfl⟩

def fromkification (X : Type*) : kification X ≃ X := ⟨fun x ↦ x, fun x ↦ x, fun _ ↦ rfl, fun _ ↦ rfl⟩

lemma continuous_fromkification {X : Type*} [t : TopologicalSpace X] : Continuous (fromkification X) where
isOpen_preimage A hA := by
  unfold fromkification
  simp only [instkification, Equiv.coe_fn_mk, Set.preimage_id', IsOpen]
  intro B
  use ⟨A, hA⟩

lemma isopenmap_tokification {X : Type*} [t: TopologicalSpace X] : IsOpenMap (tokification X) := by
  unfold IsOpenMap tokification
  intro A hA
  simp [instkification, IsOpen]
  intro B
  use ⟨A, hA⟩
  simp only [TopologicalSpace.Opens.coe_mk]


def EquivFinMap {X : Type*} (m n : ℕ) : (Fin m → X) × (Fin n → X) ≃ (Fin (m + n) → X) := Equiv.trans (Equiv.sumArrowEquivProdArrow _ _ _).symm (Equiv.arrowCongr finSumFinEquiv (Equiv.refl _))

def HomeomorphFinMap1 {X: Type*} [TopologicalSpace X] (m n : ℕ) : (Fin m → X) × (Fin n → X) ≃ₜ (Fin m ⊕ Fin n → X) where
  toFun := (Equiv.sumArrowEquivProdArrow _ _ _).symm
  invFun := Equiv.sumArrowEquivProdArrow _ _ _
  left_inv := (Equiv.sumArrowEquivProdArrow _ _ _).right_inv
  right_inv := (Equiv.sumArrowEquivProdArrow _ _ _).left_inv
  continuous_toFun := by
    simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk]
    apply continuous_pi
    intro i
    rcases i with i1 | i2
    · simp only [Sum.elim_inl]
      have : (fun (a : (Fin m → X) × (Fin n → X)) ↦ a.1 i1) = (fun b ↦ b i1) ∘ (fun a ↦ a.1) := by
        ext x
        simp
      rw [this]
      apply Continuous.comp' (continuous_apply _) continuous_fst
    · simp only [Sum.elim_inr]
      have : (fun (a : (Fin m → X) × (Fin n → X)) ↦ a.2 i2) = (fun b ↦ b i2) ∘ (fun a ↦ a.2) := by
        ext x
        simp
      rw [this]
      apply Continuous.comp' (continuous_apply _) continuous_snd
  continuous_invFun := by
    simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_mk, continuous_prod_mk]
    continuity

def HomeomorphFinMap2 {X: Type*} [TopologicalSpace X] (m n : ℕ) : (Fin m ⊕ Fin n → X) ≃ₜ (Fin (m + n) → X) where
  toFun := Equiv.arrowCongr finSumFinEquiv (Equiv.refl _)
  invFun := (Equiv.arrowCongr finSumFinEquiv (Equiv.refl _)).symm
  left_inv := (Equiv.arrowCongr finSumFinEquiv (Equiv.refl _)).left_inv
  right_inv := (Equiv.arrowCongr finSumFinEquiv (Equiv.refl _)).right_inv

def HomeomorphFinMap {X: Type*} [TopologicalSpace X] (m n : ℕ) : (Fin m → X) × (Fin n → X) ≃ₜ (Fin (m + n) → X) := Homeomorph.trans (HomeomorphFinMap1 _ _) (HomeomorphFinMap2 _ _)

def IsometryEquivFinMap1 {X: Type*} [PseudoEMetricSpace X] (m n : ℕ) : (Fin m → X) × (Fin n → X) ≃ᵢ (Fin m ⊕ Fin n → X) where
  toFun := (Equiv.sumArrowEquivProdArrow _ _ _).symm
  invFun := Equiv.sumArrowEquivProdArrow _ _ _
  left_inv := (Equiv.sumArrowEquivProdArrow _ _ _).right_inv
  right_inv := (Equiv.sumArrowEquivProdArrow _ _ _).left_inv
  isometry_toFun := by
    simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk]
    unfold Isometry
    intro ⟨a, b⟩ ⟨c, d⟩
    simp only [PseudoEMetricSpace.toEDist, pseudoEMetricSpacePi, Prod.pseudoEMetricSpaceMax,
      ENNReal.sup_eq_max]
    apply le_antisymm
    · apply Finset.sup_le
      intro p pmem
      rw [le_max_iff]
      rcases p with p1 | p2
      · simp only [Sum.elim_inl]
        left
        apply Finset.le_sup (Finset.mem_univ p1)
      · simp only [Sum.elim_inr]
        right
        apply Finset.le_sup (Finset.mem_univ p2)
    · rw [max_le_iff]
      constructor
      · apply Finset.sup_le
        intro p1 p1mem
        let p : Fin m ⊕ Fin n := .inl p1
        have : edist (a p1) (c p1) = (fun b_1 ↦ edist (Sum.elim a b b_1) (Sum.elim c d b_1)) p := by simp only [Sum.elim_inl,
          p]
        rw [this]
        exact @Finset.le_sup _ _ _ _ (Finset.univ : Finset (Fin m ⊕ Fin n)) (fun b_1 ↦ edist (Sum.elim a b b_1) (Sum.elim c d b_1)) p (Finset.mem_univ p)
      · apply Finset.sup_le
        intro p2 p2mem
        let p : Fin m ⊕ Fin n := .inr p2
        have : edist (b p2) (d p2) = (fun b_1 ↦ edist (Sum.elim a b b_1) (Sum.elim c d b_1)) p := by simp only [Sum.elim_inr,
          p]
        rw [this]
        exact @Finset.le_sup _ _ _ _ (Finset.univ : Finset (Fin m ⊕ Fin n)) (fun b_1 ↦ edist (Sum.elim a b b_1) (Sum.elim c d b_1)) p (Finset.mem_univ p)

def IsometryEquivFinMap2 {X: Type*} [PseudoEMetricSpace X] (m n : ℕ) : (Fin m ⊕ Fin n → X) ≃ᵢ (Fin (m + n) → X) where
  toFun := Equiv.arrowCongr finSumFinEquiv (Equiv.refl _)
  invFun := (Equiv.arrowCongr finSumFinEquiv (Equiv.refl _)).symm
  left_inv := (Equiv.arrowCongr finSumFinEquiv (Equiv.refl _)).left_inv
  right_inv := (Equiv.arrowCongr finSumFinEquiv (Equiv.refl _)).right_inv
  isometry_toFun := by
    simp [Equiv.arrowCongr, finSumFinEquiv]
    unfold Isometry
    intro x1 x2
    simp [PseudoEMetricSpace.toEDist, pseudoEMetricSpacePi]
    apply le_antisymm
    · apply Finset.sup_le
      intro b bmem
      unfold Fin.addCases
      by_cases hb : b < m
      · let b' : Fin m := ⟨b, hb⟩
        simp [hb]
        have : Fin.castLT b hb = b' := by simp [b', Fin.castLT]
        rw [this]
        exact @Finset.le_sup _ _ _ _ (Finset.univ : Finset (Fin m ⊕ Fin n)) (fun b ↦ edist (x1 b) (x2 b)) (Sum.inl b') (Finset.mem_univ (Sum.inl b'))
      · let hb' := hb
        push_neg at hb
        let b' : Fin n := ⟨b - m, Nat.sub_lt_left_of_lt_add hb b.2⟩
        simp [hb']
        have : @Fin.subNat n m (Fin.cast (Nat.add_comm m n) b) hb = b' := by simp only [Fin.subNat,
          Fin.coe_cast, b']
        rw [this]
        exact @Finset.le_sup _ _ _ _ (Finset.univ : Finset (Fin m ⊕ Fin n)) (fun b ↦ edist (x1 b) (x2 b)) (Sum.inr b') (Finset.mem_univ (Sum.inr b'))
    · apply Finset.sup_le
      intro b bmem
      rcases b with b1 | b2
      · have : edist (x1 (Sum.inl b1)) (x2 (Sum.inl b1)) = (fun b ↦ edist (x1 (Fin.addCases Sum.inl Sum.inr b)) (x2 (Fin.addCases Sum.inl Sum.inr b))) ⟨(b1 : Nat), lt_of_lt_of_le b1.2 (Nat.le_add_right _ _)⟩ := by
          simp [Fin.addCases]
        rw [this]
        exact @Finset.le_sup _ _ _ _ (Finset.univ : Finset (Fin (m + n))) (fun b ↦ edist (x1 (Fin.addCases Sum.inl Sum.inr b)) (x2 (Fin.addCases Sum.inl Sum.inr b))) ⟨(b1 : Nat), lt_of_lt_of_le b1.2 (Nat.le_add_right _ _)⟩ (Finset.mem_univ _)
      · have : edist (x1 (Sum.inr b2)) (x2 (Sum.inr b2)) = (fun b ↦ edist (x1 (Fin.addCases Sum.inl Sum.inr b)) (x2 (Fin.addCases Sum.inl Sum.inr b))) ⟨(m + b2: Nat), add_lt_add_left b2.2 _⟩ := by
          simp [Fin.addCases]
        rw [this]
        exact @Finset.le_sup _ _ _ _ (Finset.univ : Finset (Fin (m + n))) (fun b ↦ edist (x1 (Fin.addCases Sum.inl Sum.inr b)) (x2 (Fin.addCases Sum.inl Sum.inr b))) ⟨(m + b2: Nat), add_lt_add_left b2.2 _⟩ (Finset.mem_univ _)

def IsometryEquivFinMap {X : Type*} [PseudoEMetricSpace X] (m n : ℕ) : (Fin m → X) × (Fin n → X) ≃ᵢ (Fin (m + n) → X) := IsometryEquiv.trans (IsometryEquivFinMap1 _ _) (IsometryEquivFinMap2 _ _)

lemma IsometryEquivFinMapR_zero_eq_zero (m n : ℕ) : @IsometryEquivFinMap ℝ _ m n 0 = 0 := by
  unfold IsometryEquivFinMap IsometryEquivFinMap1 IsometryEquivFinMap2 Equiv.sumArrowEquivProdArrow Equiv.arrowCongr
  simp

lemma prod_closedBall_eq_closedBall {X : Type*} [PseudoMetricSpace X] {m n : ℕ} (x : Fin m → X) (y : Fin n → X) : (Metric.closedBall x 1 : Set (Fin m → X)) ×ˢ (Metric.closedBall y 1 : Set (Fin n → X)) = (Metric.closedBall (x, y) 1: Set ((Fin m → X) × (Fin n → X))) := by
  ext z
  simp only [Set.mem_prod, Metric.mem_closedBall, PseudoMetricSpace.toDist,
    Prod.pseudoMetricSpaceMax, sup_le_iff]
