import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.Normed.Group.Basic

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

lemma closed_in_finite {X : Type*} [t : TopologicalSpace X] {ι : Type*} [Finite ι] (A : Set X) (B : ι → Set X) (closed : ∀ i, IsClosed (B i))
    (closedini : (∀ (i : ι), ∃ (C : t.Closeds), A ∩ B i = C.1 ∩ B i)) : ∃ (C : t.Closeds), A ∩ ⋃ i, B i = C.1 ∩ ⋃ i, B i := by
  let C' i := B i ∩ (Classical.choose (closedini i)).1
  let C := ⋃ i, C' i
  have closedC : IsClosed C := by
    simp only [C, C']
    apply isClosed_iUnion_of_finite
    intro i
    apply IsClosed.inter (closed i) (Classical.choose (closedini i)).2
  use ⟨C, closedC⟩
  simp only [C, C']
  rw [Set.inter_iUnion, Set.iUnion_inter]
  apply Set.iUnion_congr
  intro i
  rw [Set.inter_comm (B i), Set.inter_assoc, Set.inter_eq_left.2 (Set.subset_iUnion _ i)]
  exact Classical.choose_spec (closedini i)


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

lemma kification_le {X : Type*} [t : TopologicalSpace X] : (instkification : TopologicalSpace X) ≤ (t : TopologicalSpace X) := by
  intro A OpenA
  unfold IsOpen instkification
  simp only [TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Opens.carrier_eq_coe]
  intro B
  use ⟨A, OpenA⟩
  simp only [TopologicalSpace.Opens.coe_mk]

-- I feel like this should be easier then this
lemma inter_eq_inter_iff_compl {X : Type*} {A B C : Set X} : A ∩ B = C ∩ B ↔ Aᶜ ∩ B = Cᶜ ∩ B := by
  constructor
  · intro h
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, and_congr_left_iff]
    intro xmemB
    apply Iff.not
    sorry
  · sorry

lemma kification.closed_iff {X : Type*} [t : TopologicalSpace X] {A : Set X} : @IsClosed (kification X) _ A ↔ ∀ (B : t.Compacts), ∃ (C: t.Closeds), A ∩ B.1 = C.1 ∩ B.1 := by
  calc
    @IsClosed (kification X) _ A ↔ @IsOpen (kification X) _ Aᶜ := (@isOpen_compl_iff (kification X) A _).symm
    _ ↔ ∀ (B : t.Compacts), ∃ (C: t.Opens), Aᶜ ∩ B.1 = C.1 ∩ B.1 := by simp only [IsOpen,
      instkification, TopologicalSpace.Compacts.carrier_eq_coe,
      TopologicalSpace.Opens.carrier_eq_coe]
    _ ↔ ∀ (B : t.Compacts), ∃ (C: t.Closeds), A ∩ B.1 = C.1 ∩ B.1 := by
      constructor
      · intro h B
        rcases h B with ⟨O, hO⟩
        use ⟨Oᶜ, isClosed_compl_iff.2 O.2⟩
        rw [inter_eq_inter_iff_compl]
        simp only [TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Opens.carrier_eq_coe,
          compl_compl] at hO ⊢
        exact hO
      · intro h B
        rcases h B with ⟨C, hC⟩
        use ⟨Cᶜ, isOpen_compl_iff.2 C.2⟩
        rw [inter_eq_inter_iff_compl]
        simp only [TopologicalSpace.Compacts.carrier_eq_coe, compl_compl] at hC ⊢
        exact hC

lemma from_kification_continuous_of_continuous {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] (f : X → Y)
(cont : Continuous f) : @Continuous _ _ instkification _ f := by
  rw [continuous_def] at cont ⊢
  intro s opens
  exact (TopologicalSpace.le_def.1 kification_le) (f ⁻¹' s) (cont s opens)

lemma from_kification_continuouson_of_continuouson {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] (f : X → Y) (s : Set X)
(conton : ContinuousOn f s) : @ContinuousOn _ _ instkification _ f s := by
  rw [continuousOn_iff'] at conton ⊢
  intro t opent
  rcases conton t opent with ⟨u, openu, usub⟩
  use u
  exact ⟨(TopologicalSpace.le_def.1 kification_le) u openu, usub⟩

-- proof from Munkres, James Raymond. Topology. 2. ed., Pearson new internat. ed. Harlow: Pearson, 2014. Print. Lemma 46.3

lemma kification_eq_self_of_WeaklyLocallyCompactSpace {X : Type*} [t : TopologicalSpace X] [WeaklyLocallyCompactSpace X] : instkification = t := by
  apply le_antisymm
  · exact kification_le
  · intro A hA
    unfold IsOpen instkification at hA
    simp only [TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Opens.carrier_eq_coe] at hA
    simp only [kification]
    rw [@isOpen_iff_mem_nhds X A t]
    intro x xmemA
    rcases WeaklyLocallyCompactSpace.exists_compact_mem_nhds x with ⟨C, compact, Cnhds⟩
    rw [@mem_nhds_iff X x _ t] at Cnhds ⊢
    rcases Cnhds with ⟨U, Usub, openU, xmemU⟩
    use A ∩ U
    refine ⟨Set.inter_subset_left, ?_, ⟨xmemA, xmemU⟩⟩
    rcases hA ⟨C, compact⟩ with ⟨⟨V, openV⟩, hV⟩
    simp only [TopologicalSpace.Compacts.coe_mk, TopologicalSpace.Opens.coe_mk] at hV
    rw [← Set.inter_eq_right.2 Usub, ← Set.inter_assoc, hV, Set.inter_assoc, Set.inter_eq_right.2 Usub]
    exact IsOpen.inter openV openU

lemma continuous_compact_to_kification {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] (compact : CompactSpace X)
(f: X → Y) (cont : Continuous f) : @Continuous X Y tX instkification f := by
  rw [@continuous_iff_isClosed _ _ _ instkification]
  intro s closeds
  rw [@kification.closed_iff _ tY _] at closeds
  rcases closeds ⟨Set.range f, isCompact_range cont⟩ with ⟨u, hu⟩
  simp at hu
  have : f ⁻¹' s = f ⁻¹' (s ∩ Set.range f) := by
    rw [Set.preimage_inter, Set.preimage_range, Set.inter_univ]
  rw [this, hu, Set.preimage_inter, Set.preimage_range, Set.inter_univ]
  exact IsClosed.preimage cont u.2

lemma continuousOn_compact_to_kification {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {A : Set X} (compact : IsCompact A)
(f : X → Y) (conton : ContinuousOn f A) : @ContinuousOn _ _ _ instkification f A := by
  rw [continuousOn_iff_continuous_restrict] at conton ⊢
  exact continuous_compact_to_kification (isCompact_iff_compactSpace.1 compact) (A.restrict f) conton

-- proof from Munkres, James Raymond. Topology. 2. ed., Pearson new internat. ed. Harlow: Pearson, 2014. Print. Lemma 46.4
lemma continuous_kification_of_continuousOn_compact {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] (f : X → Y)
    (conton : ∀ (C : tX.Compacts), ContinuousOn f C) :
    @Continuous (kification X) (kification Y) instkification instkification f := by
  have conton' :  ∀ (C : tX.Compacts), @ContinuousOn _ _ _ instkification f C := fun C ↦ continuousOn_compact_to_kification C.2 f (conton C)
  rw [continuous_def]
  intro V openV
  simp only [IsOpen, instkification, TopologicalSpace.Compacts.carrier_eq_coe,
    TopologicalSpace.Opens.carrier_eq_coe]
  intro C
  replace conton' := conton' C
  rw [continuousOn_iff'] at conton'
  rcases conton' V openV with ⟨U, openU, hU⟩
  use ⟨U, openU⟩
  exact hU

lemma continuous_kification_of_continuous {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] (f : X → Y) (cont : Continuous f) :
    @Continuous (kification X) (kification Y) instkification instkification f := by
  apply continuous_kification_of_continuousOn_compact
  intro C
  exact Continuous.continuousOn cont

lemma compacts_kification_eq_compacts {X : Type*} [t : TopologicalSpace X] (C : Set X) : IsCompact C  ↔ @IsCompact _ instkification C := by
  constructor
  · sorry
  · sorry

--This is probably too complicated with the types but I feel like it would still be useful
/-
lemma instkification_instTopologicalSpaceSubstype_comm {X : Type*} [t : TopologicalSpace X] {p : Set X} (compact : IsCompact p) :
      @instTopologicalSpaceSubtype X p instkification = @instkification {x : X // p x} instTopologicalSpaceSubtype := by
  let C := Subtype.val '' (Set.univ : Set {x : X // p x})
  have compactC := Subtype.isCompact_iff.1 (@CompactSpace.isCompact_univ {x : X // p x} _ compact)
  rw [@TopologicalSpace.ext_iff]
  intro s
  unfold instTopologicalSpaceSubtype instkification TopologicalSpace.induced IsOpen
  simp
  constructor
  · intro ⟨u, hu, subtypeu⟩ B
    rcases hu ⟨Subtype.val '' B.1, Subtype.isCompact_iff.1 B.2⟩ with ⟨O, hO⟩
    simp at hO
    use ⟨Subtype.val ⁻¹' O.1, IsOpen.preimage continuous_subtype_val O.2⟩
    simp
    rw [← subtypeu]
    sorry
  · intro h
    use Subtype.val '' s
    simp [Function.Injective.preimage_image Subtype.val_injective]
    intro B
    rcases h ⟨(@Subtype.val X p) ⁻¹' B.1, aux B⟩ with ⟨U, hU⟩
    simp at hU
    sorry
-/

-- I think I might need some more properties here for example that the compact sets of the kification
-- are again the original compact sets
-- I think taking two times the k-ification should then be again the k-ification maybe?

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
  ext x
  simp only [IsometryEquiv.image_closedBall, IsometryEquivFinMap_symmR_zero_eq_zero,
    Metric.mem_closedBall, Set.mem_prod]
  unfold PseudoMetricSpace.toDist Prod.pseudoMetricSpaceMax
  simp [dist]


lemma IsometryEquivFinMapR_image_sphere (m n : ℕ) : (IsometryEquivFinMap m n).symm '' Metric.sphere 0 1 = (Metric.sphere 0 1 : Set (Fin m → ℝ)) ×ˢ (Metric.closedBall 0 1 : Set (Fin n → ℝ)) ∪ (Metric.closedBall 0 1 : Set (Fin m → ℝ)) ×ˢ (Metric.sphere 0 1 : Set (Fin n → ℝ)) := by
  rw [IsometryEquiv.image_sphere, IsometryEquivFinMap_symmR_zero_eq_zero, sphere_prod]
  rfl

lemma prod_closedBall_eq_closedBall {X : Type*} [PseudoMetricSpace X] {m n : ℕ} (x : Fin m → X) (y : Fin n → X) : (Metric.closedBall x 1 : Set (Fin m → X)) ×ˢ (Metric.closedBall y 1 : Set (Fin n → X)) = (Metric.closedBall (x, y) 1: Set ((Fin m → X) × (Fin n → X))) := by
  ext z
  simp only [Set.mem_prod, Metric.mem_closedBall, PseudoMetricSpace.toDist,
    Prod.pseudoMetricSpaceMax, sup_le_iff]
