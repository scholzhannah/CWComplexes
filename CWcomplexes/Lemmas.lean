import CWcomplexes.Constructions

open Metric Set

variable {X : Type*} [t : TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]


namespace CWComplex

lemma isClosed_levelaux (n : ℕ∞) : IsClosed (levelaux C n) := (CWComplex_levelaux _ n).isClosed

lemma isClosed_level (n : ℕ∞) : IsClosed (level C n) := isClosed_levelaux _

lemma closed_iff_inter_levelaux_closed {A : Set X} (asubc : A ⊆ C) :
    IsClosed A ↔ ∀ (n : ℕ), IsClosed (A ∩ levelaux C n) := by
  refine ⟨fun closedA _ ↦  IsClosed.inter closedA (isClosed_levelaux _), ?_⟩
  intro h
  rw [closed A asubc]
  intro n j
  rw [(Set.inter_eq_right.2 (closedCell_subset_levelaux n j)).symm, ← inter_assoc]
  exact IsClosed.inter (h (n + 1)) isClosed_closedCell

lemma inter_levelaux_succ_closed_iff_inter_levelaux_closed_and_inter_closedCell_closed (A : Set X) :
    IsClosed (A ∩ levelaux C (Nat.succ n)) ↔ IsClosed (A ∩ levelaux C n) ∧
    ∀ (j : cell C n), IsClosed (A ∩ closedCell n j) := by
  constructor
  · intro closed
    constructor
    · rw [← inter_eq_right.2 (levelaux_mono ((by norm_cast; exact Nat.le_succ n) : ↑n ≤ ↑n.succ)),
        ← inter_assoc]
      exact closed.inter (isClosed_levelaux n)
    · intro j
      have : A ∩ levelaux C ↑(Nat.succ n) ⊆ C := by
        apply subset_trans inter_subset_right
        simp_rw [← levelaux_top (C := C)]
        exact levelaux_mono le_top
      rw [CWComplex.closed (A ∩ levelaux C ↑(Nat.succ n)) this] at closed
      replace closed := closed n j
      rw [inter_assoc, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
        inter_eq_right.2 (closedCell_subset_levelaux n j)] at closed
      exact closed
  · intro ⟨closed1, closed2⟩
    have : A ∩ levelaux C ↑(Nat.succ n) ⊆ C := by
      apply subset_trans inter_subset_right
      simp_rw [← levelaux_top (C := C)]
      exact levelaux_mono le_top
    apply strong_induction_isClosed this
    intro m _ j
    by_cases msuccltn : m < n
    · right
      rw [inter_assoc, ← inter_eq_right.2
        ((closedCell_subset_levelaux m j).trans (levelaux_mono (by norm_cast : (m : ℕ∞) + 1 ≤ n))),
        ← inter_assoc (levelaux _ _),
        inter_eq_right.2 (levelaux_mono (by norm_cast; exact Nat.le_succ n)), ← inter_assoc]
      exact closed1.inter isClosed_closedCell
    by_cases msucceqn : m = n
    · right
      subst msucceqn
      rw [inter_assoc, inter_comm (levelaux _ (Nat.succ m)), ← inter_assoc]
      exact (closed2 _).inter (isClosed_levelaux _)
    left
    have : Nat.succ n ≤ m := by
      push_neg at msuccltn msucceqn
      exact LE.le.lt_of_ne msuccltn msucceqn.symm
    rw [inter_assoc, levelaux_inter_openCell_eq_empty (by norm_cast), inter_empty]
    exact isClosed_empty

lemma induction_isClosed_levelaux {A : Set X} (asub : A ⊆ C)
    (step : ∀ (n : ℕ), (∀ m (_ : m ≤ n), IsClosed (A ∩ levelaux C m)) →
    ∀ j, IsClosed (A ∩ closedCell (C := C) n j)) :
    IsClosed A := by
  rw [closed_iff_inter_levelaux_closed asub]
  intro n
  induction' n using Nat.case_strong_induction_on with n hn
  · simp only [CharP.cast_eq_zero, levelaux_zero_eq_empty, inter_empty, isClosed_empty]
  rw [inter_levelaux_succ_closed_iff_inter_levelaux_closed_and_inter_closedCell_closed]
  exact ⟨hn n n.le_refl, step n hn⟩

lemma isDiscrete_levelaux_one {A : Set X} : IsClosed (A ∩ levelaux C 1) := by
  apply strong_induction_isClosed (C := C) (inter_subset_right.trans
    (by simp_rw [← levelaux_top (C := C)]; apply levelaux_mono le_top))
  intro n nlt j
  left
  simp_rw [← Nat.succ_le_iff, ← Nat.one_eq_succ_zero] at nlt
  rw [inter_assoc, levelaux_inter_openCell_eq_empty (by simp only [Nat.one_le_cast, nlt]), inter_empty]
  exact isClosed_empty

/- The following is one way of stating that `level 0` is discrete. -/
lemma isDiscrete_level_zero {A : Set X} : IsClosed (A ∩ level C 0) := isDiscrete_levelaux_one

lemma compact_inter_finite (A : Set X) (compact : IsCompact A) :
  _root_.Finite (Σ (m : ℕ), {j : cell C m // ¬ Disjoint A (openCell m j)}) := by
  by_contra h
  simp only [TopologicalSpace.Compacts.carrier_eq_coe, not_disjoint_iff, SetLike.mem_coe,
    not_finite_iff_infinite] at h
  let p (m : Σ (m : ℕ), { j : cell C m // ∃ x ∈ A, x ∈ openCell m j}) :=
    Classical.choose (m.2).2
  let hp m : p m ∈ A ∧ p m ∈ openCell m.1 m.2 := by
    simp_rw [p]
    exact Classical.choose_spec (m.2).2
  let P := p '' (univ : Set (Σ (m : ℕ), {j : cell C m // ∃ x ∈ A, x ∈ openCell m j}))
  have infpoints : P.Infinite := by
    apply (infinite_univ_iff.2 h).image
    intro ⟨m, j, hj⟩ _ ⟨n, i, hi⟩ _ peqp
    have hpj : p ⟨m, j, hj⟩ ∈ openCell m j := by simp_rw [p, (Classical.choose_spec hj).2]
    have hpi : p ⟨m, j, hj⟩ ∈ openCell n i := by simp_rw [peqp, p, (Classical.choose_spec hi).2]
    suffices (⟨m, j⟩ : Σ n, cell C n) = ⟨n, i⟩ by aesop
    apply eq_cell_of_not_disjoint
    rw [not_disjoint_iff]
    use p ⟨m, j, hj⟩
  have subsetA : P ⊆ A := by
    intro x xmem
    simp only [mem_image, image_univ, mem_range, P] at xmem
    obtain ⟨n, rfl⟩ := xmem
    exact (hp n).1
  have subsetsclosed : ∀ (s : Set P), IsClosed (s : Set X) := by
    intro s
    have ssubc : ↑↑s ⊆ ↑C := by
      apply (Subtype.coe_image_subset ↑P s).trans
      intro x xmem
      simp only [image_univ, mem_range, P] at xmem
      obtain ⟨m, rfl⟩ := xmem
      exact openCell_subset_complex _ _ (hp m).2
    apply induction_isClosed_levelaux ssubc
    intro n hn j
    simp_rw [← cellFrontier_union_openCell_eq_closedCell, inter_union_distrib_left]
    apply IsClosed.union
    · rw [← inter_eq_right.2 (cellFrontier_subset_levelaux n j), ← inter_assoc]
      exact (hn n (le_refl _)).inter isClosed_cellFrontier
    · by_cases empty : Subtype.val '' s ∩ openCell n j = ∅
      · rw [empty]
        exact isClosed_empty
      rw [eq_empty_iff_forall_not_mem, not_forall_not] at empty
      have hnj : ∃ x ∈ A, x ∈ openCell n j := by
        obtain ⟨x, xmem⟩ := empty
        use x
        exact ⟨((Subtype.coe_image_subset P s).trans subsetA ) xmem.1, xmem.2⟩
      suffices Subtype.val '' s ∩ openCell n j = {p ⟨n, j, hnj⟩} by
        rw [this]
        exact isClosed_singleton
      have hpnj := hp ⟨n, j, hnj⟩
      have : ∀ (y : X) (ymemP : y ∈ P), ⟨y, ymemP⟩ ∈ s → ↑y ∈ openCell n j → y = p ⟨n, ⟨j, hnj⟩⟩ := by
        intro y ymemP ymems ymemopen
        simp only [image_univ, mem_range, Sigma.exists, Subtype.exists, P] at ymemP
        obtain ⟨m, i, hmi, rfl⟩ := ymemP
        have hpmi := hp ⟨m, i, hmi⟩
        suffices (⟨m, i⟩ : Σ n, cell C n) = ⟨n, j⟩ by -- I would like to automate this somehow
          rw [Sigma.mk.inj_iff] at this
          obtain ⟨eq1, eq2⟩ := this
          subst eq1
          rw [heq_eq_eq] at eq2
          subst eq2
          rfl
        apply eq_cell_of_not_disjoint
        rw [not_disjoint_iff]
        use p ⟨m, ⟨i, hmi⟩⟩
        exact ⟨hpmi.2, ymemopen⟩
      apply subset_antisymm
      · simp only [subset_singleton_iff, mem_inter_iff, mem_image, Subtype.exists,
          exists_and_right, exists_eq_right, and_imp, forall_exists_index]
        exact this
      · obtain ⟨y, ymem⟩ := empty
        suffices y = p ⟨n, ⟨j, hnj⟩⟩ by
          subst this
          simp only [singleton_subset_iff]
          exact ymem
        refine this y (Subtype.coe_image_subset P s ymem.1) (mem_of_mem_image_val ymem.1) ymem.2
  have discrete : DiscreteTopology ↑P := by
    rw [discreteTopology_iff_forall_isClosed]
    intro s
    simp only [instTopologicalSpaceSubtype, isClosed_induced_iff]
    use s
    simp only [Subtype.val_injective, preimage_image_eq, and_true]
    exact subsetsclosed s
  have closed: IsClosed P := by
    have := subsetsclosed (univ : Set P)
    rw [Subtype.coe_image_univ] at this
    exact this
  have compact : IsCompact P := compact.of_isClosed_subset closed subsetA
  have finite : Set.Finite P := compact.finite discrete
  contradiction

lemma compact_inter_finite_subset (A : Set X) (compact : IsCompact A)
    {I : (n : ℕ) → Set (cell C n)} :
    _root_.Finite (Σ (m : ℕ), {j : I m // ¬ Disjoint A (openCell (C := C) m j)}) := by
  let f := fun (x : Σ (m : ℕ), {j : I m // ¬ Disjoint A (openCell (C := C) m j)}) ↦
    (⟨x.1, ⟨x.2.1, x.2.2⟩⟩ : Σ (m : ℕ), {j : cell C m // ¬ Disjoint A (openCell m j)})
  apply @Finite.of_injective _ _ (compact_inter_finite A compact) f
  unfold Function.Injective
  intro ⟨x1, x2, x3⟩ ⟨y1, y2, y3⟩ eq
  simp only [TopologicalSpace.Compacts.carrier_eq_coe, Sigma.mk.inj_iff, f] at eq
  rcases eq with ⟨rfl, eq⟩
  simp only [heq_eq_eq, Subtype.mk.injEq, Subtype.val_inj] at eq
  simp_rw [eq]

lemma compact_inter_finite' (A : Set X) (compact : IsCompact A) :
    _root_.Finite {x : Σ (n : ℕ), cell C n // ¬Disjoint A (openCell x.fst x.snd)} := by
  let f := fun (x : (Σ (m : ℕ), {j : cell C m // ¬ Disjoint A (openCell m j)})) ↦
    (⟨⟨x.1, x.2.1⟩, x.2.2⟩ : { x : Σ (n : ℕ), cell C n // ¬Disjoint A (openCell x.fst x.snd)})
  apply @Finite.of_surjective _ _ (compact_inter_finite A compact) f
  unfold Function.Surjective
  intro x
  use ⟨x.1.1, ⟨x.1.2, x.2⟩⟩

lemma compact_inter_finite_subset' (A : Set X) (compact : IsCompact A)
    {I : (n : ℕ) → Set (cell C n)} :
    _root_.Finite {x : Σ (n : ℕ), I n // ¬Disjoint A (openCell (C := C) x.fst x.snd)} := by
  let f := fun (x : {x : Σ (n : ℕ), I n // ¬Disjoint A (openCell (C := C) x.fst x.snd)}) ↦
    (⟨⟨x.1.1, x.1.2⟩, x.2⟩ : {x : Σ (n : ℕ), cell C n // ¬Disjoint A (openCell x.fst x.snd)})
  apply @Finite.of_injective _ _ (compact_inter_finite' A compact) f
  unfold Function.Injective
  intro ⟨⟨x1, x2⟩, x3⟩ ⟨⟨y1, y2⟩, y3⟩ eq
  simp only [TopologicalSpace.Compacts.carrier_eq_coe, Subtype.mk.injEq, Sigma.mk.inj_iff, f] at eq
  rcases eq with ⟨rfl, eq⟩
  simp only [heq_eq_eq, Subtype.mk.injEq, Subtype.val_inj] at eq
  simp_rw [eq]

lemma subset_not_disjoint (A : Set X) : A ∩ C ⊆ ⋃ (x : Σ (m : ℕ),
    {j : cell C m // ¬ Disjoint A (openCell m j)}), closedCell (C := C) x.1 x.2 := by
  intro x ⟨xmem1, xmem2⟩
  simp only [mem_iUnion]
  simp only [← union_openCell, mem_iUnion] at xmem2
  rcases xmem2 with ⟨m, j, hmj⟩
  use ⟨m, j, not_disjoint_iff.2 ⟨x, xmem1, hmj⟩⟩
  exact openCell_subset_closedCell _ _ hmj

lemma subset_not_disjoint' (A : Set X) : A ∩ C ⊆ ⋃ (x : Σ (m : ℕ),
    {j : cell C m // ¬ Disjoint A (openCell m j)}), openCell (C := C) x.1 x.2 := by
  intro x ⟨xmem1, xmem2⟩
  simp only [mem_iUnion]
  simp only [← union_openCell, mem_iUnion] at xmem2
  rcases xmem2 with ⟨m, j, hmj⟩
  use ⟨m, j, not_disjoint_iff.2 ⟨x, xmem1, hmj⟩⟩

-- I don't think this is needed right now or ever really
-- lemma map_closedball_inter_finite_le (n : ℕ)  : _root_.Finite (Σ' (m : ℕ) (_ : m ≤ n), {j : hC.cell m // ¬ Disjoint A.1 (↑(hC.map m j) '' ball 0 1)}) := by
--   let f := fun (x : {x : Σ' (n : ℕ) (_ ), I n // ¬Disjoint A.1 (hC.map x.fst x.snd '' ball 0 1)}) ↦ (⟨⟨x.1.1, x.1.2⟩, x.2⟩ : {x : Σ (n : ℕ), hC.cell n // ¬Disjoint A.1 (hC.map x.fst x.snd '' ball 0 1)})
--   apply @Finite.of_injective _ _ (hC.compact_inter_finite' A) f
--   unfold Function.Injective
--   intro ⟨⟨x1, x2⟩, x3⟩ ⟨⟨y1, y2⟩, y3⟩ eq
--   simp [f] at eq
--   rcases eq with ⟨rfl, eq⟩
--   simp only [heq_eq_eq, Subtype.mk.injEq, Subtype.val_inj] at eq
--   simp_rw [eq]
--   sorry

-- lemma subset_not_disjoint_le (n : ℕ) (i : hC.cell n) : hC.map n i '' closedBall 0 1 ⊆ ⋃ (m : ℕ) (_ : m ≤ n) (j : { j // ¬Disjoint (hC.map n i '' closedBall 0 1) (hC.map m j '' ball 0 1)}), hC.map m j.1 '' closedBall 0 1 := by
--   apply subset_iUnion_of_subset n
--   apply subset_iUnion_of_subset (by rfl)
--   refine subset_iUnion_of_subset ⟨i, ?_⟩ (by rfl)
--   rw [not_disjoint_iff]
--   use map n i 0
--   constructor
--   · apply mem_image_of_mem
--     simp only [mem_closedBall, dist_self, zero_le_one]
--   · apply mem_image_of_mem
--     simp only [mem_ball, dist_self, zero_lt_one]

-- is this needed?
lemma iUnion_cells_inter_compact (A : Set X) (compact : IsCompact A) (I : (n : ℕ) →  Set (cell C n)) :
    ∃ (p : (n : ℕ) → I n → Prop), _root_.Finite (Σ (n : ℕ), {i : I n // p n i}) ∧
    (⋃ (n : ℕ) (i : I n), openCell (C := C) n i) ∩ A =
    (⋃ (n : ℕ) (i : {i : I n // p n i}), openCell (C := C) n i) ∩ A := by
  use fun (n : ℕ) (i : I n) ↦ ¬ Disjoint A (openCell (C := C) n i)
  refine ⟨compact_inter_finite_subset _ compact, ?_⟩
  calc
    (⋃ n, ⋃ (i : ↑(I n)), openCell (C := C) n i) ∩ A =
        (⋃ n, ⋃ (i : I n), openCell (C := C) n i) ∩ C ∩ A := by
      congr
      symm
      simp_rw [Set.inter_eq_left, ← union_openCell]
      apply Set.iUnion_mono''
      intro n x
      rw [mem_iUnion, mem_iUnion]
      intro ⟨i, _⟩
      use i
    _ = (⋃ n, ⋃ (i : I n), openCell (C := C) n i) ∩ (A ∩ C) := by rw [inter_assoc, inter_comm C]
    _ = (⋃ n, ⋃ (i : I n), openCell (C := C) n i) ∩ ((⋃ (x : Σ (m : ℕ),
        {j : cell C m // ¬ Disjoint A (openCell m j)}),
        openCell (C := C) x.1 x.2) ∩ (A ∩ C)) := by
      congrm (⋃ n, ⋃ (i : I n), openCell (C := C) n i) ∩ ?_
      symm
      rw [Set.inter_eq_right]
      exact subset_not_disjoint' A
    _ = (⋃ n, ⋃ (i : { i : I n // ¬Disjoint A (openCell (C := C) n i)}),
        openCell (C := C) n i) ∩ (A ∩ C) := by
      rw [← inter_assoc]
      congrm ?_ ∩ (A ∩ C)
      ext x
      simp only [iUnion_coe_set, TopologicalSpace.Compacts.carrier_eq_coe, mem_inter_iff,
        mem_iUnion, exists_prop, Sigma.exists,
        Subtype.exists, and_iff_right_iff_imp, forall_exists_index, and_imp]
      refine ⟨?_, fun ⟨n, i, memI, notdisjoint, xmem⟩ ↦
        ⟨⟨n, ⟨i, ⟨memI, xmem⟩⟩⟩, ⟨n, ⟨i, ⟨notdisjoint, xmem⟩⟩⟩⟩⟩
      intro ⟨⟨n, i, imem, xmem1⟩, ⟨m, j, hmj, xmem2⟩⟩
      have := @eq_cell_of_not_disjoint _ _ _ _ n i m j (by rw [not_disjoint_iff]; use x)
      rw [Sigma.mk.inj_iff] at this
      rcases this with ⟨eq1, eq2⟩
      subst eq1
      rw [heq_eq_eq] at eq2
      subst eq2
      use n, i
    _ = (⋃ n, ⋃ (i : { i : ↑(I n) // ¬Disjoint A (openCell (C := C) n i) }),
        openCell (C := C) n i) ∩ A := by
      rw [inter_comm A, ← inter_assoc]
      congr
      simp_rw [Set.inter_eq_left, ← union_openCell]
      apply Set.iUnion_mono''
      intro n x
      rw [mem_iUnion, mem_iUnion]
      intro ⟨i, _⟩
      use i

lemma finite_of_compact (compact : IsCompact C) : CWComplex.Finite C := by
  apply finite_of_finite_cells
  have : ∀ m (j : cell C m), ¬Disjoint C (openCell m j) := by
    intro m j
    rw [disjoint_comm, not_disjoint_iff]
    use map m j 0
    refine ⟨map_zero_mem_openCell _ _, ?_⟩
    exact (openCell_subset_complex m j) (map_zero_mem_openCell _ _)
  let f : (Σ m, {j : cell C m // ¬ Disjoint C (openCell m j)}) ≃ Σ m, cell C m :=
    (Equiv.refl _).sigmaCongr (fun m ↦ Equiv.subtypeUnivEquiv (this m))
  rw [← Equiv.finite_iff f]
  exact compact_inter_finite C compact

lemma compact_of_finite (finite : CWComplex.Finite C) : IsCompact C := by
  rw [finite_iff_finite_cells] at finite
  rw [← union (C := C), iUnion_sigma']
  exact isCompact_iUnion (fun ⟨n, i⟩ ↦ isCompact_closedCell)

lemma compact_iff_finite : IsCompact C ↔ Finite C := ⟨finite_of_compact, compact_of_finite⟩
