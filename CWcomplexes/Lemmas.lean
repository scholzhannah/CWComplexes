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

lemma compact_inter_finite (A : t.Compacts) :
  _root_.Finite (Σ (m : ℕ), {j : cell C m // ¬ Disjoint A.1 (openCell m j)}) := by
  by_contra h
  simp only [TopologicalSpace.Compacts.carrier_eq_coe, not_disjoint_iff, SetLike.mem_coe,
    not_finite_iff_infinite] at h
  let p (m : Σ (m : ℕ), { j : cell C m // ∃ x ∈ A, x ∈ openCell m j}) :=
    Classical.choose (m.2).2
  have : Set.InjOn p (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ openCell m j})) := by
    rw [InjOn]
    intro ⟨m, j, hj⟩ _ ⟨n, i, hi⟩ nimem peqp
    have hpj : p ⟨m, j, hj⟩ ∈ openCell m j := by simp_rw [p, (Classical.choose_spec hj).2]
    have hpi : p ⟨m, j, hj⟩ ∈ openCell n i := by simp_rw [peqp, p, (Classical.choose_spec hi).2]
    have : ¬ Disjoint (openCell m j) (openCell n i) := by
      rw [Set.not_disjoint_iff]
      use p ⟨m, j, hj⟩
    have := eq_cell_of_not_disjoint this
    simp only [Sigma.mk.inj_iff] at this
    rcases this with ⟨meqn, jeqi⟩
    subst meqn
    simp only [heq_eq_eq] at jeqi
    subst jeqi
    rfl
  have infuniv : Set.Infinite (univ : Set (Σ (m : ℕ),
      { j : cell C m // ∃ x ∈ A, x ∈ openCell m j})) := by
    rw [infinite_univ_iff]
    exact h
  have infpoints := Set.Infinite.image this infuniv
  have subsetsclosed : ∀ (s : Set (p '' (univ : Set (Σ (m : ℕ),
      {j : cell C m // ∃ x ∈ A, x ∈ openCell m j})))), IsClosed (s : Set X) := by
    intro s
    have ssubc : ↑↑s ⊆ ↑C := by
      have ssub := Subtype.coe_image_subset ↑(p '' univ) s
      have subc : p '' univ ⊆ C := by
        intro x xmem
        simp only [image_univ, mem_range, Sigma.exists, Subtype.exists] at xmem
        rcases xmem with ⟨m, j, h', h⟩
        simp only [← union, mem_iUnion]
        use m
        use j
        simp only [p] at h
        have := (Classical.choose_spec h').2
        rw [h] at this
        exact openCell_subset_closedCell _ _ this
      exact subset_trans ssub subc
    apply induction_isClosed_levelaux ssubc
    intro n hn j
    simp_rw [← cellFrontier_union_openCell_eq_closedCell, inter_union_distrib_left]
    apply IsClosed.union
    · suffices IsClosed (Subtype.val '' s ∩ levelaux C n ∩ cellFrontier n j) by
        simpa only [inter_assoc, inter_eq_right.2 (cellFrontier_subset_levelaux n j)]
      exact (hn n (le_refl _)).inter isClosed_cellFrontier
    · by_cases empty : Subtype.val '' s ∩ openCell n j = ∅
      · rw [empty]
        exact isClosed_empty
      rw [eq_empty_iff_forall_not_mem, not_forall_not] at empty
      rcases empty with ⟨x, xmems, xmemball⟩
      have ssubp : Subtype.val '' s ⊆
          p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ openCell m j})) := by
        intro a amem
        simp only [mem_image] at amem
        rcases amem with ⟨b, _, beq⟩
        rw [← beq]
        exact b.2
      have : x ∈ (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ openCell m j}))) :=
        ssubp xmems
      simp only [mem_image, p] at this
      rcases this with ⟨⟨y1, y2, yprop⟩, ymem, eq⟩
      have xprop := Classical.choose_spec yprop
      rw [eq] at xprop
      have : ¬ Disjoint (map y1 y2 '' ball 0 1) (map n j '' ball 0 1) := by
        rw [not_disjoint_iff]
        use x
        exact ⟨xprop.2, xmemball⟩
      have := eq_cell_of_not_disjoint this
      simp only [Sigma.mk.inj_iff] at this
      rcases this with ⟨h1, h2⟩
      subst y1
      simp only [heq_eq_eq] at h2
      subst y2
      suffices IsClosed {x} by
        convert this
        apply subset_antisymm
        · intro x' ⟨x'mems, x'memball⟩
          simp only [mem_singleton_iff]
          have : x' ∈ (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ openCell m j}))) :=
            ssubp x'mems
          simp only [mem_image, p] at this
          rcases this with ⟨⟨y'1, y'2, y'prop⟩, y'mem, eq'⟩
          have x'prop := Classical.choose_spec y'prop
          rw [eq'] at x'prop
          have : ¬ Disjoint (map y'1 y'2 '' ball 0 1) (map n j '' ball 0 1) := by
            rw [not_disjoint_iff]
            use x'
            exact ⟨x'prop.2, x'memball⟩
          have := eq_cell_of_not_disjoint this
          simp only [Sigma.mk.inj_iff] at this
          rcases this with ⟨h1, h2⟩
          subst y'1
          simp only [heq_eq_eq] at h2
          subst y'2
          rw [← eq, ← eq']
        · simp only [subset_inter_iff, singleton_subset_iff, xmems, xmemball, and_self]
      exact isClosed_singleton
  have discrete : DiscreteTopology
      ↑(p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ openCell m j}))) := by
    simp only [discreteTopology_iff_forall_isClosed]
    intro s
    simp only [instTopologicalSpaceSubtype, isClosed_induced_iff]
    use s
    simp only [Subtype.val_injective, preimage_image_eq, and_true]
    exact subsetsclosed s
  have closed: IsClosed (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ openCell m j}))) := by
    have :=
      subsetsclosed (univ : Set (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ openCell m j}))))
    rw [Subtype.coe_image_univ] at this
    exact this
  have subsetA : (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ openCell m j}))) ⊆ A.1 := by
    intro x xmem
    simp only [mem_image, image_univ, mem_range, Sigma.exists, Subtype.exists, p] at xmem
    rcases xmem with ⟨n, j, hj, hjj⟩
    have := Classical.choose_spec hj
    rw [← hjj]
    exact this.1
  have compact : IsCompact (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ openCell m j}))) :=
    IsCompact.of_isClosed_subset A.2 closed subsetA
  have finite : Set.Finite (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ openCell m j}))) :=
    IsCompact.finite compact discrete
  contradiction

lemma compact_inter_finite_subset (A : t.Compacts) {I : (n : ℕ) → Set (cell C n)} :
    _root_.Finite (Σ (m : ℕ), {j : I m // ¬ Disjoint A.1 (openCell (C := C) m j)}) := by
  let f := fun (x : Σ (m : ℕ), {j : I m // ¬ Disjoint A.1 (openCell (C := C) m j)}) ↦
    (⟨x.1, ⟨x.2.1, x.2.2⟩⟩ : Σ (m : ℕ), {j : cell C m // ¬ Disjoint A.1 (openCell m j)})
  apply @Finite.of_injective _ _ (compact_inter_finite A) f
  unfold Function.Injective
  intro ⟨x1, x2, x3⟩ ⟨y1, y2, y3⟩ eq
  simp only [TopologicalSpace.Compacts.carrier_eq_coe, Sigma.mk.inj_iff, f] at eq
  rcases eq with ⟨rfl, eq⟩
  simp only [heq_eq_eq, Subtype.mk.injEq, Subtype.val_inj] at eq
  simp_rw [eq]

lemma compact_inter_finite' (A : t.Compacts) :
    _root_.Finite {x : Σ (n : ℕ), cell C n // ¬Disjoint A.1 (openCell x.fst x.snd)} := by
  let f := fun (x : (Σ (m : ℕ), {j : cell C m // ¬ Disjoint A.1 (openCell m j)})) ↦
    (⟨⟨x.1, x.2.1⟩, x.2.2⟩ : { x : Σ (n : ℕ), cell C n // ¬Disjoint A.1 (openCell x.fst x.snd)})
  apply @Finite.of_surjective _ _ (compact_inter_finite A) f
  unfold Function.Surjective
  intro x
  use ⟨x.1.1, ⟨x.1.2, x.2⟩⟩

lemma compact_inter_finite_subset' (A : t.Compacts) {I : (n : ℕ) → Set (cell C n)} :
    _root_.Finite {x : Σ (n : ℕ), I n // ¬Disjoint A.1 (openCell (C := C) x.fst x.snd)} := by
  let f := fun (x : {x : Σ (n : ℕ), I n // ¬Disjoint A.1 (openCell (C := C) x.fst x.snd)}) ↦
    (⟨⟨x.1.1, x.1.2⟩, x.2⟩ : {x : Σ (n : ℕ), cell C n // ¬Disjoint A.1 (openCell x.fst x.snd)})
  apply @Finite.of_injective _ _ (compact_inter_finite' A) f
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

lemma iUnion_cells_inter_compact (A : t.Compacts) (I : (n : ℕ) →  Set (cell C n)) :
    ∃ (p : (n : ℕ) → I n → Prop), _root_.Finite (Σ (n : ℕ), {i : I n // p n i}) ∧
    (⋃ (n : ℕ) (i : I n), openCell (C := C) n i) ∩ A.1 =
    (⋃ (n : ℕ) (i : {i : I n // p n i}), openCell (C := C) n i) ∩ A.1 := by
  use fun (n : ℕ) (i : I n) ↦ ¬ Disjoint A.1 (openCell (C := C) n i)
  refine ⟨compact_inter_finite_subset _, ?_⟩
  calc
    (⋃ n, ⋃ (i : ↑(I n)), openCell (C := C) n i) ∩ A.1 =
        (⋃ n, ⋃ (i : I n), openCell (C := C) n i) ∩ C ∩ A.1 := by
      congr
      symm
      simp_rw [Set.inter_eq_left, ← union_openCell]
      apply Set.iUnion_mono''
      intro n x
      rw [mem_iUnion, mem_iUnion]
      intro ⟨i, _⟩
      use i
    _ = (⋃ n, ⋃ (i : I n), openCell (C := C) n i) ∩ (A.1 ∩ C) := by rw [inter_assoc, inter_comm C]
    _ = (⋃ n, ⋃ (i : I n), openCell (C := C) n i) ∩ ((⋃ (x : Σ (m : ℕ),
        {j : cell C m // ¬ Disjoint A.1 (openCell m j)}),
        openCell (C := C) x.1 x.2) ∩ (A.1 ∩ C)) := by
      congrm (⋃ n, ⋃ (i : I n), openCell (C := C) n i) ∩ ?_
      symm
      rw [Set.inter_eq_right]
      exact subset_not_disjoint' A.1
    _ = (⋃ n, ⋃ (i : { i : I n // ¬Disjoint A.carrier (openCell (C := C) n i)}),
        openCell (C := C) n i) ∩ (A.1 ∩ C) := by
      rw [← inter_assoc]
      congrm ?_ ∩ (A.1 ∩ C)
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
    _ = (⋃ n, ⋃ (i : { i : ↑(I n) // ¬Disjoint A.carrier (openCell (C := C) n i) }),
        openCell (C := C) n i) ∩ A.1 := by
      rw [inter_comm A.carrier, ← inter_assoc]
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
    have zeromem : map m j 0 ∈ openCell m j := by
      apply mem_image_of_mem
      simp only [mem_ball, dist_self, zero_lt_one]
    refine ⟨zeromem, ?_⟩
    exact (openCell_subset_complex m j) zeromem
  let f : (Σ m, {j : cell C m // ¬ Disjoint C (openCell m j)}) ≃ Σ m, cell C m := {
    toFun := fun ⟨m, j, _⟩ ↦ ⟨m, j⟩
    invFun := fun ⟨m, j⟩ ↦ ⟨m, j, this m j⟩
    left_inv := by simp only [Function.LeftInverse, Subtype.coe_eta, Sigma.eta, implies_true]
    right_inv := by simp only [Function.RightInverse, Function.LeftInverse, Sigma.eta, implies_true]
  }
  rw [← Equiv.finite_iff f]
  exact compact_inter_finite ⟨C, compact⟩

lemma compact_of_finite (finite : CWComplex.Finite C) : IsCompact C := by
  rw [finite_iff_finite_cells] at finite
  rw [← union (C := C), Set.iUnion_sigma']
  apply isCompact_iUnion
  intro ⟨n, i⟩
  exact isCompact_closedCell

lemma compact_iff_finite : IsCompact C ↔ Finite C := ⟨finite_of_compact, compact_of_finite⟩
