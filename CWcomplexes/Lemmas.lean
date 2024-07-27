import CWcomplexes.Constructions

open Metric Set

variable {X : Type*} [t : TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]


namespace CWComplex

lemma isClosed_levelaux (n : ℕ∞) : IsClosed (levelaux C n) := (CWComplex_levelaux _ n).isClosed

lemma isClosed_level (n : ℕ∞) : IsClosed (level C n) := isClosed_levelaux _

lemma closed_iff_inter_levelaux_closed (A : Set X) (asubc : A ⊆ C) :
    IsClosed A ↔ ∀ (n : ℕ), IsClosed (A ∩ levelaux C n) := by
  constructor
  · intro closedA n
    exact IsClosed.inter closedA (isClosed_levelaux n)
  · intro h
    rw [closed _ A asubc]
    intro n j
    suffices IsClosed (A ∩ levelaux C (n + 1) ∩ ccell n j) by
      rw [(Set.inter_eq_right.2 (ccell_subset_levelaux _ n j)).symm, ← inter_assoc]
      exact this
    exact IsClosed.inter (h (n + 1)) (isClosed_ccell _)

lemma inter_levelaux_succ_closed_iff_inter_levelaux_closed_and_inter_ccell_closed (A : Set X) :
    IsClosed (A ∩ levelaux C (Nat.succ n)) ↔ IsClosed (A ∩ levelaux C n) ∧
    ∀ (j : cell C n), IsClosed (A ∩ ccell n j) := by
  constructor
  · intro closed
    constructor
    · suffices IsClosed ((A ∩ levelaux C ↑(Nat.succ n)) ∩ levelaux C n) by
        convert this using 1
        rw [inter_assoc,
          inter_eq_right.2 (levelaux_mono C (by norm_cast; exact Nat.le_succ n))]
      exact IsClosed.inter closed (isClosed_levelaux n)
    · intro j
      have : A ∩ levelaux C ↑(Nat.succ n) ⊆ C := by
        apply subset_trans inter_subset_right
        simp_rw [← levelaux_top C]
        exact levelaux_mono _ le_top
      rw [CWComplex.closed _ (A ∩ levelaux C ↑(Nat.succ n)) this] at closed
      replace closed := closed n j
      rw [inter_assoc, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
        inter_eq_right.2 (ccell_subset_levelaux _ n j)] at closed
      exact closed
  · intro ⟨closed1, closed2⟩
    have : A ∩ levelaux C ↑(Nat.succ n) ⊆ C := by
      apply subset_trans inter_subset_right
      simp_rw [← levelaux_top (C := C)]
      exact levelaux_mono _ le_top
    rw [closed _ (A ∩ levelaux C ↑(Nat.succ n)) this]
    intro m j
    induction' m using Nat.case_strong_induction_on with m hm
    · simp [ccell_zero_eq_singleton, isClosed_inter_singleton]
    by_cases msuccltn : Nat.succ m < n
    · have ccellsublevelaux : ccell (Nat.succ m) j ⊆ levelaux C n :=
        subset_trans (ccell_subset_levelaux _ _ _) (levelaux_mono _ (by norm_cast))
      suffices IsClosed (A ∩ levelaux C n ∩ ccell (Nat.succ m) j) by
        convert this using 1
        rw [inter_assoc, inter_assoc]
        congrm A ∩ ?_
        rw [inter_eq_right.2 ccellsublevelaux]
        have : ccell (Nat.succ m) j ⊆ levelaux C (Nat.succ n) :=
          subset_trans ccellsublevelaux (levelaux_mono _ (by norm_cast; exact Nat.le_succ n))
        rw [inter_eq_right.2 this]
      exact IsClosed.inter closed1 (isClosed_ccell _ )
    by_cases msucceqn : Nat.succ m = n
    · subst msucceqn
      rw [inter_assoc, inter_comm (levelaux _ (Nat.succ (Nat.succ m))), ← inter_assoc]
      exact IsClosed.inter (closed2 _) (isClosed_levelaux _)
    have : Nat.succ n ≤ Nat.succ m := by
      push_neg at msuccltn msucceqn
      exact LE.le.lt_of_ne msuccltn msucceqn.symm
    rw [inter_assoc, levelaux_inter_ccell_eq_levelaux_inter_ecell _ (by norm_cast),
       ← inter_assoc]
    exact isClosed_inter_ecell_succ_of_le_isClosed_inter_ccell _ hm _

/- The following is one way of stating that `level 0` is discrete. -/
lemma isDiscrete_level_zero {A : Set X} : IsClosed (A ∩ level C 0) := by
  rw [closed C (A ∩ level C 0) (subset_trans Set.inter_subset_right
    (by simp_rw [← level_top C]; apply level_mono _ le_top))]
  intro n
  induction' n using Nat.case_strong_induction_on with n hn
  · intro j
    have := Set.inter_eq_right.2 (ccell_subset_level _ 0 j)
    norm_cast at this
    rw [inter_assoc, this, ccell_zero_eq_singleton]
    exact isClosed_inter_singleton
  · rw [← Nat.add_one]
    intro j
    rw [inter_assoc, level_inter_ccell_eq_level_inter_ecell _
      (by norm_cast; exact Nat.zero_lt_succ n), ← inter_assoc]
    exact isClosed_inter_ecell_succ_of_le_isClosed_inter_ccell _ hn j

lemma compact_inter_finite (A : t.Compacts) :
  _root_.Finite (Σ (m : ℕ), {j : cell C m // ¬ Disjoint A.1 (ocell m j)}) := by
  by_contra h
  simp only [TopologicalSpace.Compacts.carrier_eq_coe, not_disjoint_iff, SetLike.mem_coe,
    not_finite_iff_infinite] at h
  let p (m : Σ (m : ℕ), { j : cell C m // ∃ x ∈ A, x ∈ ocell m j}) :=
    Classical.choose (m.2).2
  have : Set.InjOn p (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ ocell m j})) := by
    rw [InjOn]
    intro ⟨m, j, hj⟩ _ ⟨n, i, hi⟩ nimem peqp
    have hpj : p ⟨m, j, hj⟩ ∈ ocell m j := by simp_rw [p, (Classical.choose_spec hj).2]
    have hpi : p ⟨m, j, hj⟩ ∈ ocell n i := by simp_rw [peqp, p, (Classical.choose_spec hi).2]
    have : ¬ Disjoint (ocell m j) (ocell n i) := by
      rw [Set.not_disjoint_iff]
      use p ⟨m, j, hj⟩
    have := eq_cell_of_not_disjoint _ this
    simp only [Sigma.mk.inj_iff] at this
    rcases this with ⟨meqn, jeqi⟩
    subst meqn
    simp only [heq_eq_eq] at jeqi
    subst jeqi
    rfl
  have infuniv : Set.Infinite (univ : Set (Σ (m : ℕ),
      { j : cell C m // ∃ x ∈ A, x ∈ ocell m j})) := by
    rw [infinite_univ_iff]
    exact h
  have infpoints := Set.Infinite.image this infuniv
  have subsetsclosed : ∀ (s : Set (p '' (univ : Set (Σ (m : ℕ),
      {j : cell C m // ∃ x ∈ A, x ∈ ocell m j})))), IsClosed (s : Set X) := by
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
        exact ocell_subset_ccell _ _ _ this
      exact subset_trans ssub subc
    rw [closed_iff_inter_levelaux_closed (C := C) s ssubc]
    intro n
    induction' n using Nat.case_strong_induction_on with n hn
    · rw [Nat.cast_zero, levelaux_zero_eq_empty, inter_empty]
      exact isClosed_empty
    rw [inter_levelaux_succ_closed_iff_inter_levelaux_closed_and_inter_ccell_closed _]
    refine ⟨hn n (le_refl _), ?_⟩
    intro j
    simp_rw [← ecell_union_ocell_eq_ccell, inter_union_distrib_left]
    apply IsClosed.union
    · suffices IsClosed (Subtype.val '' s ∩ levelaux C n ∩ ecell n j) by
        simpa only [inter_assoc, inter_eq_right.2 (ecell_subset_levelaux C n j)]
      exact IsClosed.inter (hn n (le_refl _)) (isClosed_ecell _)
    · by_cases empty : Subtype.val '' s ∩ ocell n j = ∅
      · rw [empty]
        exact isClosed_empty
      rw [eq_empty_iff_forall_not_mem, not_forall_not] at empty
      rcases empty with ⟨x, xmems, xmemball⟩
      have ssubp : Subtype.val '' s ⊆
          p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ ocell m j})) := by
        intro a amem
        simp only [mem_image] at amem
        rcases amem with ⟨b, _, beq⟩
        rw [← beq]
        exact b.2
      have : x ∈ (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ ocell m j}))) :=
        ssubp xmems
      simp only [mem_image, p] at this
      rcases this with ⟨⟨y1, y2, yprop⟩, ymem, eq⟩
      have xprop := Classical.choose_spec yprop
      rw [eq] at xprop
      have : ¬ Disjoint (map y1 y2 '' ball 0 1) (map n j '' ball 0 1) := by
        rw [not_disjoint_iff]
        use x
        exact ⟨xprop.2, xmemball⟩
      have := eq_cell_of_not_disjoint C this
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
          have : x' ∈ (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ ocell m j}))) :=
            ssubp x'mems
          simp only [mem_image, p] at this
          rcases this with ⟨⟨y'1, y'2, y'prop⟩, y'mem, eq'⟩
          have x'prop := Classical.choose_spec y'prop
          rw [eq'] at x'prop
          have : ¬ Disjoint (map y'1 y'2 '' ball 0 1) (map n j '' ball 0 1) := by
            rw [not_disjoint_iff]
            use x'
            exact ⟨x'prop.2, x'memball⟩
          have := eq_cell_of_not_disjoint C this
          simp only [Sigma.mk.inj_iff] at this
          rcases this with ⟨h1, h2⟩
          subst y'1
          simp only [heq_eq_eq] at h2
          subst y'2
          rw [← eq, ← eq']
        · simp only [subset_inter_iff, singleton_subset_iff, xmems, xmemball, and_self]
      exact isClosed_singleton
  have discrete : DiscreteTopology
      ↑(p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ ocell m j}))) := by
    simp only [discreteTopology_iff_forall_isClosed]
    intro s
    simp only [instTopologicalSpaceSubtype, isClosed_induced_iff]
    use s
    simp only [Subtype.val_injective, preimage_image_eq, and_true]
    exact subsetsclosed s
  have closed: IsClosed (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ ocell m j}))) := by
    have :=
      subsetsclosed (univ : Set (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ ocell m j}))))
    rw [Subtype.coe_image_univ] at this
    exact this
  have subsetA : (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ ocell m j}))) ⊆ A.1 := by
    intro x xmem
    simp only [mem_image, image_univ, mem_range, Sigma.exists, Subtype.exists, p] at xmem
    rcases xmem with ⟨n, j, hj, hjj⟩
    have := Classical.choose_spec hj
    rw [← hjj]
    exact this.1
  have compact : IsCompact (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ ocell m j}))) :=
    IsCompact.of_isClosed_subset A.2 closed subsetA
  have finite : Set.Finite (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ ocell m j}))) :=
    IsCompact.finite compact discrete
  contradiction

lemma compact_inter_finite_subset (A : t.Compacts) {I : (n : ℕ) → Set (cell C n)} :
    _root_.Finite (Σ (m : ℕ), {j : I m // ¬ Disjoint A.1 (ocell (C := C) m j)}) := by
  let f := fun (x : Σ (m : ℕ), {j : I m // ¬ Disjoint A.1 (ocell (C := C) m j)}) ↦
    (⟨x.1, ⟨x.2.1, x.2.2⟩⟩ : Σ (m : ℕ), {j : cell C m // ¬ Disjoint A.1 (ocell m j)})
  apply @Finite.of_injective _ _ (compact_inter_finite A) f
  unfold Function.Injective
  intro ⟨x1, x2, x3⟩ ⟨y1, y2, y3⟩ eq
  simp only [TopologicalSpace.Compacts.carrier_eq_coe, Sigma.mk.inj_iff, f] at eq
  rcases eq with ⟨rfl, eq⟩
  simp only [heq_eq_eq, Subtype.mk.injEq, Subtype.val_inj] at eq
  simp_rw [eq]

lemma compact_inter_finite' (A : t.Compacts) :
    _root_.Finite {x : Σ (n : ℕ), cell C n // ¬Disjoint A.1 (ocell x.fst x.snd)} := by
  let f := fun (x : (Σ (m : ℕ), {j : cell C m // ¬ Disjoint A.1 (ocell m j)})) ↦
    (⟨⟨x.1, x.2.1⟩, x.2.2⟩ : { x : Σ (n : ℕ), cell C n // ¬Disjoint A.1 (ocell x.fst x.snd)})
  apply @Finite.of_surjective _ _ (compact_inter_finite A) f
  unfold Function.Surjective
  intro x
  use ⟨x.1.1, ⟨x.1.2, x.2⟩⟩

lemma compact_inter_finite_subset' (A : t.Compacts) {I : (n : ℕ) → Set (cell C n)} :
    _root_.Finite {x : Σ (n : ℕ), I n // ¬Disjoint A.1 (ocell (C := C) x.fst x.snd)} := by
  let f := fun (x : {x : Σ (n : ℕ), I n // ¬Disjoint A.1 (ocell (C := C) x.fst x.snd)}) ↦
    (⟨⟨x.1.1, x.1.2⟩, x.2⟩ : {x : Σ (n : ℕ), cell C n // ¬Disjoint A.1 (ocell x.fst x.snd)})
  apply @Finite.of_injective _ _ (compact_inter_finite' A) f
  unfold Function.Injective
  intro ⟨⟨x1, x2⟩, x3⟩ ⟨⟨y1, y2⟩, y3⟩ eq
  simp only [TopologicalSpace.Compacts.carrier_eq_coe, Subtype.mk.injEq, Sigma.mk.inj_iff, f] at eq
  rcases eq with ⟨rfl, eq⟩
  simp only [heq_eq_eq, Subtype.mk.injEq, Subtype.val_inj] at eq
  simp_rw [eq]

lemma subset_not_disjoint (A : Set X) : A ∩ C ⊆ ⋃ (x : Σ (m : ℕ),
    {j : cell C m // ¬ Disjoint A (ocell m j)}), ccell (C := C) x.1 x.2 := by
  intro x ⟨xmem1, xmem2⟩
  simp only [mem_iUnion]
  simp only [← union_ocell, mem_iUnion] at xmem2
  rcases xmem2 with ⟨m, j, hmj⟩
  use ⟨m, j, not_disjoint_iff.2 ⟨x, xmem1, hmj⟩⟩
  exact ocell_subset_ccell _ _ _ hmj

lemma subset_not_disjoint' (A : Set X) : A ∩ C ⊆ ⋃ (x : Σ (m : ℕ),
    {j : cell C m // ¬ Disjoint A (ocell m j)}), ocell (C := C) x.1 x.2 := by
  intro x ⟨xmem1, xmem2⟩
  simp only [mem_iUnion]
  simp only [← union_ocell, mem_iUnion] at xmem2
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
    (⋃ (n : ℕ) (i : I n), ocell (C := C) n i) ∩ A.1 =
    (⋃ (n : ℕ) (i : {i : I n // p n i}), ocell (C := C) n i) ∩ A.1 := by
  use fun (n : ℕ) (i : I n) ↦ ¬ Disjoint A.1 (ocell (C := C) n i)
  refine ⟨compact_inter_finite_subset _, ?_⟩
  calc
    (⋃ n, ⋃ (i : ↑(I n)), ocell (C := C) n i) ∩ A.1 =
        (⋃ n, ⋃ (i : I n), ocell (C := C) n i) ∩ C ∩ A.1 := by
      congr
      symm
      simp_rw [Set.inter_eq_left, ← union_ocell]
      apply Set.iUnion_mono''
      intro n x
      rw [mem_iUnion, mem_iUnion]
      intro ⟨i, _⟩
      use i
    _ = (⋃ n, ⋃ (i : I n), ocell (C := C) n i) ∩ (A.1 ∩ C) := by rw [inter_assoc, inter_comm C]
    _ = (⋃ n, ⋃ (i : I n), ocell (C := C) n i) ∩ ((⋃ (x : Σ (m : ℕ),
        {j : cell C m // ¬ Disjoint A.1 (ocell m j)}),
        ocell (C := C) x.1 x.2) ∩ (A.1 ∩ C)) := by
      congrm (⋃ n, ⋃ (i : I n), ocell (C := C) n i) ∩ ?_
      symm
      rw [Set.inter_eq_right]
      exact subset_not_disjoint' A.1
    _ = (⋃ n, ⋃ (i : { i : I n // ¬Disjoint A.carrier (ocell (C := C) n i)}),
        ocell (C := C) n i) ∩ (A.1 ∩ C) := by
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
    _ = (⋃ n, ⋃ (i : { i : ↑(I n) // ¬Disjoint A.carrier (ocell (C := C) n i) }),
        ocell (C := C) n i) ∩ A.1 := by
      rw [inter_comm A.carrier, ← inter_assoc]
      congr
      simp_rw [Set.inter_eq_left, ← union_ocell]
      apply Set.iUnion_mono''
      intro n x
      rw [mem_iUnion, mem_iUnion]
      intro ⟨i, _⟩
      use i

lemma finite_of_compact (compact : IsCompact C) : CWComplex.Finite C := by
  apply finite_of_finite_cells
  have : ∀ m (j : cell C m), ¬Disjoint C (ocell m j) := by
    intro m j
    rw [disjoint_comm, not_disjoint_iff]
    use map m j 0
    have zeromem : map m j 0 ∈ ocell m j := by
      apply mem_image_of_mem
      simp only [mem_ball, dist_self, zero_lt_one]
    refine ⟨zeromem, ?_⟩
    exact (ocell_subset_complex _ m j) zeromem
  let f : (Σ m, {j : cell C m // ¬ Disjoint C (ocell m j)}) ≃ Σ m, cell C m := {
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
  exact isCompact_ccell C

lemma compact_iff_finite : IsCompact C ↔ Finite C := ⟨finite_of_compact, compact_of_finite⟩
