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
    rw [closed A asubc]
    intro n j
    have : map n j '' closedBall 0 1 = levelaux C (n + 1) ∩ map n j '' closedBall 0 1 := by
      exact (Set.inter_eq_right.2 (map_closedBall_subset_levelaux _ n j)).symm
    rw [this, ← inter_assoc]
    exact IsClosed.inter (h (n + 1)) (isClosed_map_closedBall _ n j)

lemma inter_levelaux_succ_closed_iff_inter_levelaux_closed_and_inter_closedBall_closed (A : Set X) :
    IsClosed (A ∩ levelaux C (Nat.succ n)) ↔ IsClosed (A ∩ levelaux C n) ∧
    ∀ (j : cell C n), IsClosed (A ∩ map n j '' closedBall 0 1) := by
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
        simp_rw [← levelaux_top (C := C)] -- why does taking away (C := C) completely kill lean?
        exact levelaux_mono _ le_top
      rw [CWComplex.closed (A ∩ levelaux C ↑(Nat.succ n)) this] at closed
      replace closed := closed n j
      rw [inter_assoc, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
        inter_eq_right.2 (map_closedBall_subset_levelaux _ n j)] at closed
      exact closed
  · intro ⟨closed1, closed2⟩
    have : A ∩ levelaux C ↑(Nat.succ n) ⊆ C := by
      apply subset_trans inter_subset_right
      simp_rw [← levelaux_top (C := C)]
      exact levelaux_mono _ le_top
    rw [closed (A ∩ levelaux C ↑(Nat.succ n)) this]
    intro m j
    induction' m using Nat.case_strong_induction_on with m hm
    · simp [Matrix.empty_eq, isClosed_inter_singleton]
    by_cases msuccltn : Nat.succ m < n
    · have : map (Nat.succ m) j '' closedBall 0 1 ⊆ levelaux C n := by
        refine subset_trans (map_closedBall_subset_levelaux _ _ _) (levelaux_mono _ ?_)
        norm_cast
      have : A ∩ levelaux C ↑(Nat.succ n) ∩ map (Nat.succ m) j '' closedBall 0 1 =
          A ∩ levelaux C n ∩ map (Nat.succ m) j '' closedBall 0 1 := by
        rw [inter_assoc, inter_assoc]
        congrm A ∩ ?_
        rw [inter_eq_right.2 this]
        have : map (Nat.succ m) j '' closedBall 0 1 ⊆ levelaux C (Nat.succ n) :=
          subset_trans this (levelaux_mono _ (by norm_cast; exact Nat.le_succ n))
        rw [inter_eq_right.2 this]
      rw [this]
      exact IsClosed.inter closed1 (isClosed_map_closedBall _ _ _)
    by_cases msucceqn : Nat.succ m = n
    · subst msucceqn
      rw [inter_assoc, inter_comm (levelaux _ (Nat.succ (Nat.succ m))), ← inter_assoc]
      exact IsClosed.inter (closed2 _) (isClosed_levelaux _)
    have : Nat.succ n ≤ Nat.succ m := by
      push_neg at msuccltn msucceqn
      exact LE.le.lt_of_ne msuccltn msucceqn.symm
    rw [inter_assoc, levelaux_inter_image_closedBall_eq_levelaux_inter_image_sphere _ (by norm_cast),
       ← inter_assoc]
    exact isClosed_inter_sphere_succ_of_le_isClosed_inter_closedBall _ hm _

/- The following is one way of stating that `level 0` is discrete. -/
lemma isDiscrete_level_zero {A : Set X} : IsClosed (A ∩ level C 0) := by
  rw [closed (C := C) (A ∩ level C 0) (subset_trans Set.inter_subset_right
    (by simp_rw [← level_top C]; apply level_mono _ le_top))]
  intro n
  induction' n using Nat.case_strong_induction_on with n hn
  · intro j
    have := Set.inter_eq_right.2 (map_closedBall_subset_level _ 0 j)
    norm_cast at this
    rw [inter_assoc, this]
    have : map 0 j '' closedBall 0 1 = {map 0 j ![]} := by
      ext x
      constructor
      · intro h
        rw [mem_image] at h
        rcases h with ⟨y, _, mapy⟩
        have : y = ![] := by simp [Matrix.empty_eq]
        rw [this] at mapy
        simp only [mapy, mem_singleton_iff]
      · intro h
        rw [h]
        apply Set.mem_image_of_mem
        simp only [Matrix.zero_empty, mem_closedBall, dist_self, zero_le_one]
    rw [this]
    by_cases h : {map 0 j ![]} ⊆ A
    · rw [inter_eq_right.2 h]
      exact isClosed_singleton
    · simp at h
      have : A ∩ {map 0 j ![]} = ∅ := by
        simp only [inter_singleton_eq_empty, h, not_false_eq_true]
      rw [this]
      exact isClosed_empty
  · rw [← Nat.add_one]
    intro j
    rw [inter_assoc, level_inter_image_closedBall_eq_level_inter_image_sphere _
      (by norm_cast; exact Nat.zero_lt_succ n), ← inter_assoc]
    exact isClosed_inter_sphere_succ_of_le_isClosed_inter_closedBall _ hn j

lemma compact_inter_finite (A : t.Compacts) :
  _root_.Finite (Σ (m : ℕ), {j : cell C m // ¬ Disjoint A.1 (map m j '' ball 0 1)}) := by
  by_contra h
  simp only [TopologicalSpace.Compacts.carrier_eq_coe, not_disjoint_iff, SetLike.mem_coe,
    not_finite_iff_infinite] at h
  let p (m : Σ (m : ℕ), { j : cell C m // ∃ x ∈ A, x ∈ map m j '' ball 0 1}) :=
    Classical.choose (m.2).2
  have : Set.InjOn p (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ map m j '' ball 0 1 })) := by
    rw [InjOn]
    intro ⟨m, j, hj⟩ _ ⟨n, i, hi⟩ nimem peqp
    have hpj : p ⟨m, j, hj⟩ ∈ map m j '' ball 0 1 := by simp only [p, (Classical.choose_spec hj).2]
    have hpi : p ⟨m, j, hj⟩ ∈ map n i '' ball 0 1 := by
      rw [peqp]
      simp only [p, (Classical.choose_spec hi).2]
    have : ¬ Disjoint (map m j '' ball 0 1) (map n i '' ball 0 1) := by
      rw [Set.not_disjoint_iff]
      use p ⟨m, j, hj⟩
    have := not_disjoint_equal _ this
    simp only [Sigma.mk.inj_iff] at this
    rcases this with ⟨meqn, jeqi⟩
    subst meqn
    simp only [heq_eq_eq] at jeqi
    subst jeqi
    rfl
  have infuniv : Set.Infinite (univ : Set (Σ (m : ℕ),
      { j : cell C m // ∃ x ∈ A, x ∈ map m j '' ball 0 1 })) := by
    rw [infinite_univ_iff]
    exact h
  have infpoints := Set.Infinite.image this infuniv
  have subsetsclosed : ∀ (s : Set (p '' (univ : Set (Σ (m : ℕ),
      {j : cell C m // ∃ x ∈ A, x ∈ map m j '' ball 0 1 })))), IsClosed (s : Set X) := by
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
        exact map_ball_subset_map_closedball _ this
      exact subset_trans ssub subc
    rw [closed_iff_inter_levelaux_closed (C := C) s ssubc]
    intro n
    induction' n using Nat.case_strong_induction_on with n hn
    · rw [Nat.cast_zero, levelaux_zero_eq_empty, inter_empty]
      exact isClosed_empty
    rw [inter_levelaux_succ_closed_iff_inter_levelaux_closed_and_inter_closedBall_closed _]
    constructor
    · exact hn n (le_refl _)
    intro j
    simp_rw [← Metric.sphere_union_ball, image_union, inter_union_distrib_left]
    apply IsClosed.union
    · have sub : map n j '' sphere 0 1 ⊆ levelaux C n := by
        rcases mapsto n j with ⟨I, hI⟩
        rw [mapsTo'] at hI
        apply subset_trans hI
        intro x xmem
        unfold levelaux
        simp only [mem_iUnion] at xmem ⊢
        rcases xmem with ⟨m, mlt, i, _, xmem⟩
        use m, (by norm_num; exact mlt), i
      suffices IsClosed (Subtype.val '' s ∩ levelaux C n ∩ map n j '' sphere 0 1) by
        simpa only [inter_assoc, inter_eq_right.2 sub]
      exact IsClosed.inter (hn n (le_refl _)) (isClosed_map_sphere _)
    · by_cases empty : Subtype.val '' s ∩ map n j '' ball 0 1 = ∅
      · rw [empty]
        exact isClosed_empty
      rw [eq_empty_iff_forall_not_mem, not_forall_not] at empty
      rcases empty with ⟨x, xmems, xmemball⟩
      have ssubp : Subtype.val '' s ⊆
          p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ map m j '' ball 0 1 })) := by
        intro a amem
        simp only [mem_image] at amem
        rcases amem with ⟨b, _, beq⟩
        rw [← beq]
        exact b.2
      have : x ∈ (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ map m j '' ball 0 1 }))) :=
        ssubp xmems
      simp only [mem_image, p] at this
      rcases this with ⟨⟨y1, y2, yprop⟩, ymem, eq⟩
      have xprop := Classical.choose_spec yprop
      rw [eq] at xprop
      have : ¬ Disjoint (map y1 y2 '' ball 0 1) (map n j '' ball 0 1) := by
        rw [not_disjoint_iff]
        use x
        exact ⟨xprop.2, xmemball⟩
      have := not_disjoint_equal C this
      simp at this
      rcases this with ⟨h1, h2⟩
      subst y1
      simp at h2
      subst y2
      have : Subtype.val '' s ∩ map n j '' ball 0 1 = {x} := by
        apply subset_antisymm
        · intro x' ⟨x'mems, x'memball⟩
          simp only [mem_singleton_iff]
          have : x' ∈ (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ map m j '' ball 0 1 }))) :=
            ssubp x'mems
          simp only [mem_image, p] at this
          rcases this with ⟨⟨y'1, y'2, y'prop⟩, y'mem, eq'⟩
          have x'prop := Classical.choose_spec y'prop
          rw [eq'] at x'prop
          have : ¬ Disjoint (map y'1 y'2 '' ball 0 1) (map n j '' ball 0 1) := by
            rw [not_disjoint_iff]
            use x'
            exact ⟨x'prop.2, x'memball⟩
          have := not_disjoint_equal C this
          simp at this
          rcases this with ⟨h1, h2⟩
          subst y'1
          simp at h2
          subst y'2
          rw [← eq, ← eq']
        · simp only [subset_inter_iff, singleton_subset_iff, xmems, xmemball, and_self]
      rw [this]
      exact isClosed_singleton
  have discrete : DiscreteTopology ↑(p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ map m j '' ball 0 1 }))) := by
    simp only [discreteTopology_iff_forall_isClosed]
    intro s
    simp only [instTopologicalSpaceSubtype, isClosed_induced_iff]
    use s
    simp only [Subtype.val_injective, preimage_image_eq, and_true]
    exact subsetsclosed s
  have closed: IsClosed (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ map m j '' ball 0 1 }))) := by
    have := subsetsclosed (univ : Set (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ map m j '' ball 0 1 }))))
    rw [Subtype.coe_image_univ] at this
    exact this
  have subsetA : (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ map m j '' ball 0 1 }))) ⊆ A.1 := by
    intro x xmem
    simp only [mem_image, image_univ, mem_range, Sigma.exists, Subtype.exists, p] at xmem
    rcases xmem with ⟨n, j, hj, hjj⟩
    have := Classical.choose_spec hj
    rw [← hjj]
    exact this.1
  have compact : IsCompact (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ map m j '' ball 0 1 }))) := by
    exact IsCompact.of_isClosed_subset A.2 closed subsetA
  have finite : Set.Finite (p '' (univ : Set (Σ (m : ℕ), { j // ∃ x ∈ A, x ∈ map m j '' ball 0 1 }))) := by
    exact IsCompact.finite compact discrete
  contradiction

lemma compact_inter_finite_subset (A : t.Compacts) {I : (n : ℕ) → Set (cell C n)} :
    _root_.Finite (Σ (m : ℕ), {j : I m // ¬ Disjoint A.1 (map (C := C) m j '' ball 0 1)}) := by
  let f := fun (x : Σ (m : ℕ), {j : I m // ¬ Disjoint A.1 (map (C := C) m j '' ball 0 1)}) ↦
    (⟨x.1, ⟨x.2.1, x.2.2⟩⟩ : Σ (m : ℕ), {j : cell C m // ¬ Disjoint A.1 (map m j '' ball 0 1)})
  apply @Finite.of_injective _ _ (compact_inter_finite A) f
  unfold Function.Injective
  intro ⟨x1, x2, x3⟩ ⟨y1, y2, y3⟩ eq
  simp [f] at eq
  rcases eq with ⟨rfl, eq⟩
  simp only [heq_eq_eq, Subtype.mk.injEq, Subtype.val_inj] at eq
  simp_rw [eq]

lemma compact_inter_finite' (A : t.Compacts) :
    _root_.Finite {x : Σ (n : ℕ), cell C n // ¬Disjoint A.1 (map x.fst x.snd '' ball 0 1)} := by
  let f := fun (x : (Σ (m : ℕ), {j : cell C m // ¬ Disjoint A.1 (map m j '' ball 0 1)})) ↦
    (⟨⟨x.1, x.2.1⟩, x.2.2⟩ : { x : Σ (n : ℕ), cell C n // ¬Disjoint A.1 (map x.fst x.snd '' ball 0 1)})
  apply @Finite.of_surjective _ _ (compact_inter_finite A) f
  unfold Function.Surjective
  intro x
  use ⟨x.1.1, ⟨x.1.2, x.2⟩⟩

lemma compact_inter_finite_subset' (A : t.Compacts) {I : (n : ℕ) → Set (cell C n)} :
    _root_.Finite {x : Σ (n : ℕ), I n // ¬Disjoint A.1 (map (C := C) x.fst x.snd '' ball 0 1)} := by
  let f := fun (x : {x : Σ (n : ℕ), I n // ¬Disjoint A.1 (map (C := C) x.fst x.snd '' ball 0 1)}) ↦
    (⟨⟨x.1.1, x.1.2⟩, x.2⟩ : {x : Σ (n : ℕ), cell C n // ¬Disjoint A.1 (map x.fst x.snd '' ball 0 1)})
  apply @Finite.of_injective _ _ (compact_inter_finite' A) f
  unfold Function.Injective
  intro ⟨⟨x1, x2⟩, x3⟩ ⟨⟨y1, y2⟩, y3⟩ eq
  simp only [TopologicalSpace.Compacts.carrier_eq_coe, Subtype.mk.injEq, Sigma.mk.inj_iff, f] at eq
  rcases eq with ⟨rfl, eq⟩
  simp only [heq_eq_eq, Subtype.mk.injEq, Subtype.val_inj] at eq
  simp_rw [eq]

lemma subset_not_disjoint (A : Set X) : A ∩ C ⊆ ⋃ (x : Σ (m : ℕ),
    {j : cell C m // ¬ Disjoint A (map m j '' ball 0 1)}), map (C := C) x.1 x.2 '' closedBall 0 1 := by
  intro x ⟨xmem1, xmem2⟩
  simp only [mem_iUnion]
  simp only [← union', mem_iUnion] at xmem2
  rcases xmem2 with ⟨m, j, hmj⟩
  use ⟨m, j, not_disjoint_iff.2 ⟨x, xmem1, hmj⟩⟩
  exact map_ball_subset_map_closedball _ hmj

lemma subset_not_disjoint' (A : Set X) : A ∩ C ⊆ ⋃ (x : Σ (m : ℕ),
    {j : cell C m // ¬ Disjoint A (map m j '' ball 0 1)}), map (C := C) x.1 x.2 '' ball 0 1 := by
  intro x ⟨xmem1, xmem2⟩
  simp only [mem_iUnion]
  simp only [← union', mem_iUnion] at xmem2
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
    (⋃ (n : ℕ) (i : I n), map (C := C) n i '' ball 0 1) ∩ A.1 =
    (⋃ (n : ℕ) (i : {i : I n // p n i}), map (C := C) n i '' ball 0 1) ∩ A.1 := by
  use fun (n : ℕ) (i : I n) ↦ ¬ Disjoint A.1 (map (C := C) n i '' ball 0 1)
  refine ⟨compact_inter_finite_subset _, ?_⟩
  calc
    (⋃ n, ⋃ (i : ↑(I n)), map (C := C) n i '' ball 0 1) ∩ A.1 =
        (⋃ n, ⋃ (i : I n), map (C := C) n i '' ball 0 1) ∩ C ∩ A.1 := by
      congr
      symm
      simp_rw [Set.inter_eq_left, ← union']
      apply Set.iUnion_mono''
      intro n x
      rw [mem_iUnion, mem_iUnion]
      intro ⟨i, _⟩
      use i
    _ = (⋃ n, ⋃ (i : I n), map (C := C) n i '' ball 0 1) ∩ (A.1 ∩ C) := by
      rw [inter_assoc, inter_comm C]
     _ = (⋃ n, ⋃ (i : I n), map (C := C) n i '' ball 0 1) ∩ ((⋃ (x : Σ (m : ℕ),
        {j : cell C m // ¬ Disjoint A.1 (map m j '' ball 0 1)}),
        map (C := C) x.1 x.2 '' ball 0 1) ∩ (A.1 ∩ C)) := by
      congrm (⋃ n, ⋃ (i : I n), map (C := C) n i '' ball 0 1) ∩ ?_
      symm
      rw [Set.inter_eq_right]
      exact subset_not_disjoint' A.1
    _ = (⋃ n, ⋃ (i : { i : I n // ¬Disjoint A.carrier (map (C := C) n i '' ball 0 1) }),
        map (C := C) n i '' ball 0 1) ∩ (A.1 ∩ C) := by
      rw [← inter_assoc]
      congrm ?_ ∩ (A.1 ∩ C)
      ext x
      simp only [iUnion_coe_set, TopologicalSpace.Compacts.carrier_eq_coe, mem_inter_iff,
        mem_iUnion, exists_prop, Sigma.exists,
        Subtype.exists, and_iff_right_iff_imp, forall_exists_index, and_imp]
      constructor
      · intro ⟨⟨n, i, imem, xmem1⟩, ⟨m, j, hmj, xmem2⟩⟩
        have := @not_disjoint_equal _ _ _ _ n i m j (by rw [not_disjoint_iff]; use x)
        rw [Sigma.mk.inj_iff] at this
        rcases this with ⟨eq1, eq2⟩
        subst eq1
        rw [heq_eq_eq] at eq2
        subst eq2
        use n, i
      · exact fun ⟨n, i, memI, notdisjoint, xmem⟩ ↦ ⟨⟨n, ⟨i, ⟨memI, xmem⟩⟩⟩, ⟨n, ⟨i, ⟨notdisjoint, xmem⟩⟩⟩⟩
    _ = (⋃ n, ⋃ (i : { i : ↑(I n) // ¬Disjoint A.carrier (map (C := C) n i '' ball 0 1) }),
        map (C := C) n i '' ball 0 1) ∩ A.1 := by
      rw [inter_comm A.carrier, ← inter_assoc]
      congr
      simp_rw [Set.inter_eq_left, ← union']
      apply Set.iUnion_mono''
      intro n x
      rw [mem_iUnion, mem_iUnion]
      intro ⟨i, _⟩
      use i

lemma finite_of_compact (compact : IsCompact C) : CWComplex.Finite C := by
  apply finite_of_finite_cells
  have : ∀ m (j : cell C m), ¬Disjoint C (map m j '' ball 0 1) := by
    intro m j
    rw [disjoint_comm, not_disjoint_iff]
    use map m j 0
    have zeromem : map m j 0 ∈ ↑(map m j) '' ball 0 1 := by
      apply mem_image_of_mem
      simp only [mem_ball, dist_self, zero_lt_one]
    refine ⟨zeromem, ?_⟩
    exact (map_ball_subset_complex _ m j) zeromem
  let f : (Σ m, {j : cell C m // ¬ Disjoint C (map m j '' ball 0 1)}) ≃ Σ m, cell C m := {
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
  exact isCompact_map_closedBall C n i

lemma compact_iff_finite : IsCompact C ↔ Finite C := ⟨finite_of_compact, compact_of_finite⟩
