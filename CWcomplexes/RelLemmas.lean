import CWcomplexes.RelConstructions
import CWcomplexes.RelSubcomplex
import Mathlib.Topology.Sets.Compacts

/-!
# Lemmas about CW-complexes

In this file we proof some lemmas about CW-complexes such as:
* `induction_isClosed_levelaux`: A set `A` in a CW-complex is closed if assuming that
  the intersection `A ∩ levelaux C m` is closed for all `m ≤ n` implies that
  `A ∩ closedCell n j` is closed for every `j : cell C n`.
* `isDiscrete_level_zero`: the zeroth level of a CW-complex is discrete.
* `compact_inter_finite`: A compact set can only meet finitely many open cells.
* `compact_iff_finite`: A CW-complex is compact iff it is finte.
* `compact_subset_finite_subcomplex`: Every compact set in a CW-complex is contained in a finite
  subcomplex.

## References
* [A. Hatcher, *Algebraic Topology*]
-/

open Metric Set

namespace Topology

variable {X : Type*} [t : TopologicalSpace X] [T2Space X] {C D : Set X}

/-
1. Somehow it forgets `D` at the beginning of the inference. Is that supposed to happen?
  (But that also happens when inference doesn't fail)

2. Then it seems to want to prove that `skeletonLT C n` is a subcomplex of `∅`. Which it doesn't
  give up on immediately since it knows now that `∅` is a CW complex.

3. Then it thinks that it should try to decompose `∅` into `iUnions` and just never stops.
-/

--set_option trace.Meta.synthInstance true in
lemma RelCWComplex.isClosed_skeletonLT [RelCWComplex C D] (n : ℕ∞) :
    IsClosed (skeletonLT C n) :=
  --let _ := ClasCWComplex.instEmpty (X := X)
  isClosed --(D := D)

lemma RelCWComplex.isClosed_skeleton [RelCWComplex C D] (n : ℕ∞) : IsClosed (skeleton C n) :=
  let _ := Subcomplex.instSubcomplex (C := C) (skeleton C n)
  isClosed

lemma RelCWComplex.isClosed_iff_inter_skeletonLT_isClosed [RelCWComplex C D] {A : Set X}
    (asubc : A ⊆ C) : IsClosed A ↔ ∀ (n : ℕ), IsClosed (A ∩ skeletonLT C n) := by
  refine ⟨fun closedA _ ↦  IsClosed.inter closedA (isClosed_skeletonLT _), ?_⟩
  intro h
  rw [closed C A asubc]
  constructor
  · intro n j
    rw [(inter_eq_right.2 (closedCell_subset_skeletonLT n j)).symm, ← inter_assoc]
    exact IsClosed.inter (h (n + 1)) isClosed_closedCell
  · rw [← skeletonLT_zero_eq_base (C := C) (D := D)]
    exact h 0

/-- The intersection with `skeletonLT C (Nat.succ n)` is closed iff the intersection with
  `skeletonLT C n ` and every cell of dimension `n` is closed.-/
lemma RelCWComplex.inter_skeletonLT_succ_isClosed_iff
    [RelCWComplex C D] (A : Set X) (n : ℕ):
    IsClosed (A ∩ skeletonLT C n.succ) ↔ IsClosed (A ∩ skeletonLT C n) ∧
    ∀ (j : cell C n), IsClosed (A ∩ closedCell n j) := by
  constructor
  · intro hclosed
    constructor
    · rw [← inter_eq_right.2 (skeletonLT_mono ((by norm_cast; exact Nat.le_succ n) : ↑n ≤ ↑n.succ)),
        ← inter_assoc]
      exact hclosed.inter (isClosed_skeletonLT n)
    · intro j
      have : A ∩ skeletonLT C n.succ ⊆ C := by
        apply subset_trans inter_subset_right
        simp_rw [← skeletonLT_top (C := C) (D := D)]
        exact skeletonLT_mono le_top
      rw [closed C (A ∩ skeletonLT C n.succ) this] at hclosed
      replace hclosed := hclosed.1 n j
      rw [inter_assoc, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
        inter_eq_right.2 (closedCell_subset_skeletonLT n j)] at hclosed
      exact hclosed
  · intro ⟨closed1, closed2⟩
    have sub : A ∩ skeletonLT C n.succ ⊆ C := by
      apply subset_trans inter_subset_right
      simp_rw [← skeletonLT_top (C := C) (D := D)]
      exact skeletonLT_mono le_top
    have : IsClosed (A ∩ skeletonLT C ↑n.succ ∩ D) := by
      simp_rw [inter_assoc, ← skeletonLT_zero_eq_base (C := C),
        inter_eq_right.2 (skeletonLT_mono n.succ.cast_nonneg')]
      rw [← inter_eq_right.2 (skeletonLT_mono n.cast_nonneg'), ← inter_assoc,
        skeletonLT_zero_eq_base]
      exact closed1.inter (isClosedBase C)
    apply isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell (D := D) sub this
    intro m _ j
    by_cases msuccltn : m < n
    · right
      rw [inter_assoc, ← inter_eq_right.2
        ((closedCell_subset_skeletonLT m j).trans
          (skeletonLT_mono (by norm_cast : (m : ℕ∞) + 1 ≤ n))),
        ← inter_assoc (skeletonLT _ _),
        inter_eq_right.2 (skeletonLT_mono (by norm_cast; exact Nat.le_succ n)), ← inter_assoc]
      exact closed1.inter isClosed_closedCell
    by_cases msucceqn : m = n
    · right
      subst msucceqn
      rw [inter_assoc, inter_comm (skeletonLT _ m.succ), ← inter_assoc]
      exact (closed2 _).inter (isClosed_skeletonLT _)
    left
    have : n.succ ≤ m := by
      push_neg at msuccltn msucceqn
      exact msuccltn.lt_of_ne msucceqn.symm
    rw [inter_assoc, (disjoint_skeletonLT_openCell (by norm_cast)).inter_eq, inter_empty]
    exact isClosed_empty

/--  A set `A` in a CW-complex is closed if `A ∩ D` is closed and assuming that the intersection
  `A ∩ levelaux C m` is closed for all `m ≤ n` implies that `A ∩ closedCell n j` is closed for every
   `j : cell C n`.-/
lemma RelCWComplex.induction_isClosed_skeletonLT [RelCWComplex C D] {A : Set X} (asub : A ⊆ C)
    (start : IsClosed (A ∩ D))
    (step : ∀ (n : ℕ), (∀ m (_ : m ≤ n), IsClosed (A ∩ skeletonLT C m)) →
    ∀ j, IsClosed (A ∩ closedCell (C := C) (D := D) n j)) :
    IsClosed A := by
  rw [isClosed_iff_inter_skeletonLT_isClosed (D := D) asub]
  intro n
  induction' n using Nat.case_strong_induction_on with n hn
  · simpa only [CharP.cast_eq_zero, skeletonLT_zero_eq_base (C := C) (D := D)]
  rw [inter_skeletonLT_succ_isClosed_iff]
  exact ⟨hn n n.le_refl, step n hn⟩

/--  A set `A` in a CW-complex is closed if assuming that the intersection `A ∩ levelaux C m` is
  closed for all `m ≤ n` implies that `A ∩ closedCell n j` is closed for every `j : cell C n`.-/
lemma CWComplex.induction_isClosed_skeletonLT [CWComplex C] {A : Set X} (asub : A ⊆ C)
    (step : ∀ (n : ℕ), (∀ m (_ : m ≤ n), IsClosed (A ∩ skeletonLT C m)) →
    ∀ j, IsClosed (A ∩ closedCell (C := C) (D := ∅) n j)) :
    IsClosed A := by
  rw [RelCWComplex.isClosed_iff_inter_skeletonLT_isClosed (D := ∅) asub]
  intro n
  induction' n using Nat.case_strong_induction_on with n hn
  · simp only [CharP.cast_eq_zero, skeletonLT_zero_eq_empty, inter_empty, isClosed_empty]
  rw [RelCWComplex.inter_skeletonLT_succ_isClosed_iff]
  exact ⟨hn n n.le_refl, step n hn⟩

/-- `levelaux C 1` is discrete.-/
lemma CWComplex.isDiscrete_levelaux_one [CWComplex C] {A : Set X} :
    IsClosed (A ∩ skeletonLT C 1) := by
  apply isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell (C := C)
    (inter_subset_right.trans
    (by simp_rw [← skeletonLT_top (C := C) (D := ∅)]; apply skeletonLT_mono le_top))
  intro n nlt j
  left
  simp_rw [← Nat.succ_le_iff] at nlt
  rw [inter_assoc, (disjoint_skeletonLT_openCell (by simp only [Nat.one_le_cast, nlt])).inter_eq,
    inter_empty]
  exact isClosed_empty

/-- `level 0` is discrete.-/
lemma CWComplex.isDiscrete_level_zero [CWComplex C] {A : Set X} :
    IsClosed (A ∩ skeleton C 0) :=
  isDiscrete_levelaux_one

/-- A compact set can only meet finitely many open cells.-/
lemma RelCWComplex.compact_inter_finite [RelCWComplex C D] (A : Set X) (compact : IsCompact A) :
    _root_.Finite (Σ (m : ℕ), {j : cell C m // ¬ Disjoint A (openCell m j)}) := by
  -- We do a proof by contradiction assuming that `A` meets infinitely many cells.
  -- We then pick a set `P` of points where each one is in the intersection of `A` with
  -- a different open cell. This set is therefore also infinite.
  -- We then show that this set is closed and has discrete topology.
  -- Since it is a closed subset of a compact set it is also compact.
  -- But a compact set with discrete topology must be finite. Contradiction.
  by_contra h
  simp only [TopologicalSpace.Compacts.carrier_eq_coe, not_disjoint_iff, SetLike.mem_coe,
    not_finite_iff_infinite] at h
  let p (m : Σ (m : ℕ), { j : cell C m // ∃ x ∈ A, x ∈ openCell m j}) :=
    Classical.choose (m.2).2
  let hp m : p m ∈ A ∧ p m ∈ openCell m.1 m.2 := by
    simp_rw [p]
    exact Classical.choose_spec (m.2).2
  -- We define `P`:
  let P := p '' (univ : Set (Σ (m : ℕ), {j : cell C m // ∃ x ∈ A, x ∈ openCell m j}))
  -- `P` is infinite:
  have infpoints : P.Infinite := by
    apply (infinite_univ_iff.2 h).image
    intro ⟨m, j, hj⟩ _ ⟨n, i, hi⟩ _ peqp
    have hpj : p ⟨m, j, hj⟩ ∈ openCell m j := by simp_rw [p, (Classical.choose_spec hj).2]
    have hpi : p ⟨m, j, hj⟩ ∈ openCell n i := by simp_rw [peqp, p, (Classical.choose_spec hi).2]
    suffices (⟨m, j⟩ : Σ n, cell C n) = ⟨n, i⟩ by aesop
    apply eq_of_not_disjoint_openCell
    rw [not_disjoint_iff]
    use p ⟨m, j, hj⟩
  have subsetA : P ⊆ A := by
    intro x xmem
    simp only [mem_image, image_univ, mem_range, P] at xmem
    obtain ⟨n, rfl⟩ := xmem
    exact (hp n).1
  -- `P` has discrete topology:
  have subsetsclosed : ∀ (s : Set P), IsClosed (s : Set X) := by
    intro s
    have ssubc : ↑↑s ⊆ ↑C := by
      apply (Subtype.coe_image_subset ↑P s).trans
      intro x xmem
      simp only [image_univ, mem_range, P] at xmem
      obtain ⟨m, rfl⟩ := xmem
      exact openCell_subset_complex _ _ (hp m).2
    apply induction_isClosed_skeletonLT (D := D) ssubc
    · suffices Subtype.val '' s ∩ D = ∅ by
        rw [this]
        exact isClosed_empty
      by_contra h
      push_neg at h
      rw [inter_nonempty_iff_exists_left] at h
      rcases h with ⟨x, hx1, hx2⟩
      replace hx1 := (Subtype.coe_image_subset P s) hx1
      simp only [image_univ, mem_range, Sigma.exists, Subtype.exists, P] at hx1
      obtain ⟨n, j, h, h2⟩ := hx1
      replace hp := hp ⟨n, ⟨j, h⟩⟩
      suffices x ∈ openCell n j ∩ D by
        rw [(disjointBase n j).inter_eq] at this
        exact this
      subst x
      exact ⟨hp.2, hx2⟩
    intro n hn j
    simp_rw [← cellFrontier_union_openCell_eq_closedCell, inter_union_distrib_left]
    apply IsClosed.union
    · rw [← inter_eq_right.2 (cellFrontier_subset_skeletonLT n j), ← inter_assoc]
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
      have : ∀ (y : X) (ymemP : y ∈ P), ⟨y, ymemP⟩ ∈ s →
          ↑y ∈ openCell n j → y = p ⟨n, ⟨j, hnj⟩⟩ := by
        intro y ymemP ymems ymemopen
        simp only [image_univ, mem_range, Sigma.exists, Subtype.exists, P] at ymemP
        obtain ⟨m, i, hmi, rfl⟩ := ymemP
        have hpmi := hp ⟨m, i, hmi⟩
        suffices (⟨m, i⟩ : Σ n, cell C n) = ⟨n, j⟩ by
          rw [Sigma.mk.inj_iff] at this
          obtain ⟨eq1, eq2⟩ := this
          subst eq1
          rw [heq_eq_eq] at eq2
          subst eq2
          rfl
        apply eq_of_not_disjoint_openCell
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
  -- `P` is closed:
  have closed: IsClosed P := by
    have := subsetsclosed (univ : Set P)
    rw [Subtype.coe_image_univ] at this
    exact this
  -- `P` is compact:
  have compact : IsCompact P := compact.of_isClosed_subset closed subsetA
  -- `P` is finite:
  have finite : Set.Finite P := compact.finite discrete
  contradiction

/-- This is a version of `compact_inter_finite` that says that a compact set can only meet
  finitely many open cells out of a subset of all cells.-/
lemma RelCWComplex.compact_inter_finite_subset [RelCWComplex C D] (A : Set X)
    (compact : IsCompact A)
    {I : (n : ℕ) → Set (cell C n)} :
    _root_.Finite (Σ (m : ℕ), {j : I m // ¬ Disjoint A (openCell (C := C) (D := D) m j)}) := by
  let f := fun (x : Σ (m : ℕ), {j : I m // ¬ Disjoint A (openCell (C := C) (D := D) m j)}) ↦
    (⟨x.1, ⟨x.2.1, x.2.2⟩⟩ : Σ (m : ℕ), {j : cell C m // ¬ Disjoint A (openCell m j)})
  apply @Finite.of_injective _ _ (compact_inter_finite A compact) f
  intro ⟨x1, x2, x3⟩ ⟨y1, y2, y3⟩ eq
  simp only [TopologicalSpace.Compacts.carrier_eq_coe, Sigma.mk.inj_iff, f] at eq
  rcases eq with ⟨rfl, eq⟩
  simp only [heq_eq_eq, Subtype.mk.injEq, Subtype.val_inj] at eq
  simp_rw [eq]

/-- This is a version of `compact_inter_finite` where the subtype is written differently. -/
lemma RelCWComplex.compact_inter_finite' [RelCWComplex C D] (A : Set X) (compact : IsCompact A) :
    _root_.Finite {x : Σ (n : ℕ), cell C n // ¬Disjoint A (openCell x.fst x.snd)} := by
  let f := fun (x : (Σ (m : ℕ), {j : cell C m // ¬ Disjoint A (openCell m j)})) ↦
    (⟨⟨x.1, x.2.1⟩, x.2.2⟩ : { x : Σ (n : ℕ), cell C n // ¬Disjoint A (openCell x.fst x.snd)})
  apply @Finite.of_surjective _ _ (compact_inter_finite A compact) f
  intro x
  use ⟨x.1.1, ⟨x.1.2, x.2⟩⟩

/-- This is a version of `compact_inter_finite_subset` where the subtype is written differently.-/
lemma RelCWComplex.compact_inter_finite_subset' [RelCWComplex C D] (A : Set X)
    (compact : IsCompact A) {I : (n : ℕ) → Set (cell C n)} :
    _root_.Finite {x : Σ (n : ℕ), I n // ¬Disjoint A (openCell (C := C) (D := D) x.fst x.snd)} := by
  let f := fun (x : {x : Σ (n : ℕ), I n // ¬Disjoint A (openCell (C := C) (D := D) x.fst x.snd)}) ↦
    (⟨⟨x.1.1, x.1.2⟩, x.2⟩ :
    {x : Σ (n : ℕ), cell C n // ¬Disjoint A (openCell (D := D) x.fst x.snd)})
  apply @Finite.of_injective _ _ (compact_inter_finite' A compact) f
  intro ⟨⟨x1, x2⟩, x3⟩ ⟨⟨y1, y2⟩, y3⟩ eq
  simp only [TopologicalSpace.Compacts.carrier_eq_coe, Subtype.mk.injEq, Sigma.mk.inj_iff, f] at eq
  rcases eq with ⟨rfl, eq⟩
  simp only [heq_eq_eq, Subtype.mk.injEq, Subtype.val_inj] at eq
  simp_rw [eq]

-- I will probably need a relative version of this someday but right now I don't know what.

/-- For a set `A` the intersection `A ∩ C` is a subset of the base and all the cells of `C`
  that `A` meets. This is useful when applied together with `compact_inter_finite`.-/
lemma RelCWComplex.subset_not_disjoint' {X : Type*} [TopologicalSpace X] {C D : Set X}
    [RelCWComplex C D] (A : Set X) : A ∩ C ⊆ D ∪ ⋃ (x : Σ (m : ℕ),
    {j : cell C m // ¬ Disjoint A (openCell m j)}), openCell (C := C) x.1 x.2 := by
  intro x ⟨xmem1, xmem2⟩
  rw [← union_iUnion_openCell_eq_complex (C := C) (D := D)] at xmem2
  rcases xmem2 with xmem2 | xmem2
  · exact mem_union_left _ xmem2
  right
  simp only [mem_iUnion] at xmem2 ⊢
  rcases xmem2 with ⟨m, j, hmj⟩
  use ⟨m, j, not_disjoint_iff.2 ⟨x, xmem1, hmj⟩⟩

/-- For a set `A` the intersection `A ∩ C` is a subset of all the cells of `C` that `A` meets.
  This is useful when applied together with `compact_inter_finite`.-/
lemma CWComplex.subset_not_disjoint' {X : Type*} [TopologicalSpace X] {C : Set X}
    [CWComplex C] (A : Set X) : A ∩ C ⊆ ⋃ (x : Σ (m : ℕ),
    {j : cell C m // ¬ Disjoint A (openCell m j)}), openCell (C := C) x.1 x.2 := by
  have := RelCWComplex.subset_not_disjoint' A (C := C)
  rw [empty_union] at this
  exact this

/-- A version of `subset_not_disjoint'` using closed cells.-/
lemma RelCWComplex.subset_not_disjoint {X : Type*} [TopologicalSpace X] {C D : Set X}
    [RelCWComplex C D] (A : Set X) : A ∩ C ⊆ D ∪ ⋃ (x : Σ (m : ℕ),
    {j : cell C m // ¬ Disjoint A (openCell m j)}), closedCell (C := C) (D := D) x.1 x.2 := by
  intro x ⟨xmem1, xmem2⟩
  rw [← union_iUnion_openCell_eq_complex (C := C) (D := D)] at xmem2
  rcases xmem2 with xmem2 | xmem2
  · exact mem_union_left _ xmem2
  right
  simp only [mem_iUnion] at xmem2 ⊢
  rcases xmem2 with ⟨m, j, hmj⟩
  use ⟨m, j, not_disjoint_iff.2 ⟨x, xmem1, hmj⟩⟩
  exact openCell_subset_closedCell _ _ hmj

/-- A version of `subset_not_disjoint'` using closed cells.-/
lemma CWComplex.subset_not_disjoint {X : Type*} [TopologicalSpace X] {C : Set X}
    [CWComplex C] (A : Set X) : A ∩ C ⊆ ⋃ (x : Σ (m : ℕ),
    {j : cell C m // ¬ Disjoint A (openCell m j)}), closedCell (C := C) x.1 x.2 := by
  have := RelCWComplex.subset_not_disjoint (C := C) A
  rw [empty_union] at this
  exact this

/-- A compact CW-complex is finite.-/
lemma RelCWComplex.finite_of_compact [RelCWComplex C D] (compact : IsCompact C) : Finite C := by
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
  exact RelCWComplex.compact_inter_finite C compact

/-- A finite relative CW-complex with compact base is compact.-/
lemma RelCWComplex.compact_of_finite {X : Type*} [TopologicalSpace X] {C D : Set X}
    [RelCWComplex C D] [finite : Finite C] (hD: IsCompact D) : IsCompact C := by
  rw [finite_iff_finite_cells] at finite
  rw [← union (C := C) (D := D), iUnion_sigma']
  exact hD.union (isCompact_iUnion (fun ⟨n, i⟩ ↦ isCompact_closedCell))

/-- A finite CW-complex is compact.-/
lemma CWComplex.compact_of_finite {X : Type*} [TopologicalSpace X] {C : Set X}
    [CWComplex C] [finite : Finite C] : IsCompact C := by
  rw [finite_iff_finite_cells] at finite
  rw [← union (C := C), iUnion_sigma']
  exact isCompact_iUnion (fun ⟨n, i⟩ ↦ isCompact_closedCell)

/-- A relative CW-complex with compact base is compact iff it is finite. -/
lemma RelCWComplex.compact_iff_finite [RelCWComplex C D] (hD : IsCompact D) :
    IsCompact C ↔ Finite C :=
  ⟨finite_of_compact, fun _ ↦ compact_of_finite hD⟩

/-- A CW-complex is compact iff it is finite. -/
lemma CWComplex.compact_iff_finite [CWComplex C] : IsCompact C ↔ Finite C :=
  ⟨RelCWComplex.finite_of_compact, fun _ ↦ RelCWComplex.compact_of_finite isCompact_empty⟩

/-- Every compact set in a CW-complex is contained in a finite subcomplex.-/
lemma RelCWComplex.Subcomplex.compact_subset_finite_subcomplex [RelCWComplex C D]
    {B : Set X} (compact : IsCompact B) :
    ∃ (E : Set X) (_sub : Subcomplex C E), Finite E ∧ B ∩ C ⊆ E := by
  have : _root_.Finite (Σ n, { j | ¬Disjoint B (openCell (C:= C) n j)}) :=
    compact_inter_finite (C := C) (D := D) B compact
  obtain ⟨E, sub, finite, subset⟩ := finite_iUnion_subset_finite_subcomplex (C := C) (D := D)
    (fun n ↦ { j | ¬Disjoint B (openCell (C := C) n j)})
  use E,sub
  refine ⟨finite, ?_⟩
  apply subset_trans (subset_not_disjoint (C := C) (D := D) B)
  apply union_subset
  · exact base_subset_complex
  rw [iUnion_sigma]
  exact subset

instance RelCWComplex.FiniteDimensional_instskeletonLT_of_nat [RelCWComplex C D]
    [FiniteDimensional C] (n : ℕ) : FiniteDimensional (skeletonLT C n) where
  eventually_isEmpty_cell := by
    simp only [Subcomplex.instSubcomplex_cell, Subcomplex.mk''_I, Nat.cast_lt, coe_setOf,
      isEmpty_subtype, not_lt, Filter.eventually_atTop, ge_iff_le]
    use n
    intro b hnb
    simp [hnb]

instance RelCWComplex.FiniteDimensional_instskeleton_of_nat [RelCWComplex C D] [FiniteDimensional C]
    (n : ℕ) : FiniteDimensional (skeleton C n) :=
  FiniteDimensional_instskeletonLT_of_nat _


namespace CWComplex

export RelCWComplex (isClosed_skeletonLT isClosed_skeleton isClosed_iff_inter_skeletonLT_isClosed
  inter_skeletonLT_succ_isClosed_iff compact_inter_finite compact_inter_finite_subset
  compact_inter_finite' compact_inter_finite_subset' finite_of_compact
  Subcomplex.compact_subset_finite_subcomplex Subcomplex.instSkeletonLT
  Subcomplex.instSkeleton FiniteDimensional_instskeletonLT_of_nat
  FiniteDimensional_instskeleton_of_nat)

end CWComplex

end Topology
