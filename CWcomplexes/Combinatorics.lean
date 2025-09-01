import Mathlib.Topology.CWComplex.Classical.Basic

noncomputable section

open Metric Set

namespace Topology

variable {X : Type*} [t : TopologicalSpace X] {C D : Set X}

lemma RelCWComplex.lt_of_openCell_subset_cellFrontier [RelCWComplex C D] (n m : ℕ) (i : cell C n)
    (j : cell C m) (hij : openCell m j ⊆ cellFrontier n i) : m < n := by
  obtain ⟨I, hI⟩ := cellFrontier_subset_finite_openCell n i
  have := (disjointBase m j).subset_right_of_subset_union (hij.trans hI)
  by_cases h : ∃ (l : ℕ) (hl : l < n) (k : cell C l) (hj : k ∈ I l),
    (⟨l, k⟩ :  Σ m, cell C m ) = ⟨m, j⟩
  · obtain ⟨l, hl, k, hk, h⟩ := h
    simp_all
  · exfalso
    push_neg at h
    suffices openCell m j = ∅ by
      rw [← (mem_empty_iff_false (map m j 0)), ← this]
      exact map_zero_mem_openCell m j
    simp_rw [← disjoint_of_subset_iff_left_eq_empty this, disjoint_iUnion_right]
    intro l hl k hk
    exact disjoint_openCell_of_ne (h l hl k hk).symm

lemma RelCWComplex.eq_of_openCell_subset_closedCell [RelCWComplex C D] (n : ℕ) (i j : cell C n)
    (hij : openCell n j ⊆ closedCell n i) : j = i := by
  by_contra h
  rw [← cellFrontier_union_openCell_eq_closedCell] at hij
  replace hni := ((disjoint_openCell_of_ne (by simp [h])).subset_left_of_subset_union hij)
  exact (lt_of_openCell_subset_cellFrontier n n i j hni).false

lemma RelCWComplex.le_of_openCell_subset_closedCell [RelCWComplex C D] (n m : ℕ) (i : cell C n)
    (j : cell C m) (hij : openCell m j ⊆ closedCell n i) : m ≤ n := by
  by_cases h: (⟨m, j⟩ : Σ m, cell C m ) = ⟨n, i⟩
  · simp_all
  · rw [← cellFrontier_union_openCell_eq_closedCell] at hij
    replace hij := (disjoint_openCell_of_ne h).subset_left_of_subset_union hij
    exact (lt_of_openCell_subset_cellFrontier n m i j hij).le

open Classical in
def RelCWComplex.subcells [RelCWComplex C D] (n : ℕ) (i : cell C n) : Finset (Σ m, cell C m) :=
  Finite.toFinset (s := {⟨m, j⟩ : Σ m, cell C m | openCell m j ⊆ closedCell n i}) (by
    obtain ⟨I, hI⟩ := cellFrontier_subset_finite_openCell n i
    suffices {⟨m, j⟩ : Σ m, cell C m | openCell m j ⊆ closedCell n i} ⊆
        (((Finset.range n).sigma I) ∪ {⟨n, i⟩}).toSet from
      (((Finset.range n).sigma I) ∪ {⟨n, i⟩}).finite_toSet.subset this
    intro ⟨m, j⟩ hmj
    simp_all only [mem_setOf_eq, Finset.coe_union, Finset.coe_sigma, Finset.coe_range,
      Finset.coe_singleton, union_singleton, mem_insert_iff, Sigma.mk.injEq, mem_sigma_iff, mem_Iio,
      Finset.mem_coe]
    have h := lt_or_eq_of_le (le_of_openCell_subset_closedCell n m i j hmj)
    rcases h with h | h
    · right
      refine ⟨h, ?_⟩
      by_contra hj
      rw [← cellFrontier_union_openCell_eq_closedCell] at hmj
      replace hI :=
        ((disjoint_openCell_of_ne (by simp [h.ne])).subset_left_of_subset_union hmj).trans hI
      suffices openCell m j = ∅ by
        rw [← (mem_empty_iff_false (map m j 0)), ← this]
        exact map_zero_mem_openCell m j
      simp_rw [← disjoint_of_subset_iff_left_eq_empty hI, disjoint_union_right,
        disjoint_iUnion_right]
      refine ⟨disjointBase m j, fun l hl k hk ↦ disjoint_openCell_of_ne ?_⟩
      rw [ne_eq, Sigma.mk.injEq, not_and]
      intro h1 h2
      subst m
      exact (eq_of_heq h2 ▸ hj) hk
    · left
      refine ⟨h, ?_⟩
      subst m
      exact heq_of_eq (eq_of_openCell_subset_closedCell n i j hmj))

@[simp]
lemma RelCWComplex.mem_subcells_iff [RelCWComplex C D] {n m : ℕ} {i : cell C n} {j : cell C m} :
    ⟨m, j⟩ ∈ subcells n i ↔ openCell m j ⊆ closedCell n i := by
  simp [subcells]

/- This is untrue!-/
lemma RelCWComplex.openCell_subset_cellFrontier_of_not_disjoint [RelCWComplex C D] {n m : ℕ}
    {i : cell C n} {j : cell C m} (h : ¬ Disjoint (openCell n i) (cellFrontier m j)) :
    openCell n i ⊆ cellFrontier m j := by
  obtain ⟨I, hI⟩ := cellFrontier_subset_finite_openCell m j

  sorry


/- Also untrue!-/
open Classical in
lemma RelCWComplex.mem_subcells_of_not_disjoint [RelCWComplex C D] {n m : ℕ} {i : cell C n}
    {j : cell C m} (h : ¬ Disjoint (openCell n i) (closedCell m j)) : ⟨n, i⟩ ∈ subcells m j := by
  rw [← cellFrontier_union_openCell_eq_closedCell, disjoint_union_right,
    Decidable.not_and_iff_or_not] at h
  rw [mem_subcells_iff]
  rcases h with h | h
  · exact (openCell_subset_cellFrontier_of_not_disjoint h).trans
      (cellFrontier_subset_closedCell m j)
  · rw [not_disjoint_iff] at h
    obtain ⟨x, hx1, hx2⟩ := h
    suffices (⟨n, i⟩ : Σ m, cell C m) = ⟨m, j⟩ by
      obtain ⟨h1, h2⟩ := Sigma.mk.injEq _ _ _ _ ▸ this
      subst n
      rw [heq_iff_eq] at h2
      subst i
      exact openCell_subset_closedCell m j
    apply eq_of_not_disjoint_openCell
    rw [not_disjoint_iff]
    use x

/- Untrue!-/
lemma RelCWComplex.closedCell_subset_base_union_iUnion_subcells [RelCWComplex C D] (n : ℕ)
    (i : cell C n) : closedCell n i ⊆ D ∪ ⋃ (m) (j) (_ : ⟨m, j⟩ ∈ subcells n i), openCell m j := by
  obtain ⟨I, hI⟩ := cellFrontier_subset_finite_openCell n i
  rw [← cellFrontier_union_openCell_eq_closedCell]
  apply union_subset
  ·
    intro x
    sorry
  · apply subset_union_of_subset_right
    refine subset_iUnion_of_subset n (subset_iUnion_of_subset i ?_)
    exact subset_iUnion_of_subset (by simp [openCell_subset_closedCell]) (Subset.refl _)

/-- An alternative version of `Subcomplex`: Instead of requiring that `E` is closed it requires that
  every subcell of a cell in the indexing set is also in the indexing set. -/
@[simps! -isSimp]
def RelCWComplex.Subcomplex.mk''' [T2Space X] (C : Set X) {D : Set X} [RelCWComplex C D] (E : Set X)
    (I : Π n, Set (cell C n))
    (subcell : ∀ n i (_ : i ∈ I n) m j (_ : ⟨m, j⟩ ∈ subcells n i), j ∈ I m)
    (union : D ∪ ⋃ (n : ℕ) (j : I n), openCell (C := C) (D := D) n j = E) : Subcomplex C :=
  mk' C E I
    (by
      intro n ⟨i, hi⟩
      rw [← union, ← cellFrontier_union_openCell_eq_closedCell]
      sorry)
    union


end Topology
