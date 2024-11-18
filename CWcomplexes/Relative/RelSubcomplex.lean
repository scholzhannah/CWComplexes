import CWcomplexes.Relative.RelLemmas
import Mathlib.Analysis.NormedSpace.Real

/-!
# Subcomplexes

In this file we discuss subcomplexes of CW-complexes.

## Main definitions:
* `Subcomplex`: A subcomplex is a closed subspace of a CW-complex that is the union of open cells of
  the CW-complex.
* `Subcomplex'`: An alternative definition of a subcomplex that does not require that the subspace
  is closed. Instead it requires that for every open cell that forms the subcomplex the
  corresponding closed cell is a subset of the subspace.
* `Subcomplex''` : An alternative definition of a subcomplex that does not require the subspace to
  be closed but instead requires that it is a CW-complex itself.
* `attach_cell`: The subcomplex that results from attaching a cell to a subcomplex when the edge of
  the cell is contained in the original subcomplex.

## Main results:
* `CWComplex_subcomplex`: A subcomplex of a CW-complex is again a CW-complex.
* `subcomplex_iUnion_subcomplex`: A union of subcomplexes is again a subcomplex.
* `cell_mem_finite_subcomplex`: Every cell is part of a finite subcomplex.
* `compact_subset_finite_subcomplex`: Every compact set in a CW-complex is contained in a finite
  subcomplex.

## Notation
* `E ⇂ C`: `E` is a subcomplex of the CW-complex `C`.

## References
* [K. Jänich, *Topology*]
-/

noncomputable section

open Metric Set

namespace CWComplex

variable {X : Type*} [t : TopologicalSpace X] [T2Space X] {C D : Set X}

section

/-- A subcomplex is a closed subspace of a CW-complex that is the union of open cells of the
  CW-complex.-/
class Subcomplex (C D : Set X) [RelCWComplex C D] (E : Set X) where
  /-- The indexing set of cells of the subcomplex.-/
  I : Π n, Set (cell C D n)
  /-- A subcomplex is closed.-/
  closed : IsClosed E
  /-- The union of all open cells of the subcomplex equals the subcomplex.-/
  union : D ∪ ⋃ (n : ℕ) (j : I n), openCell (C := C) (D := D) n j = E

/-- An alternative version of `Subcomplex`: Instead of requiring that `E` is closed it requires
  that for every cell of the subcomplex the corresponding closed cell is a subset of `E`.-/
def Subcomplex' (C D : Set X) [RelCWComplex C D] (E : Set X) (I : Π n, Set (cell C D n))
    (closedCell_subset : ∀ (n : ℕ) (i : I n), closedCell (C := C) (D := D) n i ⊆ E)
    (union : D ∪ ⋃ (n : ℕ) (j : I n), openCell (C := C) (D := D) n j = E) : Subcomplex C D E where
  I := I
  closed := by
    have EsubC : E ⊆ C := by
      simp_rw [← union, ← iUnion_openCell (C := C) (D := D)]
      exact union_subset_union_right D
        (iUnion_mono fun n ↦ iUnion_subset fun i ↦ by apply subset_iUnion_of_subset ↑i; rfl)
    apply isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell (D := D) EsubC
    · have : D ⊆ E := by
        rw [← union]
        exact subset_union_left
      rw [inter_eq_right.2 this]
      exact isClosedBase C
    intro n _ j
    by_cases h : j ∈ I n
    · right
      suffices closedCell n j ⊆ E by
        rw [inter_eq_right.2 this]
        exact isClosed_closedCell
      exact closedCell_subset n ⟨j, h⟩
    · left
      rw [← union, union_inter_distrib_right]
      apply IsClosed.union
      · rw [inter_comm, (disjointBase n j).inter_eq]
        exact isClosed_empty
      · simp_rw [iUnion_inter]
        suffices ⋃ m, ⋃ (i : ↑(I m)), openCell m (i : cell C D m) ∩ openCell (C := C) n j = ∅ by
          rw [this]
          exact isClosed_empty
        apply iUnion_eq_empty.2 fun m ↦ iUnion_eq_empty.2 fun i ↦ ?_
        apply disjoint_openCell_of_ne
        aesop
  union := union

/-- An alternative version of `Subcomplex`: Instead of requiring that `E` is closed it requires
  that for every cell of the subcomplex the corresponding closed cell is a subset of `E`.-/
def Subcomplex'AB (C : Set X) [CWComplex C] (E : Set X) (I : Π n, Set (cell C ∅ n))
    (closedCell_subset : ∀ (n : ℕ) (i : I n), closedCell (C := C) (D := ∅) n i ⊆ E)
    (union : ⋃ (n : ℕ) (j : I n), openCell (C := C) (D := ∅) n j = E) : Subcomplex C ∅ E where
  I := I
  closed := by
    have EsubC : E ⊆ C := by
      simp_rw [← union, ← iUnion_openCell (C := C) (D := ∅), empty_union]
      exact iUnion_mono fun n ↦ iUnion_subset fun i ↦ by apply subset_iUnion_of_subset ↑i; rfl
    apply isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell (D := ∅) EsubC
      (by rw [inter_empty]; exact isClosed_empty)
    intro n _ j
    by_cases h : j ∈ I n
    · right
      suffices closedCell n j ⊆ E by
        rw [inter_eq_right.2 this]
        exact isClosed_closedCell
      exact closedCell_subset n ⟨j, h⟩
    · left
      simp_rw [← union, iUnion_inter]
      suffices ⋃ m, ⋃ (i : ↑(I m)), openCell m (i : cell C ∅ m) ∩ openCell (C := C) n j = ∅ by
        rw [this]
        exact isClosed_empty
      apply iUnion_eq_empty.2 fun m ↦ iUnion_eq_empty.2 fun i ↦ ?_
      apply disjoint_openCell_of_ne
      aesop
  union := by
    rw [empty_union]
    exact union

/-- An alternative version of `Subcomplex`: Instead of requiring that `E` is closed it requires that
  `E` is a CW-complex. -/
def Subcomplex'' (C D : Set X) [RelCWComplex C D] (E : Set X) (I : Π n, Set (cell C D n))
    [RelCWComplex E D]
    (union : D ∪ ⋃ (n : ℕ) (j : I n), openCell (C := C) (D := D) n j = E) : Subcomplex C D E where
  I := I
  closed := CWComplex.isClosed (D := D)
  union := union

/-- An alternative version of `Subcomplex`: Instead of requiring that `E` is closed it requires that
  `E` is a CW-complex. -/
def Subcomplex''AB (C : Set X) [CWComplex C] (E : Set X) (I : Π n, Set (cell C ∅ n))
    [CWComplex E]
    (union : ⋃ (n : ℕ) (j : I n), openCell (C := C) (D := ∅) n j = E) : Subcomplex C ∅ E where
  I := I
  closed := CWComplex.isClosed (D := ∅)
  union := by
    rw [empty_union]
    exact union

namespace Subcomplex

lemma subset_complex {X : Type*} [TopologicalSpace X] {C D : Set X} [RelCWComplex C D]
    (E : Set X) [subcomplex : Subcomplex C D E] : E ⊆ C := by
  simp_rw [← subcomplex.union, ← iUnion_openCell (C := C) (D := D)]
  apply union_subset_union_right D
  exact iUnion_mono fun n ↦ iUnion_subset fun i ↦ by apply subset_iUnion_of_subset ↑i; rfl
