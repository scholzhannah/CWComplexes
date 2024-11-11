import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Order.CompletePartialOrder


/-!
# CW-complexes

This file defines the CW-complexes and proofs basic properties about them.

A CW-complex is a topological space that is made by gluing closed disks of different dimensions
together.

## Main definitions
* `RelCWComplex C D` : The class of CW-structures on a subspace `C` realtive to `D` of a topological
  space `X`.
* `openCell n i` : An open cell of dimension `n`.
* `closedCell n i` : A closed cell of dimension `n`.
* `cellFrontier n i` : The edge of a cell of dimension `n`.
* `level C D n` : The `n`-th level of the CW-complex `C`.

## Main statements
* `iUnion_openCell_eq_level` : The levels can also be seen as a union of open cells.
* `cellFrontier_subset_finite_openCell` : The edge of a cell is contained in a finite union of
  open cells of a lower dimension.

## Implementation notes
* The definition used is the historical definition rather than the modern one to avoid working
  with a lot of different topological spaces.
* We define what it means for a subspace to be a CW-complex instead of a topological space itself.
  This has the advantage that it makes a lot of constructions easier as you do not need to deal with
  different topologies. However, this approach requires the subspace to be closed. Should that
  not be the case you need to consider that subspace as a subspace of itself.
* The definition `CW-complex` does not require `X` to be a Hausdorff space or that `D` is closed.
  A lot of the lemmas will however require these properties.
* For statements the auxiliary construction `levelaux` is preferred over `level` as it makes
  the base case of inductions easier. The statement about `level` should then be derived from the
  one about `levelaux`.

## References
* [A. Hatcher, *Algebraic Topology*]
-/

noncomputable section

open Metric Set

/-- Characterizing when a subspace `C` of a topological space `X` is a CW-complex relative to
  another subspace `D`. Note that this requires `C` and `D` to be closed subspaces.
  If `C` is not closed choose `X` to be `C`. A lot of lemmas will require `[T2Space X]`.-/
class RelCWComplex.{u} {X : Type u} [TopologicalSpace X] (C D : Set X) where
  /-- The indexing type of the cells of dimension `n`.-/
  cell (n : ℕ) : Type u
  /-- The characteristic map of the `n`-cell given by the index `i`.
    This map is a bijection when restricting to `closedBall 0 1` as specified by the property
    `source_eq`. Note that `(Fin n → ℝ)` carries the maximum metric.-/
  map (n : ℕ) (i : cell n) : PartialEquiv (Fin n → ℝ) X
  /-- The source of every charactersitic map of dimension `n` is
    `(closedBall 0 1 : Set (Fin n → ℝ))`.-/
  source_eq (n : ℕ) (i : cell n) : (map n i).source = closedBall 0 1
  /-- The characteristic maps are continuous when restricting to `closedBall 0 1`.-/
  cont (n : ℕ) (i : cell n) : ContinuousOn (map n i) (closedBall 0 1)
  /-- The inverse of the restriction to `closedBall 0 1` is continuous on the image.-/
  cont_symm (n : ℕ) (i : cell n) : ContinuousOn (map n i).symm (map n i).target
  /-- The open cells are pairwise disjoint. Use `pairwiseDisjoint` or `disjoint_openCell_of_ne` in
    the namespace `RelCWComplex` instead. -/
  pairwiseDisjoint' :
    (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1)
  /-- All open cells are disjoint with the base. Use `disjointBase` in the namespace `RelCWComplex`
    instead. -/
  disjointBase' (n : ℕ) (i : cell n) : Disjoint (map n i '' ball 0 1) D
  /-- The edge of a cell is contained in a finite union of closed cells of a lower dimension.
    Use `cellFrontier_subset_finite_closedCell` in the namespace `RelCWComplex` instead.-/
  mapsto (n : ℕ) (i : cell n) : ∃ I : Π m, Finset (cell m),
    MapsTo (map n i) (sphere 0 1) (D ∪ ⋃ (m < n) (j ∈ I m), map m j '' closedBall 0 1)
  /-- A CW-complex has weak topology, i.e. a set `A` in `X` is closed iff its intersection with
    every closed cell and `D` is closed. Use `closed` in the namespace `RelCWComplex` instead.-/
  closed' (A : Set X) (asubc : A ⊆ C) :
    ((∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) ∧ IsClosed (A ∩ D)) → IsClosed A
  /-- The base `D` is closed.-/
  isClosedBase : IsClosed D
  /-- The union of all closed cells equals `C`. Use `union` in the namespace `RelCWComplex`
    instead.-/
  union' : D ∪ ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C

namespace CWComplex

export RelCWComplex (cell map source_eq cont cont_symm mapsto isClosedBase)

variable {X : Type*} [t : TopologicalSpace X] {C D : Set X} [RelCWComplex C D]

/-- The open `n`-cell given by the index `i`. Use this instead of `map n i '' ball 0 1` whenever
  possible.-/
def openCell (n : ℕ) (i : cell C D n) : Set X := map n i '' ball 0 1

/-- The closed `n`-cell given by the index `i`. Use this instead of `map n i '' closedBall 0 1
  whenever possible.`-/
def closedCell (n : ℕ) (i : cell C D n) : Set X := map n i '' closedBall 0 1

/-- The edge of the `n`-cell given by the index `i`. Use this instead of `map n i '' sphere 0 1`
  whenever possible. -/
def cellFrontier (n : ℕ) (i : cell C D n) : Set X := map n i '' sphere 0 1

lemma pairwiseDisjoint :
    (univ : Set (Σ n, cell C D n)).PairwiseDisjoint (fun ni ↦ openCell ni.1 ni.2) :=
  RelCWComplex.pairwiseDisjoint'

lemma disjointBase (n : ℕ) (i : cell C D n) : Disjoint (openCell n i) D :=
  RelCWComplex.disjointBase' n i

lemma disjoint_openCell_of_ne {n m : ℕ} {i : cell C D n} {j : cell C D m}
    (ne : (⟨n, i⟩ : Σ n, cell C D n) ≠ ⟨m, j⟩) : openCell n i ∩ openCell m j = ∅ := by
  have := pairwiseDisjoint (C := C) (D := D)
  simp only [PairwiseDisjoint, Set.Pairwise, Function.onFun, disjoint_iff_inter_eq_empty] at this
  exact this (mem_univ _) (mem_univ _) ne

lemma cellFrontier_subset_finite_closedCell (n : ℕ) (i : cell C D n) :
    ∃ I : Π m, Finset (cell C D m), cellFrontier n i ⊆
    D ∪ ⋃ (m < n) (j ∈ I m), closedCell m j := by
  rcases mapsto n i with ⟨I, hI⟩
  use I
  rw [mapsTo'] at hI
  exact hI

lemma union : D ∪ ⋃ (n : ℕ) (j : cell C D n), closedCell n j = C := RelCWComplex.union'

lemma openCell_subset_closedCell (n : ℕ) (i : cell C D n) : openCell n i ⊆ closedCell n i :=
  image_mono Metric.ball_subset_closedBall

lemma cellFrontier_subset_closedCell (n : ℕ) (i : cell C D n) : cellFrontier n i ⊆ closedCell n i :=
  image_mono Metric.sphere_subset_closedBall

lemma cellFrontier_union_openCell_eq_closedCell (n : ℕ) (i : cell C D n) :
    cellFrontier n i ∪ openCell n i = closedCell n i := by
  rw [cellFrontier, openCell, closedCell, ← image_union]
  congrm map n i '' ?_
  exact sphere_union_ball

lemma map_zero_mem_openCell (n : ℕ) (i : cell C D n) : map n i 0 ∈ openCell n i := by
  apply mem_image_of_mem
  simp only [mem_ball, dist_self, zero_lt_one]

lemma map_zero_mem_closedCell (n : ℕ) (i : cell C D n) : map n i 0 ∈ closedCell n i :=
  openCell_subset_closedCell _ _ (map_zero_mem_openCell _ _)

/-- A non-standard definition of the `n`-th level of a CW-complex for `n ∈ ℕ ∪ ∞` useful for
  induction. The standard `level` is defined in terms of levelaux. `levelaux` is preferred
  statements. You should then derive the statement about `level`. -/
def levelaux (C D : Set X) [RelCWComplex C D] (n : ℕ∞) : Set X :=
  D ∪ ⋃ (m : ℕ) (_ : m < n) (j : cell C D m), closedCell m j

/-- The `n`-th level of a CW-complex, for `n ∈ ℕ ∪ ∞`. For statements use `levelaux` instead
  and then derive the statement about `level`.-/
def level (C D : Set X) [RelCWComplex C D] (n : ℕ∞) : Set X :=
  levelaux C D (n + 1)

lemma levelaux_zero_eq_base : levelaux C D 0 = D := by
  simp only [levelaux, ENat.not_lt_zero, iUnion_of_empty, iUnion_empty, union_empty]

lemma isCompact_closedCell {n : ℕ} {i : cell C D n} : IsCompact (closedCell n i) :=
  (isCompact_closedBall _ _).image_of_continuousOn (cont n i)

lemma isClosed_closedCell [T2Space X] {n : ℕ} {i : cell C D n} :
  IsClosed (closedCell n i) := isCompact_closedCell.isClosed

lemma isCompact_cellFrontier {n : ℕ} {i : cell C D n} : IsCompact (cellFrontier n i) :=
  (isCompact_sphere _ _).image_of_continuousOn ((cont n i).mono sphere_subset_closedBall)

lemma isClosed_cellFrontier [T2Space X] {n : ℕ} {i : cell C D n} : IsClosed (cellFrontier n i) :=
  isCompact_cellFrontier.isClosed

lemma closure_openCell_eq_closedCell [T2Space X] {n : ℕ} {j : cell C D n} :
    closure (openCell n j) = closedCell n j := by
  apply subset_antisymm (isClosed_closedCell.closure_subset_iff.2 (openCell_subset_closedCell n j))
  rw [closedCell, ← closure_ball 0 (by exact one_ne_zero)]
  apply ContinuousOn.image_closure
  rw [closure_ball 0 (by exact one_ne_zero)]
  exact cont n j

lemma closed (C D : Set X) [RelCWComplex C D] [T2Space X] (A : Set X) (asubc : A ⊆ C) :
    IsClosed A ↔ (∀ n (j : cell C D n), IsClosed (A ∩ closedCell n j)) ∧ IsClosed (A ∩ D) := by
  constructor
  · intro closedA
    constructor
    · intro n j
      exact closedA.inter isClosed_closedCell
    · exact closedA.inter (isClosedBase C)
  · exact RelCWComplex.closed' A asubc

@[simp] lemma levelaux_top : levelaux C D ⊤ = C := by
  simp [levelaux, union]

@[simp] lemma level_top : level C D ⊤ = C := levelaux_top

lemma levelaux_mono {n m : ℕ∞} (h : m ≤ n) : levelaux C D m ⊆ levelaux C D n := by
  apply union_subset_union_right
  intro x xmem
  simp_rw [mem_iUnion, exists_prop] at xmem ⊢
  obtain ⟨l , lltm, xmeml⟩ := xmem
  exact ⟨l, lt_of_lt_of_le lltm h, xmeml⟩

lemma level_mono {n m : ℕ∞} (h : m ≤ n) : level C D m ⊆ level C D n :=
  levelaux_mono (add_le_add_right h 1)

lemma levelaux_subset_complex {n : ℕ∞} : levelaux C D n ⊆ C := by
  simp_rw [← levelaux_top (C := C) (D := D)]
  exact levelaux_mono (OrderTop.le_top n)

lemma level_subset_complex {n : ℕ∞} : level C D n ⊆ C := levelaux_subset_complex

lemma closedCell_subset_levelaux (n : ℕ) (j : cell C D n) :
    closedCell n j ⊆ levelaux C D (n + 1) := by
  intro x xmem
  right
  simp_rw [mem_iUnion, exists_prop]
  refine ⟨n, (by norm_cast; exact lt_add_one n), ⟨j,xmem⟩⟩

lemma closedCell_subset_level (n : ℕ) (j : cell C D n) : closedCell n j ⊆ level C D n :=
  closedCell_subset_levelaux n j

lemma closedCell_subset_complex (n : ℕ) (j : cell C D n) : closedCell n j ⊆ C :=
  (closedCell_subset_level n j).trans
    (by simp_rw [← level_top (C := C) (D := D)]; exact level_mono le_top)

lemma openCell_subset_levelaux (n : ℕ) (j : cell C D n) : openCell n j ⊆ levelaux C D (n + 1) :=
  (openCell_subset_closedCell _ _).trans (closedCell_subset_levelaux _ _ )

lemma openCell_subset_level (n : ℕ) (j : cell C D n) : openCell n j ⊆ level C D n :=
  (openCell_subset_closedCell _ _).trans (closedCell_subset_level _ _)

lemma openCell_subset_complex (n : ℕ) (j : cell C D n) : openCell n j ⊆ C := by
  apply subset_trans (openCell_subset_level _ _)
    (by simp_rw [← level_top (C := C) (D := D)]; exact level_mono le_top)

lemma cellFrontier_subset_levelaux (n : ℕ) (j : cell C D n) :
    cellFrontier n j ⊆  levelaux C D n := by
  obtain ⟨I, hI⟩ := cellFrontier_subset_finite_closedCell n j
  refine subset_trans hI (fun x xmem ↦ ?_)
  rcases xmem with xmem | xmem
  · left
    exact xmem
  · right
    simp only [mem_iUnion, levelaux, exists_prop] at xmem ⊢
    obtain ⟨i, iltn, j, _, xmem⟩ := xmem
    exact ⟨i, by norm_cast, j, xmem⟩

lemma cellFrontier_subset_level (n : ℕ) (j : cell C D (n + 1)) :
    cellFrontier (n + 1) j ⊆ level C D n :=
  cellFrontier_subset_levelaux _ _

lemma iUnion_cellFrontier_subset_levelaux (l : ℕ) :
    ⋃ (j : cell C D l), cellFrontier l j ⊆ levelaux C D l :=
  iUnion_subset  (fun _ ↦ cellFrontier_subset_levelaux _ _)

lemma iUnion_cellFrontier_subset_level (l : ℕ) :
    ⋃ (j : cell C D l), cellFrontier l j ⊆ level C D l :=
  (iUnion_cellFrontier_subset_levelaux l).trans (levelaux_mono le_self_add)

lemma closedCell_zero_eq_singleton {j : cell C D 0} : closedCell 0 j = {map 0 j ![]} := by
  simp [closedCell, Matrix.empty_eq]

lemma openCell_zero_eq_singleton {j : cell C D 0} : openCell 0 j = {map 0 j ![]} := by
  simp [openCell, Matrix.empty_eq]

lemma cellFrontier_zero_eq_empty {j : cell C D 0} : cellFrontier 0 j = ∅ := by
  simp [cellFrontier, sphere_eq_empty_of_subsingleton]

lemma base_subset_levelaux (n : ℕ∞) : D ⊆ levelaux C D n := subset_union_left

lemma base_subset_level (n : ℕ∞) : D ⊆ level C D n := base_subset_levelaux (n + 1)

lemma base_subset_complex : D ⊆ C := by
  simp_rw [← level_top (C := C) (D := D)]
  exact base_subset_level ⊤

-- I don't know why I need to add all the hypothesese again? I think new update on hypotheses...
lemma isClosed [T2Space X] {D : Set X} [RelCWComplex C D] : IsClosed C := by
  rw [closed (C := C) (D := D) C (by rfl)]
  constructor
  · intros
    rw [inter_eq_right.2 (closedCell_subset_complex _ _)]
    exact isClosed_closedCell
  · rw [inter_eq_right.2 base_subset_complex]
    exact isClosedBase C

lemma iUnion_levelaux_eq_levelaux (n : ℕ∞) :
    ⋃ (m : ℕ) (_ : m < n + 1), levelaux C D m = levelaux C D n := by
  apply subset_antisymm
  · simp_rw [iUnion_subset_iff]
    exact fun _ h ↦  levelaux_mono (Order.le_of_lt_add_one h)
  · cases' n with n
    · intro x xmem
      rcases xmem with xmem | xmem
      · simp only [top_add, ENat.coe_lt_top, iUnion_true, mem_iUnion]
        use 0
        rwa [← levelaux_zero_eq_base (C := C) (D := D)] at xmem
      · simp only [levelaux, ENat.coe_lt_top, iUnion_true, mem_iUnion, top_add, Nat.cast_lt]
          at xmem ⊢
        obtain ⟨m, i, xmem⟩ := xmem
        use m + 1
        right
        simp_rw [mem_iUnion, exists_prop]
        exact ⟨m, lt_add_one m, ⟨i, xmem⟩⟩
    · apply subset_iUnion_of_subset n
      norm_cast
      simp

lemma iUnion_level_eq_level (n : ℕ∞) : ⋃ (m : ℕ) (_ : m < n + 1), level C D m = level C D n := by
  simp_rw [level, ← iUnion_levelaux_eq_levelaux (n + 1)]
  ext
  simp only [mem_iUnion, exists_prop]
  constructor
  · intro ⟨i, hin, hiC⟩
    refine ⟨i + 1, ?_, hiC⟩
    exact (ENat.add_lt_add_iff_right ENat.one_ne_top).mpr hin
  · intro ⟨i, hin, hiC⟩
    cases' i with i
    · refine ⟨0, ?_, levelaux_mono (by norm_num) hiC⟩
      exact ENat.add_one_pos
    · refine ⟨i, ?_, hiC⟩
      exact (ENat.add_lt_add_iff_right ENat.one_ne_top).mp hin

lemma levelaux_succ_eq_levelaux_union_iUnion_closedCell (n : ℕ) :
    levelaux C D (n + 1) = levelaux C D n ∪ ⋃ (j : cell C D n), closedCell n j := by
  rw [levelaux, levelaux, union_assoc]
  congr
  norm_cast
  exact biUnion_lt_succ _ _

lemma level_succ_eq_level_union_iUnion (n : ℕ) :
    level C D (n + 1) = level C D n ∪ ⋃ (j : cell C D (↑n + 1)), closedCell (n + 1) j :=
  levelaux_succ_eq_levelaux_union_iUnion_closedCell _

/-- A version of the definition of `levelaux` with open cells. -/
lemma iUnion_openCell_eq_levelaux (n : ℕ∞) :
    D ∪ ⋃ (m : ℕ) (_ : m < n) (j : cell C D m), openCell m j = levelaux C D n := by
  induction' n using ENat.nat_induction with n hn hn
  · simp [levelaux]
  · calc
      D ∪ ⋃ (m : ℕ), ⋃ (_ : (m : ℕ∞) < ↑n.succ), ⋃ (j : cell C D m), openCell m j
      _ = D ∪ ((⋃ m, ⋃ (_ : m < n), ⋃ j, openCell m j) ∪ ⋃ (j : cell C D n), openCell n j) := by
        congr
        norm_cast
        exact biUnion_lt_succ _ _
      _ = D ∪ (levelaux C D n ∪ ⋃ (j : cell C D n), openCell n j) := by
        simp_rw [← union_assoc, ← hn, ← union_assoc, union_self]
        norm_cast
      _ = D ∪ (levelaux C D n ∪ (⋃ (j : cell C D n), cellFrontier n j) ∪
          ⋃ (j : cell C D n), openCell n j) := by
        congr
        exact (union_eq_left.2 (iUnion_cellFrontier_subset_levelaux n)).symm
      _ = D ∪ (levelaux C D n ∪ ⋃ (j : cell C D n), closedCell n j) := by
        simp_rw [union_assoc, ← iUnion_union_distrib, cellFrontier_union_openCell_eq_closedCell]
      _ = D ∪ levelaux C D n.succ := by
        unfold levelaux
        simp_rw [union_assoc]
        congr
        norm_cast
        exact (biUnion_lt_succ _ _).symm
      _ = levelaux C D n.succ := by
        rw [union_eq_right]
        exact base_subset_levelaux n.succ
  · calc
      D ∪ ⋃ (m : ℕ), ⋃ (_ : (m : ℕ∞) < ⊤), ⋃ j, openCell m j
      _ = D ∪ ⋃ m, ⋃ (j : cell C D m), openCell m j := by
        simp_rw [ENat.coe_lt_top, iUnion_true]
      _ = D ∪ ⋃ m, ⋃ l, ⋃ (_ : l < m), ⋃ (j : cell C D l), openCell l j := by
        congr
        exact biSup_lt_eq_iSup.symm
      _ = ⋃ (m : ℕ), levelaux C D m := by
        rw [union_iUnion]
        apply iUnion_congr
        intro n
        norm_cast at hn
        exact hn n
      _ = D ∪ ⋃ m, ⋃ l, ⋃ (_ : l < m), ⋃ (j : cell C D l), closedCell l j := by
        unfold levelaux
        rw [union_iUnion]
        norm_cast
      _ = D ∪ ⋃ m, ⋃ (j : cell C D m), closedCell m j := by
        congr
        exact biSup_lt_eq_iSup
      _ = levelaux C D ⊤ := by rw [levelaux_top, union]

lemma iUnion_openCell_eq_level (n : ℕ∞) :
    D ∪ ⋃ (m : ℕ) (_ : m < n + 1) (j : cell C D m), openCell m j = level C D n :=
  iUnion_openCell_eq_levelaux _

lemma iUnion_openCell : D ∪ ⋃ (n : ℕ) (j : cell C D n), openCell n j = C := by
  simp only [← levelaux_top (C := C) (D := D), ← iUnion_openCell_eq_levelaux,
    ENat.coe_lt_top, iUnion_true]

/-- The contraposition of `disjoint_openCell_of_ne`.-/
lemma eq_cell_of_not_disjoint {n : ℕ} {j : cell C D n} {m : ℕ} {i : cell C D m}
    (notdisjoint: ¬ Disjoint (openCell n j) (openCell m i)) :
    (⟨n, j⟩ : (Σ n, cell C D n)) = ⟨m, i⟩ := by
  by_contra h'
  push_neg at h'
  apply notdisjoint
  have := pairwiseDisjoint (C := C) (D := D)
  simp only [PairwiseDisjoint, Set.Pairwise, Function.onFun] at this
  exact this (x := ⟨n, j⟩) (mem_univ _) (y := ⟨m, i⟩) (mem_univ _) h'

-- Alternatively I could add `x ∉ D` as a hypothesis
lemma exists_mem_openCell_of_mem_levelaux {n : ℕ∞} {x : X} (xmemlvl : x ∈ levelaux C D n) :
    x ∈ D ∨ ∃ (m : ℕ) (_ : m < n) (j : cell C D m), x ∈ openCell m j := by
  rw [← iUnion_openCell_eq_levelaux] at xmemlvl
  rcases xmemlvl with xmem | xmem
  · left
    exact xmem
  · right
    simp_rw [mem_iUnion] at xmem
    obtain ⟨m, mltn, j, _⟩ := xmem
    use m, mltn, j

lemma exists_mem_openCell_of_mem_level {n : ℕ∞} {x : X} (xmemlvl : x ∈ level C D n) :
    x ∈ D ∨ ∃ (m : ℕ) (_ : m ≤ n) (j : cell C D m), x ∈ openCell m j := by
  rw [level] at xmemlvl
  rcases exists_mem_openCell_of_mem_levelaux xmemlvl with xmem | xmem
  · left
    exact xmem
  · right
    obtain ⟨m, mlen, _⟩ := xmem
    use m, Order.le_of_lt_add_one mlen

/-- A level and an open cell of a higher dimension are disjoint -/
lemma levelaux_inter_openCell_eq_empty {n : ℕ∞} {m : ℕ} {j : cell C D m} (nlem : n ≤ m) :
    levelaux C D n ∩ openCell m j = ∅ := by
  -- This is a consequence of `iUnion_openCell_eq_levelaux` and `disjoint_openCell_of_ne`
  simp_rw [← iUnion_openCell_eq_levelaux, union_inter_distrib_right, iUnion_inter, union_empty_iff,
    iUnion_eq_empty]
  constructor
  · rw [← Disjoint.inter_eq]
    exact Disjoint.symm (disjointBase m j)
  intro l llt i
  apply disjoint_openCell_of_ne
  intro eq
  rw [Sigma.mk.inj_iff] at eq
  obtain ⟨eq1, eq2⟩ := eq
  subst l
  rw [heq_eq_eq] at eq2
  subst i
  exact LT.lt.false (LT.lt.trans_le llt nlem)

/-- A level and an open cell of a higher dimension are disjoint -/
lemma level_inter_openCell_eq_empty {n : ℕ∞} {m : ℕ} {j : cell C D m} (nlem : n < m) :
    level C D n ∩ openCell m j = ∅ :=
  levelaux_inter_openCell_eq_empty (Order.add_one_le_of_lt nlem)

/-- A level intersected with a closed cell of a higher dimension is the level intersected with
  the edge of the cell.-/
lemma levelaux_inter_closedCell_eq_levelaux_inter_cellFrontier {n : ℕ∞} {m : ℕ} {j : cell C D m}
    (nlem : n ≤ m) :
    levelaux C D n ∩ closedCell m j = levelaux C D n ∩ cellFrontier m j := by
  refine subset_antisymm ?_ (inter_subset_inter_right _ (cellFrontier_subset_closedCell _ _))
  rw [← cellFrontier_union_openCell_eq_closedCell, inter_union_distrib_left]
  apply union_subset (by rfl)
  rw [levelaux_inter_openCell_eq_empty nlem]
  exact empty_subset (levelaux C D n ∩ cellFrontier m j)

/-- Version of `levelaux_inter_openCell_eq_empty` using `level`.-/
lemma level_inter_closedCell_eq_level_inter_cellFrontier {n : ℕ∞} {m : ℕ} {j : cell C D m}
    (nltm : n < m) :
    level C D n ∩ closedCell m j = level C D n ∩ cellFrontier m j :=
  levelaux_inter_closedCell_eq_levelaux_inter_cellFrontier (Order.add_one_le_of_lt nltm)

/-- If for all `m ≤ n` and every `i : cell C D m` the intersection `A ∩ closedCell m j` is closed
  and `A ∩ D` is closed then `A ∩ cellFrontier (n + 1) j` is closed for every
  `j : cell C D (n + 1)`.-/
lemma isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell [T2Space X] {A : Set X}
    {n : ℕ} (hn : ∀ m ≤ n, ∀ (j : cell C D m),
    IsClosed (A ∩ closedCell m j)) (j : cell C D (n + 1)) (hD : IsClosed (A ∩ D)) :
    IsClosed (A ∩ cellFrontier (n + 1) j) := by
  -- this is a consequence of `cellFrontier_subset_finite_closedCell`
  obtain ⟨I, hI⟩ := cellFrontier_subset_finite_closedCell (n + 1) j
  rw [← inter_eq_right.2 hI, ← inter_assoc]
  refine IsClosed.inter ?_ isClosed_cellFrontier
  simp_rw [inter_union_distrib_left, inter_iUnion,
    ← iUnion_subtype (fun m ↦ m < n + 1) (fun m ↦ ⋃ i ∈ I m, A ∩ closedCell m i)]
  apply hD.union
  apply isClosed_iUnion_of_finite
  intro ⟨m, mlt⟩
  rw [← iUnion_subtype (fun i ↦ i ∈ I m) (fun i ↦ A ∩ closedCell (↑m) i.1)]
  exact isClosed_iUnion_of_finite (fun ⟨j, _⟩ ↦ hn m (Nat.le_of_lt_succ mlt) j)

/-- If for every cell either `A ∩ openCell n j` or `A ∩ closedCell n j` is closed then
  `A` is closed. -/
lemma isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell [T2Space X] {A : Set X}
    (asub : A ⊆ C) (hDA : IsClosed (A ∩ D))
    (h : ∀ n (_ : 0 < n), ∀ (j : cell C D n),
    IsClosed (A ∩ openCell n j) ∨ IsClosed (A ∩ closedCell n j)) : IsClosed A := by
  rw [closed (C := C) (D := D) A asub]
  refine ⟨?_, hDA⟩
  intro n j
  induction' n using Nat.case_strong_induction_on with n hn
  · rw [closedCell_zero_eq_singleton]
    exact isClosed_inter_singleton
  specialize h n.succ (Nat.zero_lt_succ n) j
  rcases h with h1 | h2
  · rw [← cellFrontier_union_openCell_eq_closedCell, inter_union_distrib_left]
    exact (isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell hn j hDA).union h1
  · exact h2


/-- A version of `cellFrontier_subset_finite_closedCell` using open cells: The edge of a cell is
  contained in a finite union of open cells of a lower dimension.-/
lemma cellFrontier_subset_finite_openCell (n : ℕ) (i : cell C D n) : ∃ I : Π m, Finset (cell C D m),
    cellFrontier n i ⊆ D ∪ (⋃ (m < n) (j ∈ I m), openCell m j) := by
  induction' n using Nat.case_strong_induction_on with n hn
  · simp [cellFrontier_zero_eq_empty]
  · -- We apply `cellFrontier_subset_finite_closedCell` once and then apply
    -- the induction hypothesis to the finitely many cells that
    -- `cellFrontier_subset_finite_closedCell` gives us.
    classical
    rcases cellFrontier_subset_finite_closedCell (Nat.succ n) i with ⟨J, hJ⟩
    choose p hp using hn
    let I m := J m ∪ (Finset.biUnion (Finset.range n.succ)
      (fun l ↦ Finset.biUnion (J l) (fun y ↦ if h : l ≤ n then p l h y m else ∅)))
    use I
    intro x xmem
    specialize hJ xmem
    simp only [mem_union, mem_iUnion, exists_prop] at hJ ⊢
    rcases hJ with hJ | hJ
    · left
      exact hJ
    obtain ⟨l, llen , j, jmem, xmemclosedCell⟩ := hJ
    rw [← cellFrontier_union_openCell_eq_closedCell] at xmemclosedCell
    rcases xmemclosedCell with xmemcellFrontier | xmemopenCell
    · let hK := hp l (Nat.le_of_lt_succ llen) j xmemcellFrontier
      simp_rw [mem_union, mem_iUnion, exists_prop] at hK
      rcases hK with hK | hK
      · left
        exact hK
      right
      obtain ⟨k, kltl, i, imem, xmemopenCell⟩ := hK
      use k, (lt_trans kltl llen), i
      refine ⟨?_, xmemopenCell ⟩
      simp only [Nat.succ_eq_add_one, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range, I]
      right
      use l, llen, j, jmem
      simp only [Nat.le_of_lt_succ llen, ↓reduceDIte, imem]
    · right
      use l, llen, j
      simp only [Nat.succ_eq_add_one, Finset.mem_union, I]
      exact ⟨Or.intro_left _ jmem, xmemopenCell⟩
