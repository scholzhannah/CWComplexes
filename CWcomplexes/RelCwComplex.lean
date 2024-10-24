import CWcomplexes.Auxiliary
import Mathlib.Analysis.NormedSpace.Real


noncomputable section

open Metric Set

-- Should closedD be part of the definition.

/-- Characterizing when a subspace `C` of a topological space `X` is a CW-complex.
  Note that this requires `C` to be a closed subspace. Otherwise choose `X` to be `C`.
  A lot of lemmas will require `[T2Space X]`.-/
class RelCWComplex.{u} {X : Type u} [TopologicalSpace X] (C Dense : Set X) where
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
    the namespace `CWComplex` instead. -/
  pairwiseDisjoint' :
    (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1)
  /-- The edge of a cell is contained in a finite union of closed cells of a lower dimension.
    Use `cellFrontier_subset_finite_closedCell` in the namespace `CWComplex` instead.-/
  mapsto (n : ℕ) (i : cell n) : ∃ I : Π m, Finset (cell m),
    MapsTo (map n i) (sphere 0 1) (D ∪ ⋃ (m < n) (j ∈ I m), map m j '' closedBall 0 1)
  /-- A CW-complex has weak topology, i.e. a set `A` in `X` is closed iff its intersection with
    every closed cell and `D` is closed. Use `closed` in the namespace `CWComplex` instead.-/
  closed' (A : Set X) (asubc : A ⊆ C) :
    ((∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) ∧ IsClosed (A ∩ D)) → IsClosed A
  /-- The union of all closed cells equals `C`. Use `union` in the namespace `CWComplex` instead.-/
  union' : D ∪ ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C

namespace RelCWComplex

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
  (univ : Set (Σ n, cell C D n)).PairwiseDisjoint (fun ni ↦ openCell ni.1 ni.2) := pairwiseDisjoint'

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

lemma union : D ∪ ⋃ (n : ℕ) (j : cell C D n), closedCell n j = C := union'

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

lemma closed [T2Space X] (closedD : IsClosed D) (A : Set X) (asubc : A ⊆ C) :
    IsClosed A ↔ (∀ n (j : cell C D n), IsClosed (A ∩ closedCell n j)) ∧ IsClosed (A ∩ D) := by
  constructor
  · intro closedA
    constructor
    · intro n j
      exact closedA.inter isClosed_closedCell
    · exact closedA.inter closedD
  · exact closed' A asubc

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
  simp [cellFrontier, sphere_zero_dim_empty]

lemma base_subset_levelaux (n : ℕ∞) : D ⊆ levelaux C D n := subset_union_left

lemma base_subset_level (n : ℕ∞) : D ⊆ level C D n := base_subset_levelaux (n + 1)

lemma base_subset_complex : D ⊆ C := by
  simp_rw [← level_top (C := C) (D := D)]
  exact base_subset_level ⊤

lemma isClosed [T2Space X] (closedD : IsClosed D) : IsClosed C := by
  rw [closed closedD _ (by rfl)]
  constructor
  · intros
    rw [inter_eq_right.2 (closedCell_subset_complex _ _)]
    exact isClosed_closedCell
  · rw [inter_eq_right.2 base_subset_complex]
    exact closedD

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
    exact (ENat.add_finite_lt_add_finite_right ENat.one_ne_top).mpr hin
  · intro ⟨i, hin, hiC⟩
    cases' i with i
    · refine ⟨0, ?_, levelaux_mono (by norm_num) hiC⟩
      exact ENat.add_one_pos
    · refine ⟨i, ?_, hiC⟩
      exact (ENat.add_finite_lt_add_finite_right ENat.one_ne_top).mp hin

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
        exact (biSup_lt_eq_iSup _).symm
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
        exact biSup_lt_eq_iSup _
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
