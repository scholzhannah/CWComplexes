import CWcomplexes.Relative.RelCwComplex

/-!
# Finite CW-complexes

In this file we define what it means for a CW-complex to finite dimensional, of finite type or
finite. We define constructors with relaxed conditions for CW-complexes of finite type and
finite CW-complexes.

## Main definitions
* `FiniteDimensional`: A CW-complex is finite dimensional if it has only finitely many
  nonempty indexing types for the cells.
* `FiniteType`: A CW-complex is of finite type if it has only finitely many cells in each dimension.
* `Finite`: A CW-complex is finite if it is finite dimensional and of finite type.

## Main statements
* `CWComplexFiniteType`: If we want to construct a CW-complex of finite type, we can relax the
  condition `mapsto`.
* `CWComplexFinite`: If we want to construct a finite CW-complex, we can relax the condition
  `mapsto` and can leave out he condition `closed'`.
* `finite_iff_finite_cells`: A CW-complex is finite iff the total number of cells is finite.
-/

open Metric Set

namespace CWComplex

/-- A CW-complex is finite dimensional if `cell C D n` is empty for all but finitely many `n`.-/
class FiniteDimensional.{u} {X : Type u} [TopologicalSpace X] (C D : Set X) [RelCWComplex C D] :
    Prop where
  /-- For some natural number `n` the type `cell C D m` is empty for all `m ≥ n`.-/
  eventually_isEmpty_cell : ∀ᶠ n in Filter.atTop, IsEmpty (cell C D n)

/-- A CW-complex is of finite type if `cell C D n` is finite for every `n`.-/
class FiniteType.{u} {X : Type u} [TopologicalSpace X] (C D : Set X) [RelCWComplex C D] : Prop where
  /-- `cell C n` is finite for every `n`.-/
  finite_cell (n : ℕ) : Finite (cell C D n)

/-- A CW-complex is finite if it is finite dimensional and of finite type.-/
class Finite.{u} {X : Type u} [TopologicalSpace X] (C : Set X) (D : Set X := ∅) [RelCWComplex C D] :
    Prop where
  /-- For some natural number `n` the type `cell C D m` is empty for all `m ≥ n`.-/
  eventually_isEmpty_cell : ∀ᶠ n in Filter.atTop, IsEmpty (cell C D n)
  /-- `cell C D n` is finite for every `n`.-/
  finite_cell (n : ℕ) : _root_.Finite (cell C D n)

/-- If we want to construct a relative CW-complex of finite type, we can add the condition
  `finite_cell` and relax the condition `mapsto`.-/
def RelCWComplexFiniteType.{u} {X : Type u} [TopologicalSpace X] (C D : Set X)
    (cell : (n : ℕ) → Type u) (map : (n : ℕ)  → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = closedBall 0 1)
    (cont : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (cont_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (disjointBase' : ∀ (n : ℕ) (i : cell n), Disjoint (map n i '' ball 0 1) D)
    (mapsto : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (closed' : ∀ (A : Set X) (asubc : A ⊆ C),
    ((∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) ∧ IsClosed (A ∩ D)) → IsClosed A)
    (isClosedBase : IsClosed D)
    (union' : D ∪ ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
    RelCWComplex C D where
  cell := cell
  map := map
  source_eq := source_eq
  cont := cont
  cont_symm := cont_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  disjointBase' := disjointBase'
  mapsto n i := by
    use fun m ↦ finite_univ.toFinset (s := (univ : Set (cell m)))
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true]
    exact mapsto n i
  closed' := closed'
  isClosedBase := isClosedBase
  union' := union'

/-- If we want to construct a CW-complex of finite type, we can add the condition `finite_cell` and
  relax the condition `mapsto`.-/
def CWComplexFiniteType.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (cell : (n : ℕ) → Type u) (map : (n : ℕ)  → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = closedBall 0 1)
    (cont : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (cont_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (mapsto : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (closed' : ∀ (A : Set X) (asubc : A ⊆ C),
    (∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) → IsClosed A)
    (union' :  ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
    CWComplex C where
  cell := cell
  map := map
  source_eq := source_eq
  cont := cont
  cont_symm := cont_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  disjointBase' := by simp only [disjoint_empty, implies_true]
  mapsto n i := by
    use fun m ↦ finite_univ.toFinset (s := (univ : Set (cell m)))
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true, empty_union]
    exact mapsto n i
  closed' := by simpa only [inter_empty, isClosed_empty, and_true]
  isClosedBase := isClosed_empty
  union' := by simpa only [empty_union]

/-- If we want to construct a finite relative CW-complex we can add the conditions
  `eventually_isEmpty_cell` and `finite_cell`, relax the condition `mapsto` and remove the condition
   `closed'`.-/
def RelCWComplexFinite.{u} {X : Type u} [TopologicalSpace X] [T2Space X] (C D : Set X)
    (cell : (n : ℕ) → Type u)
    (map : (n : ℕ)  → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (eventually_isEmpty_cell : ∀ᶠ n in Filter.atTop, IsEmpty (cell n))
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = closedBall 0 1)
    (cont : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (cont_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (disjointBase' : ∀ (n : ℕ) (i : cell n), Disjoint (map n i '' ball 0 1) D)
    (mapsto : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (isClosedBase : IsClosed D)
    (union' : D ∪ ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
    RelCWComplex C D where
  cell := cell
  map := map
  source_eq := source_eq
  cont := cont
  cont_symm := cont_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  disjointBase' := disjointBase'
  mapsto n i := by
    use fun m ↦ finite_univ.toFinset (s := (univ : Set (cell m)))
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true]
    exact mapsto n i
  closed' A asubc := by
    intro h
    -- `A = A ∩ C = A ∩ ⋃ n, ⋃ j, closedCell n j` is closed by assumption since `C` has only
    -- finitely many cells.
    rw [← inter_eq_left.2 asubc]
    simp_rw [Filter.eventually_atTop, ge_iff_le] at eventually_isEmpty_cell
    obtain ⟨N, hN⟩ := eventually_isEmpty_cell
    suffices IsClosed (A ∩ (D ∪ ⋃ (n : {n : ℕ // n < N}), ⋃ j, ↑(map n j) '' closedBall 0 1)) by
      convert this using 2
      rw [← union', iUnion_subtype]
      congr
      apply iUnion_congr
      intro n
      ext x
      nth_rw 2 [mem_iUnion]
      refine ⟨fun xmem ↦ ⟨?_, xmem⟩, fun ⟨_, h⟩ ↦ h⟩
      by_contra h
      push_neg at h
      simp only [hN n h, iUnion_of_empty, mem_empty_iff_false] at xmem
    simp_rw [inter_union_distrib_left, inter_iUnion]
    exact h.2.union (isClosed_iUnion_of_finite (fun n ↦ isClosed_iUnion_of_finite (h.1 n.1)))
  isClosedBase := isClosedBase
  union' := union'

/-- If we want to construct a finite relative CW-complex we can add the conditions
  `eventually_isEmpty_cell` and `finite_cell`, relax the condition `mapsto` and remove the condition
   `closed'`.-/
def CWComplexFinite.{u} {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X)
    (cell : (n : ℕ) → Type u)
    (map : (n : ℕ)  → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (eventually_isEmpty_cell : ∀ᶠ n in Filter.atTop, IsEmpty (cell n))
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = closedBall 0 1)
    (cont : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (cont_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (mapsto : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (union' : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
    CWComplex C := RelCWComplexFinite C ∅
  (cell := cell)
  (map := map)
  (eventually_isEmpty_cell := eventually_isEmpty_cell)
  (finite_cell := finite_cell)
  (source_eq := source_eq)
  (cont := cont)
  (cont_symm := cont_symm)
  (pairwiseDisjoint' := pairwiseDisjoint')
  (disjointBase' := by simp only [disjoint_empty, implies_true])
  (mapsto := by simpa only [empty_union])
  (isClosedBase := isClosed_empty)
  (union' := by simpa only [empty_union])

variable {X : Type*} [TopologicalSpace X] {C D : Set X} [RelCWComplex C D]

variable {X : Type*} [t : TopologicalSpace X] {C D : Set X} [RelCWComplex C D]

lemma finite_of_finite_cells (finite : _root_.Finite (Σ n, cell C D n)) : Finite C D where
  eventually_isEmpty_cell := by
    simp only [Filter.eventually_atTop, ge_iff_le]
    by_cases h : IsEmpty (Σ n, cell C D n)
    · use 0
      intro n _
      rw [isEmpty_sigma] at h
      exact h n
    -- We take the greatest `n` such that there is a `j : cell C n` and show that this fulfils
    -- the necessary conditions.
    rw [not_isEmpty_iff] at h
    have _ := Fintype.ofFinite (Σ n, cell C D n)
    classical
    let A := (Finset.univ : Finset (Σ n, cell C D n)).image Sigma.fst
    use A.max' (Finset.image_nonempty.2 Finset.univ_nonempty) + 1
    intro m _
    by_contra h'
    have mmem : m ∈ A := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, A]
      simp only [not_isEmpty_iff, ← exists_true_iff_nonempty] at h'
      obtain ⟨j, _⟩ := h'
      use ⟨m, j⟩
    linarith [A.le_max' m mmem]
  finite_cell := fun _ ↦ Finite.of_injective (Sigma.mk _) sigma_mk_injective

lemma finite_cells_of_finite (finite : Finite C D) : _root_.Finite (Σ n, cell C D n) := by
  -- We show that there is a bijection between `Σ n, cell C n` and
  -- `Σ (m : {m : ℕ // m < n}), cell C m`.
  have finitelvl := finite.eventually_isEmpty_cell
  have _ := finite.finite_cell
  simp only [Filter.eventually_atTop, ge_iff_le] at finitelvl
  rcases finitelvl with ⟨n, hn⟩
  have : ∀ m (j : cell C D m), m < n := by
    intro m j
    by_contra h
    exact (hn m (not_lt.1 h)).false j
  let f : (Σ (m : {m : ℕ // m < n}), cell C D m) ≃ Σ m, cell C D m := {
    toFun := fun ⟨m, j⟩ ↦ ⟨m, j⟩
    invFun := fun ⟨m, j⟩ ↦ ⟨⟨m, this m j⟩, j⟩
    left_inv := by simp only [Function.LeftInverse, implies_true]
    right_inv := by simp only [Function.RightInverse, Function.LeftInverse, Sigma.eta, implies_true]
  }
  rw [← Equiv.finite_iff f]
  exact Finite.instSigma

lemma finite_iff_finite_cells : Finite C D ↔ _root_.Finite (Σ n, cell C D n) :=
  ⟨finite_cells_of_finite, finite_of_finite_cells⟩
