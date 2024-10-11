import CWcomplexes.Auxiliary
import Mathlib.Analysis.NormedSpace.Real


noncomputable section

open Metric Set

/-- Characterizing when a subspace `C` of a topological space `X` is a CW-complex.
  Note that this requires `C` to be a closed subspace. Otherwise choose `X` to be `C`.
  A lot of lemmas will require `[T2Space X]`.-/
class CWComplex.{u} {X : Type u} [TopologicalSpace X] (C : Set X) (D : Set X) where
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
    every closed cell is closed. Use `closed` in the namespace `CWComplex` instead.-/
  -- this needs some thinking
  closed' (A : Set X) (asubc : A ⊆ C) : IsClosed A ↔
    ∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1) ∧ IsClosed (A ∩ D)
  /-- The union of all closed cells equals `C`. Use `union` in the namespace `CWComplex` instead.-/
  union' : D ∪ ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C
