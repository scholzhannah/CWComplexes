import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Homotopy.HomotopyGroup

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open Metric Set

variable {X : Type*} [t : TopologicalSpace X]

/- Characterizing when a set is a CW-complex. See [Hatcher, Proposition A.2].
Generally we will need `[T2Space X]`.
Note that we are changing the definition a little bit: we are saying that a subspace `C` of `X` is a
`CW-complex`. -/
structure CWComplex.{u} {X : Type u} [TopologicalSpace X] (C : Set X) where
  cell (n : ℕ) : Type u
  map (n : ℕ) (i : cell n) : PartialEquiv (Fin n → ℝ) X
  -- note: "spheres" in `Fin n → ℝ` are actually cubes.
  -- We can also use `EuclideanSpace ℝ n` to have actual spheres.
  source_eq (n : ℕ) (i : cell n) : (map n i).source = closedBall 0 1
  cont (n : ℕ) (i : cell n) : ContinuousOn (map n i) (closedBall 0 1)
  cont_symm (n : ℕ) (i : cell n) : ContinuousOn (map n i).symm (map n i).target
  pairwiseDisjoint :
    (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1)
  mapsto (n : ℕ) (i : cell n) : ∃ I : Π m, Finset (cell m),
    MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j ∈ I m), map m j '' closedBall 0 1)
  closed (A : Set X) : IsClosed A ↔ ∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)
  union : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C

variable [T2Space X] {C : Set X} (hC : CWComplex C)

namespace CWComplex

/- The `n`-th level of a CW-complex, for `n ∈ ℕ ∪ ∞`. -/
def level (n : ℕ∞) : Set X :=
  ⋃ (m : ℕ) (hm : m < n) (j : hC.cell m), hC.map m j '' closedBall 0 1

/- Every `map` restricts to a homeomorphism between `ball 0 1` and its image.
Note: `PartialHomeomorph` requires that it's source and target are open. -/
def mapHomeo (n : ℕ) (i : hC.cell n) : PartialHomeomorph (Fin n → ℝ) X where
  toFun := hC.map n i
  invFun := (hC.map n i).symm
  source := ball 0 1
  target := hC.map n i '' ball 0 1
  map_source' := fun x xmem ↦ mem_image_of_mem ↑(hC.map n i) xmem
  map_target' := by
    intro x xmem
    rcases xmem with ⟨a, amem, rfl⟩
    rw [PartialEquiv.left_inv]
    apply amem
    rw [source_eq]
    apply ball_subset_closedBall amem
  left_inv' := by
    intro x xmem
    apply PartialEquiv.left_inv
    rw [source_eq]; apply ball_subset_closedBall xmem
  right_inv' := by
    intro x xmem
    apply PartialEquiv.right_inv
    rw [← PartialEquiv.image_source_eq_target, source_eq]
    exact (image_subset ↑(hC.map n i) ball_subset_closedBall) xmem
  open_source := isOpen_ball
  open_target := sorry /- Is this even true? Because in the typical
  definition of a CW-complex an open cell is only open in its dimension.-/
  continuousOn_toFun := by
    simp
    have := hC.cont n i
    rw [_root_.continuousOn_iff] at this
    rw [_root_.continuousOn_iff]
    intro x xmemball a aopen mapxmem
    rcases this x (ball_subset_closedBall xmemball) a aopen mapxmem with ⟨y, yopen, xmemy, ycapcball⟩
    use y
    have : y ∩ ball 0 1 ⊆ y ∩ closedBall 0 1 := by
      apply inter_subset_inter_right
      exact ball_subset_closedBall
    exact ⟨yopen, ⟨xmemy, subset_trans this ycapcball⟩⟩
  continuousOn_invFun := by
    simp
    have contsymm := hC.cont_symm n i
    rw [_root_.continuousOn_iff] at contsymm
    rw [_root_.continuousOn_iff]
    intro x xmemball a aopen mapxmem
    have : ↑(hC.map n i) '' ball 0 1 ⊆ (hC.map n i).target := by
      rw [← PartialEquiv.image_source_eq_target, source_eq]
      apply image_subset
      exact ball_subset_closedBall
    rcases contsymm x (this xmemball) a aopen mapxmem with ⟨y, yopen, xmemy, ycapcball⟩
    use y
    have : y ∩ ↑(hC.map n i) '' ball 0 1 ⊆ y ∩ (hC.map n i).target := by
      apply inter_subset_inter_right
      exact this
    exact ⟨yopen, ⟨xmemy, subset_trans this ycapcball⟩⟩

@[simp] lemma level_top : hC.level ⊤ = C := by
  have : C = ⋃ (n : ℕ) (j : hC.cell n), hC.map n j '' closedBall 0 1 := by
    rw [hC.union]
  simp only [this]
  rw [CWComplex.level]
  ext x
  repeat rw [mem_iUnion₂, mem_iUnion]
  constructor
  · intro ⟨i, ⟨_, xmem⟩⟩
    use i
  · intro ⟨i, xmem⟩
    use i
    have : i < (⊤ : ENat) := by
      apply Ne.lt_top
      apply WithTop.nat_ne_top
    use this

/- We can also define the levels using `ball` instead of `closedBall`, using assumption `mapsto`. -/
lemma iUnion_ball_eq_level (n : ℕ∞) :
    ⋃ (m : ℕ) (hm : m < n) (j : hC.cell m), hC.map m j '' ball 0 1 = hC.level n := by
  sorry

def CWComplex_level (n : ℕ∞) : CWComplex (hC.level n) := by
  sorry

/- The following lemmas are already hard! -/

/- The levels are closed. The following might be helpful:
https://math.stackexchange.com/questions/4051497/subcomplex-is-closed -/
lemma isClosed_level (n : ℕ∞) : IsClosed (hC.level n) := sorry


/- The following is one way of stating that `level 0` is discrete. -/
lemma isDiscrete_level_zero {A : Set X} : IsClosed (A ∩ hC.level 0) := sorry


/- State some more properties: e.g.
* `C` is closed
* the disjoint union of two CW-complexes (in the same space `X`) is a CW-complex
  (maybe you need to require that the subspaces are separated by neighborhoods)
-/

/- Define subcomplexes and quotients -/

/- Prove some of the results in Hatcher, appendix A. -/
