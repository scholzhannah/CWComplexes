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
  ⋃ (m : ℕ) (hm : m < n) (j : hC.cell m), hC.map m j '' closedBall 0 1 -- should this be m ≤ n instead of m < n

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


-- I feel like this proof should be wayyy shorter. Correct usage of protected?
protected lemma aux1 (l : ℕ) (Y : (m : ℕ) → hC.cell m → Set X):
    ⋃ m, ⋃ (_ : m < Nat.succ l), ⋃ j, Y m j = (⋃ (j : hC.cell l), Y l j) ∪ ⋃ m, ⋃ (_ : m < l), ⋃ j, Y m j := by
  ext x
  constructor
  · intro xmem
    rw [mem_iUnion] at xmem
    simp only [mem_iUnion, exists_prop] at xmem
    rcases xmem with ⟨i, ilel, ⟨e, xmeme⟩⟩
    rw [Nat.lt_succ] at ilel
    rw [mem_union]
    by_cases h : i = l
    · left
      rw [mem_iUnion, ← h]
      use e
    · push_neg at h
      have iltl := LE.le.lt_of_ne ilel h
      right
      rw [mem_iUnion]
      use i
      rw [mem_iUnion]
      use iltl
      rw [mem_iUnion]
      use e
  · intro xmem
    rw [mem_union] at xmem
    simp only [mem_iUnion, exists_prop]
    rcases xmem with h | h
    · use l
      constructor
      · apply Nat.lt_succ_self
      · rw [← mem_iUnion]
        exact h
    · simp only [mem_iUnion, exists_prop] at h
      rcases h with ⟨m, mltl, existsxmem⟩
      use m
      constructor
      · apply lt_trans mltl (Nat.lt_succ_self l)
      · exact existsxmem

protected lemma aux2 (l : ℕ) : ⋃ (j : hC.cell l), ↑(hC.map l j) '' sphere 0 1 ⊆ hC.level l := by
  rw [CWComplex.level]
  norm_cast
  intro x xmem
  rw [mem_iUnion] at xmem
  rcases xmem with ⟨e, xmeme⟩
  rcases hC.mapsto l e with ⟨I, hI⟩
  apply MapsTo.image_subset at hI
  apply hI at xmeme
  have : ⋃ m, ⋃ (_ : m < l), ⋃ j ∈ I m, ↑(hC.map m j) '' closedBall 0 1 ⊆ ⋃ m, ⋃ (_ : m < l), ⋃ j, ↑(hC.map m j) '' closedBall 0 1 := by
    apply iUnion_mono
    intro i
    apply iUnion_mono
    intro _
    intro y ymem
    rw [mem_iUnion] at ymem
    rcases ymem with ⟨f, hf⟩
    simp only [mem_iUnion, exists_prop] at hf
    rw [mem_iUnion]
    use f
    exact hf.2
  exact this xmeme

lemma level_subset_level_of_le {n m : ℕ∞} (h : m ≤ n) : hC.level m ⊆ hC.level n := by
  repeat rw [CWComplex.level]
  intro x xmem
  rw [mem_iUnion] at xmem
  rcases xmem with ⟨l , xmeml⟩
  simp only [mem_iUnion, exists_prop] at xmeml
  rw [mem_iUnion]
  use l
  simp only [mem_iUnion, exists_prop]
  constructor
  · apply lt_of_lt_of_le xmeml.1 h
  · exact xmeml.2

lemma iUnion_level_eq_level (n : ℕ∞) : ⋃ (m : ℕ) (hm : m < n + 1), hC.level m = hC.level n := by
  apply subset_antisymm
  · intro x xmem
    rw [mem_iUnion] at xmem
    rcases xmem with ⟨m, xmemm⟩
    simp at xmemm
    have h : m ≤ n := by
      apply Order.le_of_lt_succ
      rw [ENat.succ_def]
      exact xmemm.1
    exact (hC.level_subset_level_of_le h) xmemm.2
  · intro x xmem
    rw [mem_iUnion]
    by_cases h : n = ⊤
    · rw [h, top_add]
      rw [h, CWComplex.level, mem_iUnion] at xmem
      rcases xmem with ⟨i, xmemi⟩
      simp only [mem_iUnion, exists_prop] at xmemi
      use i + 1
      simp
      constructor
      · rw [WithTop.add_lt_top]
        exact ⟨xmemi.1 , (by apply lt_top_iff_ne_top.2 (WithTop.nat_ne_top 1))⟩
      rw [CWComplex.level, mem_iUnion]
      use i
      simp only [mem_iUnion, exists_prop]
      norm_cast
      exact ⟨lt_add_one i, xmemi.2⟩
    · push_neg at h
      let m := ENat.toNat n
      have coemn: ↑m = n := ENat.coe_toNat h
      rw [← coemn]
      use m
      simp
      norm_cast
      rw [coemn]
      exact ⟨lt_add_one m, xmem⟩

/- We can also define the levels using `ball` instead of `closedBall`, using assumption `mapsto`. -/
lemma iUnion_ball_eq_level (n : ℕ∞) :
    ⋃ (m : ℕ) (hm : m < n) (j : hC.cell m), hC.map m j '' ball 0 1 = hC.level n := by
  have hnat : ∀ (l : ℕ), ⋃ (m : ℕ) (hm : m < l) (j : hC.cell m), hC.map m j '' ball 0 1 = hC.level l := by
    intro l
    induction' l with l hl
    · simp [CWComplex.level]
    rw [CWComplex.aux1 hC l (fun m j ↦ ↑(hC.map m j) '' ball 0 1)]
    rw [hl]
    nth_rewrite 2 [CWComplex.level]
    norm_cast
    symm
    calc
      ⋃ m, ⋃ (_ : m < Nat.succ l), ⋃ j, ↑(hC.map m j) '' closedBall 0 1
      = (⋃ (j : hC.cell l), ↑(hC.map l j) '' closedBall 0 1) ∪ ⋃ m, ⋃ (_ : Nat.cast m < ↑l), ⋃ j, ↑(hC.map m j) '' closedBall 0 1 := by
        apply CWComplex.aux1 hC l (fun m j ↦ ↑(hC.map m j) '' closedBall 0 1)
      _ = (⋃ (j : hC.cell l), ↑(hC.map l j) '' closedBall 0 1) ∪ hC.level l := by
        rw [CWComplex.level]
        norm_cast
      _ = (⋃ (j : hC.cell l), ↑(hC.map l j) '' (sphere 0 1 ∪ ball 0 1)) ∪ hC.level l := by rw [sphere_union_ball]
      _ = (⋃ (j : hC.cell l), ↑(hC.map l j) '' sphere 0 1 ∪ ↑(hC.map l j) '' ball 0 1) ∪ hC.level l := by
        have : ⋃ (j : hC.cell l), ↑(hC.map l j) '' (sphere 0 1 ∪ ball 0 1) = ⋃ (j : hC.cell l), ↑(hC.map l j) '' sphere 0 1 ∪ ↑(hC.map l j) '' ball 0 1 := by
          apply iUnion_congr
          intro i
          rw [image_union]
        rw [this]
      _ = (⋃ (j : hC.cell l), ↑(hC.map l j) '' sphere 0 1) ∪ (⋃ (j : hC.cell l), ↑(hC.map l j) '' ball 0 1) ∪ hC.level l := by
        rw [iUnion_union_distrib]
      _ = (⋃ (j : hC.cell l), ↑(hC.map l j) '' ball 0 1) ∪ ((⋃ (j : hC.cell l), ↑(hC.map l j) '' sphere 0 1) ∪ hC.level l) := by
        rw [← union_assoc, union_comm (⋃ j, ↑(hC.map l j) '' sphere 0 1), union_assoc]
      _ = (⋃ j, ↑(hC.map l j) '' ball 0 1) ∪ level hC ↑l := by
        have : (⋃ (j : hC.cell l), ↑(hC.map l j) '' sphere 0 1) ∪ hC.level l = hC.level l := union_eq_right.2 (hC.aux2 l)
        rw [this]
  by_cases h : n = ⊤
  · rw [h]
    have : ⋃ (m : ℕ), ⋃ (_ : ↑m < (⊤ : ℕ∞)), ⋃ j, ↑(hC.map m j) '' ball 0 1 = ⋃ (n : ℕ) (hn : ↑n < (⊤ : ℕ∞)), ⋃ (m : ℕ) (hm : m < n), ⋃ j, ↑(hC.map m j) '' ball 0 1 := by
      apply subset_antisymm
      · intro x xmem
        rw [mem_iUnion] at xmem
        rcases xmem with ⟨i, xmemi⟩
        simp only [mem_iUnion, exists_prop] at xmemi
        rw [mem_iUnion]
        use i + 1
        simp only [mem_iUnion, exists_prop]
        constructor
        · rw [ENat.coe_add, WithTop.add_lt_top]
          exact ⟨xmemi.1 , (by apply lt_top_iff_ne_top.2 (WithTop.nat_ne_top 1))⟩
        · use i
          exact ⟨lt_add_one i, xmemi.2⟩
      · intro x xmem
        simp only [mem_iUnion, exists_prop] at xmem
        rcases xmem with ⟨_, ⟨_, ⟨i, ⟨_, xmemi⟩⟩⟩⟩
        simp only [mem_iUnion, exists_prop]
        use i
        exact ⟨(by apply lt_top_iff_ne_top.2 (WithTop.nat_ne_top i)), xmemi⟩
    rw [this, ← hC.iUnion_level_eq_level ⊤, top_add]
    apply iUnion_congr
    intro i
    rw [hnat]
  · push_neg at h
    let m := ENat.toNat n
    have coemn: ↑m = n := ENat.coe_toNat h
    rw [← coemn]
    norm_cast
    exact hnat m


/- I have no idea how to work with definitions by cases. Need help to progress with this part.-/
def CWComplex_level (n : ℕ∞) : CWComplex (hC.level n) := by sorry
  -- cell l := ite (l < n) (hC.cell l) PEmpty


/- The following lemmas are already hard! -/

lemma isClosed_map_closedBall (n : ℕ) (i : hC.cell n) : IsClosed (hC.map n i '' closedBall 0 1) := by
  apply IsCompact.isClosed
  apply IsCompact.image_of_continuousOn
  apply isCompact_closedBall
  exact hC.cont n i

lemma isClosed : IsClosed C := by
  rw [hC.closed]
  intro n i
  have : ↑(hC.map n i) '' closedBall 0 1 ⊆ C := by
    simp_rw [← hC.union]
    apply Set.subset_iUnion_of_subset n
    apply Set.subset_iUnion (fun j ↦ ↑(hC.map n j) '' closedBall 0 1)
  rw [Set.inter_eq_right.2 this]
  exact hC.isClosed_map_closedBall n i

/- The levels are closed. The following might be helpful:
https://math.stackexchange.com/questions/4051497/subcomplex-is-closed -/
lemma isClosed_level (n : ℕ∞) : IsClosed (hC.level n) := by
  by_cases h : n = ⊤
  · rw [h]
    rw [level_top]
    exact hC.isClosed
  push_neg at h
  let m := ENat.toNat n
  have coemn: ↑m = n := ENat.coe_toNat h
  rw [← coemn]
  induction' m with m hm
  · sorry


/- The following is one way of stating that `level 0` is discrete. -/
lemma isDiscrete_level_zero {A : Set X} : IsClosed (A ∩ hC.level 0) := sorry


/- State some more properties: e.g.
* `C` is closed
* the disjoint union of two CW-complexes (in the same space `X`) is a CW-complex
  (maybe you need to require that the subspaces are separated by neighborhoods)
-/

/- Define subcomplexes and quotients -/

/- Prove some of the results in Hatcher, appendix A. -/
