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
  closed (A : Set X) (asubc : A ⊆ ↑C) : IsClosed A ↔ ∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)
  -- I added asubc because if not I don't think the levels are CW-Complexes
  -- would A : Set C be better?
  union : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C

variable [T2Space X] {C : Set X} (hC : CWComplex C)

namespace CWComplex

/- The `n`-th level of a CW-complex, for `n ∈ ℕ ∪ ∞`. -/
/- Would it be possible to add a -1 to make induction proofs easier? -/
def level (n : ℕ∞) : Set X :=
  ⋃ (m : ℕ) (hm : m < n + 1) (j : hC.cell m), hC.map m j '' closedBall 0 1 -- I changed this from m < n to m < n + 1

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
    apply ContinuousOn.mono (hC.cont n i) ball_subset_closedBall
  continuousOn_invFun := by
    have : ↑(hC.map n i) '' ball 0 1 ⊆ (hC.map n i).target := by
      rw [← PartialEquiv.image_source_eq_target, source_eq]
      apply image_subset
      exact ball_subset_closedBall
    apply ContinuousOn.mono (hC.cont_symm n i) this

@[simp] lemma level_top : hC.level ⊤ = C := by
  simp only [level, top_add, lt_top_iff_ne_top, ne_eq, ENat.coe_ne_top, not_false_eq_true, iUnion_true, ← hC.union]

-- I feel like this proof should be wayyy shorter. Correct usage of protected?
protected lemma aux1 (l : ℕ) (Y : (m : ℕ) → hC.cell m → Set X):
    ⋃ m, ⋃ (_ : m < Nat.succ l), ⋃ j, Y m j = (⋃ (j : hC.cell l), Y l j) ∪ ⋃ m, ⋃ (_ : m < l), ⋃ j, Y m j := by
  ext x
  simp only [mem_iUnion, exists_prop, mem_union]
  constructor
  · intro ⟨i, ⟨iltsuccl, h⟩⟩
    apply Order.le_of_lt_succ at iltsuccl
    by_cases h' : i = l
    · left
      rw [h'] at h
      exact h
    · push_neg at h'
      have := LE.le.lt_of_ne iltsuccl h'
      right
      use i
  · intro h
    rcases h with h | h
    · use l
      exact ⟨Nat.lt_succ_self l, h⟩
    · rcases h with ⟨i, iltl, h⟩
      use i
      exact ⟨lt_trans iltl (Nat.lt_succ_self l), h⟩

protected lemma aux2 (l : ℕ) : ⋃ (j : hC.cell (l + 1)), ↑(hC.map (l + 1) j) '' sphere 0 1 ⊆ hC.level l := by
  rw [CWComplex.level]
  norm_cast
  intro x xmem
  rw [mem_iUnion] at xmem
  rcases xmem with ⟨e, xmeme⟩
  rcases hC.mapsto (l + 1) e with ⟨I, hI⟩
  apply MapsTo.image_subset at hI
  apply hI at xmeme
  have : ⋃ m, ⋃ (_ : m < l + 1), ⋃ j ∈ I m, ↑(hC.map m j) '' closedBall 0 1 ⊆ ⋃ m, ⋃ (_ : m < l + 1), ⋃ j, ↑(hC.map m j) '' closedBall 0 1 := by
    apply iUnion_mono
    simp only [iUnion_subset_iff]
    intro i iltl e ememIi y ymem
    simp only [mem_iUnion, exists_prop]
    exact ⟨iltl, ⟨e, ymem⟩⟩
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
  · exact lt_of_lt_of_le xmeml.1 (add_le_add_right h 1)
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
      exact ⟨lt_trans (lt_add_one i) (lt_add_one (i + 1)), xmemi.2⟩
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
    ⋃ (m : ℕ) (hm : m < n + 1) (j : hC.cell m), hC.map m j '' ball 0 1 = hC.level n := by
  have hnat : ∀ (l : ℕ), ⋃ (m : ℕ) (hm : m < l + 1) (j : hC.cell m), hC.map m j '' ball 0 1 = hC.level l := by
    intro l
    induction' l with l hl
    · simp [CWComplex.level, Matrix.empty_eq]
    rw [CWComplex.aux1 hC (Nat.succ l) (fun m j ↦ ↑(hC.map m j) '' ball 0 1)]
    rw [hl]
    nth_rewrite 2 [CWComplex.level]
    norm_cast
    symm
    calc
      ⋃ m, ⋃ (_ : m < Nat.succ l + 1), ⋃ j, ↑(hC.map m j) '' closedBall 0 1
      = (⋃ (j : hC.cell (l + 1)), ↑(hC.map (l + 1) j) '' closedBall 0 1) ∪ ⋃ m, ⋃ (_ : Nat.cast m < ↑l + 1), ⋃ j, ↑(hC.map m j) '' closedBall 0 1 := by
        apply CWComplex.aux1 hC (l + 1) (fun m j ↦ ↑(hC.map m j) '' closedBall 0 1)
      _ = (⋃ (j : hC.cell (l + 1)), ↑(hC.map (l + 1) j) '' closedBall 0 1) ∪ hC.level l := by
        rw [CWComplex.level]
        norm_cast
      _ = (⋃ (j : hC.cell (l + 1)), ↑(hC.map (l + 1) j) '' (sphere 0 1 ∪ ball 0 1)) ∪ hC.level l := by rw [sphere_union_ball]
      _ = (⋃ (j : hC.cell (l + 1)), ↑(hC.map (l + 1) j) '' sphere 0 1 ∪ ↑(hC.map (l + 1) j) '' ball 0 1) ∪ hC.level l := by
        have : ⋃ (j : hC.cell (l + 1)), ↑(hC.map (l + 1) j) '' (sphere 0 1 ∪ ball 0 1) = ⋃ (j : hC.cell (l + 1)), ↑(hC.map (l + 1) j) '' sphere 0 1 ∪ ↑(hC.map (l + 1) j) '' ball 0 1 := by
          apply iUnion_congr
          intro i
          rw [image_union]
        rw [this]
      _ = (⋃ (j : hC.cell (l + 1)), ↑(hC.map (l + 1) j) '' sphere 0 1) ∪ (⋃ (j : hC.cell (l + 1)), ↑(hC.map (l + 1) j) '' ball 0 1) ∪ hC.level l := by
        rw [iUnion_union_distrib]
      _ = (⋃ (j : hC.cell (l + 1)), ↑(hC.map (l + 1) j) '' ball 0 1) ∪ ((⋃ (j : hC.cell (l + 1)), ↑(hC.map (l + 1) j) '' sphere 0 1) ∪ hC.level l) := by
        rw [← union_assoc, union_comm (⋃ j, ↑(hC.map (l + 1) j) '' sphere 0 1), union_assoc]
      _ = (⋃ j, ↑(hC.map (l + 1) j) '' ball 0 1) ∪ level hC ↑l := by
        have : (⋃ (j : hC.cell (l + 1)), ↑(hC.map (l + 1) j) '' sphere 0 1) ∪ hC.level l = hC.level l := union_eq_right.2 (hC.aux2 l)
        rw [this]
  by_cases h : n = ⊤
  · rw [h]
    have : ⋃ (m : ℕ), ⋃ (_ : ↑m < (⊤ : ℕ∞)), ⋃ j, ↑(hC.map m j) '' ball 0 1 = ⋃ (n : ℕ) (hn : ↑n < (⊤ : ℕ∞)), ⋃ (m : ℕ) (hm : m < n + 1), ⋃ j, ↑(hC.map m j) '' ball 0 1 := by
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
          exact ⟨lt_trans (lt_add_one i) (lt_add_one (i + 1)), xmemi.2⟩
      · intro x xmem
        simp only [mem_iUnion, exists_prop] at xmem
        rcases xmem with ⟨_, ⟨_, ⟨i, ⟨_, xmemi⟩⟩⟩⟩
        simp only [mem_iUnion, exists_prop]
        use i
        exact ⟨(by apply lt_top_iff_ne_top.2 (WithTop.nat_ne_top i)), xmemi⟩
    rw [top_add, this, ← hC.iUnion_level_eq_level ⊤, top_add]
    apply iUnion_congr
    intro i
    rw [hnat]
  · push_neg at h
    let m := ENat.toNat n
    have coemn: ↑m = n := ENat.coe_toNat h
    rw [← coemn]
    norm_cast
    exact hnat m

lemma mapsto_sphere_level (n : ℕ) (j : hC.cell n) (nnezero : n ≠ 0) : MapsTo (hC.map n j) (sphere 0 1) (hC.level (Nat.pred n)) := by
  rcases hC.mapsto n j with ⟨I, hI⟩
  rw [Set.mapsTo'] at *
  apply subset_trans hI
  intro x xmem
  simp only [mem_iUnion, exists_prop] at xmem
  rcases xmem with ⟨i, ⟨iltn, ⟨j, ⟨jmemI, xmem⟩⟩⟩⟩
  simp only [CWComplex.level, mem_iUnion, exists_prop]
  use i
  norm_cast
  constructor
  · rw [Nat.add_one, Nat.succ_pred nnezero]
    exact iltn
  · use j

lemma exists_mem_ball_of_mem_level {n : ℕ∞} {x : X} (xmemlvl : x ∈ hC.level n) : ∃ (m : ℕ) (_ : m ≤ n) (j : hC.cell m), x ∈ ↑(hC.map m j) '' ball 0 1 := by
  induction' n using ENat.nat_induction with n hn hn
  · rw [CWComplex.level, mem_iUnion] at xmemlvl
    simp only [zero_add, Nat.cast_lt_one, mem_iUnion, exists_prop] at xmemlvl
    rcases xmemlvl with ⟨m, ⟨meqzero, h⟩⟩
    rw [meqzero] at h
    rcases h with ⟨j, xmem⟩
    use 0
    simp only [Nat.cast_zero, le_refl, exists_const]
    use j
    have : (closedBall 0 1 : Set (Fin 0 → ℝ)) = (ball 0 1 : Set (Fin 0 → ℝ)) := by
    -- I think there was a lemma stating this but I don't find it right now
      ext x
      simp [Matrix.empty_eq]
    rw [← this]
    exact xmem
  · simp only [Nat.cast_succ, level, mem_iUnion, exists_prop] at xmemlvl
    rcases xmemlvl with ⟨m, ⟨mlt, h⟩⟩
    by_cases h': m = 0
    · use 0
      simp only [Nat.cast_zero, Nat.cast_succ, zero_le, exists_const]
      rw [h'] at h
      rcases h with ⟨j, hj⟩
      use j
      have : (closedBall 0 1 : Set (Fin 0 → ℝ)) = (ball 0 1 : Set (Fin 0 → ℝ)) := by
        ext x
        simp [Matrix.empty_eq]
      rw [← this]
      exact hj
    push_neg at h'
    rcases h with ⟨j, xmem⟩
    rw [← Metric.sphere_union_ball, image_union] at xmem
    rcases xmem with h | h
    · have := hC.mapsto_sphere_level m j h'
      rw [Set.mapsTo'] at this
      apply this at h
      have :  (Nat.pred m : ℕ∞) ≤ (n : ℕ∞) := by
        norm_cast at *
        rw [← Nat.pred_succ n, ← Nat.add_one]
        apply Nat.pred_le_pred
        rw [Nat.lt_add_one_iff] at mlt
        exact mlt
      rcases hn ((hC.level_subset_level_of_le this) h) with ⟨m, hm⟩
      simp only [exists_prop] at hm
      use m
      simp only [exists_prop]
      norm_cast at *
      exact ⟨le_trans hm.1 (Nat.le_succ n), hm.2⟩
    · use m
      simp only [Nat.cast_succ, exists_prop]
      norm_cast at *
      rw [Nat.lt_add_one_iff] at mlt
      exact ⟨mlt, ⟨j, h⟩⟩
  · rw [← hC.iUnion_level_eq_level] at xmemlvl
    simp at xmemlvl
    rcases xmemlvl with ⟨i, ⟨_, xmemlvli⟩⟩
    rcases (hn i xmemlvli) with ⟨m, hm⟩
    simp only [exists_prop] at hm
    use m
    simp only [exists_prop]
    exact ⟨le_top, hm.2⟩

lemma level_inter_image_closedBall_eq_level_inter_image_sphere {n : ℕ∞} {m : ℕ}{j : hC.cell m} (nltm : n < m) : hC.level n ∩ ↑(hC.map m j) '' closedBall 0 1 = hC.level n ∩ ↑(hC.map m j) '' sphere 0 1 := by
  ext x
  constructor
  · intro ⟨xmemlevel, xmemball⟩
    constructor
    · exact xmemlevel
    rw [← Metric.sphere_union_ball, image_union] at xmemball
    rcases xmemball with h | h
    · exact h
    rcases hC.exists_mem_ball_of_mem_level xmemlevel with ⟨l, ⟨llen, ⟨i, xmem⟩⟩⟩
    have := hC.pairwiseDisjoint
    rw [PairwiseDisjoint, Set.Pairwise] at this
    simp only [mem_univ, ne_eq, forall_true_left] at this
    have h' : ¬  (⟨l, i⟩ : (Σ n, hC.cell n)) = (⟨m, j⟩ : (Σ n, hC.cell n)) := by
      simp only [Sigma.mk.inj_iff, not_and]
      have : ¬ l = m := by
        push_neg
        apply LT.lt.ne
        let k := ENat.toNat n
        have coekn: ↑k = n := ENat.coe_toNat (LT.lt.ne_top nltm)
        rw [← coekn] at nltm
        rw [← coekn] at llen
        norm_cast at *
        exact lt_of_le_of_lt llen nltm
      simp [this]
    have := this h'
    simp [Function.onFun, Disjoint] at this
    have h1 : {x} ⊆ ↑(hC.map l i) '' ball 0 1 := by
      simp only [singleton_subset_iff]
      exact xmem
    have h2 : {x} ⊆ ↑(hC.map m j) '' ball 0 1 := by
      simp only [singleton_subset_iff]
      exact h
    have := this h1 h2
    simp at this
  · intro xmem
    exact ⟨xmem.1,  (Set.image_subset ↑(hC.map m j) Metric.sphere_subset_closedBall) xmem.2⟩

lemma isClosed_map_sphere {n : ℕ} {i : hC.cell n} : IsClosed (hC.map n i '' sphere 0 1) := by
  apply IsCompact.isClosed
  apply IsCompact.image_of_continuousOn
  apply isCompact_sphere
  exact ContinuousOn.mono (hC.cont n i) sphere_subset_closedBall

lemma isClosed_inter_sphere_succ_of_le_isClosed_inter_closedBall {A : Set X} {n : ℕ} (hn : ∀ m ≤ n, ∀ (j : hC.cell m), IsClosed (A ∩ ↑(hC.map m j) '' closedBall 0 1)) : ∀ (j : hC.cell (n + 1)), IsClosed (A ∩ ↑(hC.map (n + 1) j) '' sphere 0 1) := by
  intro j
  rcases hC.mapsto (n + 1) j with ⟨I, hI⟩
  rw [mapsTo'] at hI
  have closedunion : IsClosed (A ∩ ⋃ m, ⋃ (_ : m < n + 1), ⋃ j ∈ I m, ↑(hC.map m j) '' closedBall 0 1) := by
    simp [inter_iUnion]
    let N := {m : ℕ // m < n + 1}
    have : ⋃ i, ⋃ (_ : i < n + 1), ⋃ i_1 ∈ I i, A ∩ ↑(hC.map i i_1) '' closedBall 0 1 = ⋃ (i : N), ⋃ (i_1 : I i), A ∩ ↑(hC.map i i_1) '' closedBall 0 1 := by
      ext x
      simp only [mem_iUnion, exists_prop]
      constructor
      · intro h
        rcases h with ⟨i, ⟨ilt, ⟨j, ⟨jmem, h⟩⟩⟩⟩
        use ⟨i, ilt⟩
        use ⟨j, jmem⟩
      · intro h
        rcases h with ⟨⟨i, ilt⟩, ⟨⟨j, jmem⟩, h⟩⟩
        use i
        exact ⟨ilt, (by use j)⟩
    rw [this]
    apply isClosed_iUnion_of_finite
    intro i
    apply isClosed_iUnion_of_finite
    intro j
    exact hn i (Nat.le_of_lt_succ i.2) j
  have : A ∩ ↑(hC.map (n + 1) j) '' sphere 0 1 = A ∩ (⋃ m, ⋃ (_ : m < n + 1), ⋃ j ∈ I m, ↑(hC.map m j) '' closedBall 0 1) ∩ ↑(hC.map (n + 1) j) '' sphere 0 1 := by
    rw [inter_assoc, Set.inter_eq_right.2 hI]
  rw [this]
  apply IsClosed.inter closedunion hC.isClosed_map_sphere


def CWComplex_level (n : ℕ∞) : CWComplex (hC.level n) where
  cell l := {x : hC.cell l // l < n + 1}
  map l i := hC.map l i
  source_eq l i := by rw [hC.source_eq]
  cont l i := hC.cont l i
  cont_symm l i := hC.cont_symm l i
  -- Why doesn't ← Set.image_eta work?
  pairwiseDisjoint := by
    rw [PairwiseDisjoint, Set.Pairwise]
    simp only [mem_univ, ne_eq, forall_true_left, Sigma.forall, Subtype.forall]
    intro a ja alt b jb blt
    have := hC.pairwiseDisjoint
    rw [PairwiseDisjoint, Set.Pairwise] at this
    simp only [mem_univ, ne_eq, forall_true_left, Sigma.forall, Subtype.forall] at this
    have := this a ja b jb
    intro h
    simp only [Sigma.mk.inj_iff, not_and] at *
    apply this
    by_cases h' : a = b
    · simp [h']
      by_contra h''
      apply h h'
      rw [Subtype.heq_iff_coe_heq (type_eq_of_heq h'')]
      simp [h'']
      rw [h']
    · simp only [h', IsEmpty.forall_iff]
  mapsto l i := by
    rcases hC.mapsto l i with ⟨I, hI⟩
    rcases i with ⟨i, llt⟩
    let J := fun (m : ℕ) ↦ (I m).subtype (fun j ↦ m < n + 1)
    use J
    simp only [mapsTo'] at *
    apply subset_trans hI
    apply Set.iUnion_mono''
    intro i x xmem
    simp only [mem_iUnion, exists_prop] at *
    constructor
    · exact xmem.1
    rcases xmem with ⟨iltl, ⟨j, ⟨jmemIi, xmem⟩⟩⟩
    have : (i : ℕ∞) < (l : ℕ∞) := by norm_cast
    use ⟨j, lt_trans this llt⟩
    exact ⟨(by simp only [Finset.mem_subtype, jmemIi, J]) , xmem⟩
  closed A := by
    intro asublevel
    have : A ⊆ C := by
      apply subset_trans
      exact asublevel
      simp_rw [← hC.level_top]
      apply hC.level_subset_level_of_le le_top
    have := hC.closed A this
    constructor
    · intro closedA l j
      simp [this.1]
    · intro h
      simp at h
      rw [this]
      intro m
      induction' m using Nat.case_strong_induction_on with m hm
      · have : 0 < n + 1 := by simp only [add_pos_iff, zero_lt_one, or_true]
        intro j
        exact h Nat.zero j this
      rw [← Nat.add_one] at *
      intro j
      let k := ENat.toNat n
      by_cases mlt : m + 1 < n + 1
      · exact h (m + 1) j mlt
      push_neg at mlt
      have nltm : n ≤ Nat.succ m := le_trans (le_add_right le_rfl) mlt
      have coekn: ↑k = n := ENat.coe_toNat (ne_top_of_le_ne_top (WithTop.nat_ne_top (Nat.succ m)) nltm)
      rw [← coekn] at asublevel -- why does at * not work?
      rw [← coekn] at mlt
      norm_cast at *
      have : A ∩ ↑(hC.map (m + 1) j) '' closedBall 0 1 = A ∩ ↑(hC.map (m + 1) j) '' sphere 0 1 := by
        calc
          A ∩ ↑(hC.map (m + 1) j) '' closedBall 0 1 = A ∩ (hC.level k ∩ ↑(hC.map (m + 1) j) '' closedBall 0 1) := by rw [← inter_assoc, Set.inter_eq_left.2 asublevel]
          _ = A ∩ (hC.level k ∩ ↑(hC.map (m + 1) j) '' sphere 0 1) := by
            have : (m + 1 : ℕ∞) > (k : ℕ∞) := by norm_cast
            have : hC.level k ∩ ↑(hC.map (m + 1) j) '' closedBall 0 1 = hC.level k ∩ ↑(hC.map (m + 1) j) '' sphere 0 1 := by
              apply hC.level_inter_image_closedBall_eq_level_inter_image_sphere this
            rw [this]
          _ = A ∩ ↑(hC.map (m + 1) j) '' sphere 0 1 := by rw [← inter_assoc, Set.inter_eq_left.2 asublevel]
      rw [this]
      exact hC.isClosed_inter_sphere_succ_of_le_isClosed_inter_closedBall hm j
  union := by
    rw [CWComplex.level]
    apply Set.iUnion_congr
    intro m
    ext x
    constructor
    · intro h
      rw [mem_iUnion] at *
      rcases h with ⟨⟨i, mlt⟩, hi⟩
      use mlt
      rw [mem_iUnion]
      use i
    · intro h
      rw [mem_iUnion, exists_prop] at *
      rw [mem_iUnion] at h
      rcases h with ⟨mlt, ⟨i, hi⟩⟩
      use ⟨i, mlt⟩

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
  rfl

lemma level_succ_eq_level_union_iUnion (n : ℕ) : hC.level (↑n + 1) = hC.level ↑n ∪ ⋃ (j : hC.cell (↑n + 1)), hC.map (↑n + 1) j '' closedBall 0 1 := by
  simp [CWComplex.level]
  norm_cast
  rw [Nat.add_one, union_comm]
  exact CWComplex.aux1 hC (n + 1) (fun m j ↦ ↑(hC.map m j) '' closedBall 0 1)

/- The following lemmas are already hard! -/

/- The levels are closed. The following might be helpful:
https://math.stackexchange.com/questions/4051497/subcomplex-is-closed -/
lemma isClosed_level (n : ℕ∞) : IsClosed (hC.level n) := (hC.CWComplex_level n).isClosed
-- kept my original beginning of the proof in case CWComplex_level doesn't work out:
/-
  by_cases h : n = ⊤
  · rw [h]
    rw [level_top]
    exact hC.isClosed
  push_neg at h
  let m := ENat.toNat n
  have coemn: ↑m = n := ENat.coe_toNat h
  rw [← coemn]
  induction' m with m hm
  · rw [← Set.inter_self (level hC ↑Nat.zero)]
    exact hC.isDiscrete_level_zero
  · rw [← Nat.add_one, ENat.coe_add, ENat.coe_one, hC.level_succ_eq_level_union_iUnion m]
    sorry
    /- Next step of the proof: Define disjoint map (how?) show that it is a quotient map (QuotientMap). Then our set is closed since the preimage is also closed by induction -/
-/

lemma map_closedBall_subset_level (n : ℕ) (j : hC.cell n) : (hC.map n j) '' closedBall 0 1 ⊆ hC.level n := by
  rw [CWComplex.level]
  intro x xmem
  simp only [mem_iUnion, exists_prop]
  use n
  norm_cast
  exact ⟨lt_add_one n, ⟨j,xmem⟩⟩

/- The following is one way of stating that `level 0` is discrete. -/
lemma isDiscrete_level_zero {A : Set X} : IsClosed (A ∩ hC.level 0) := by
  rw [hC.closed (A ∩ hC.level 0) (subset_trans (Set.inter_subset_right A (hC.level 0)) (by simp_rw [← hC.level_top]; apply hC.level_subset_level_of_le le_top))]
  intro n
  induction' n using Nat.case_strong_induction_on with n hn
  · intro j
    have := Set.inter_eq_right.2 (hC.map_closedBall_subset_level 0 j)
    norm_cast at this
    rw [inter_assoc, this]
    have : ↑(hC.map 0 j) '' closedBall 0 1 = {(hC.map 0 j) ![]} := by
      ext x
      constructor
      · intro h
        rw [mem_image] at h
        rcases h with ⟨y, ymem, mapy⟩
        have : y = ![] := by simp [Matrix.empty_eq]
        rw [this] at mapy
        simp only [mapy, mem_singleton_iff]
      · intro h
        rw [h]
        apply Set.mem_image_of_mem
        simp only [Matrix.zero_empty, mem_closedBall, dist_self, zero_le_one]
    rw [this]
    by_cases h : {(hC.map 0 j) ![]} ⊆ A
    · rw [inter_eq_right.2 h]
      exact isClosed_singleton
    · simp at h
      have : A ∩ {(hC.map 0 j) ![]} = ∅ := by
        simp only [inter_singleton_eq_empty, h, not_false_eq_true]
      rw [this]
      exact isClosed_empty
  · rw [← Nat.add_one]
    intro j
    rw [inter_assoc, hC.level_inter_image_closedBall_eq_level_inter_image_sphere (by norm_cast; exact Nat.zero_lt_succ n), ← inter_assoc]
    exact hC.isClosed_inter_sphere_succ_of_le_isClosed_inter_closedBall hn j



/- State some more properties: e.g.
* `C` is closed
* the disjoint union of two CW-complexes (in the same space `X`) is a CW-complex
  (maybe you need to require that the subspaces are separated by neighborhoods)
-/

/- Define subcomplexes and quotients -/

/- Prove some of the results in Hatcher, appendix A. -/
