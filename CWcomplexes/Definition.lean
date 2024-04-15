import CWcomplexes.auxiliary

/- Questions:
  - I don't think the imports should be this way but I don't know what to import in aux.lean to make it work

-/

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

/-- The `n`-th level of a CW-complex, for `n ∈ ℕ ∪ ∞`. -/
/- Would it be possible to add a -1 to make induction proofs easier? -/
def level (n : ℕ∞) : Set X :=
  ⋃ (m : ℕ) (hm : m < n + 1) (j : hC.cell m), hC.map m j '' closedBall 0 1 -- I changed this from m < n to m < n + 1

@[simp] lemma level_top : hC.level ⊤ = C := by
  simp only [level, top_add, lt_top_iff_ne_top, ne_eq, ENat.coe_ne_top, not_false_eq_true, iUnion_true, ← hC.union]

lemma iUnion_map_sphere_subset_level (l : ℕ) : ⋃ (j : hC.cell (l + 1)), ↑(hC.map (l + 1) j) '' sphere 0 1 ⊆ hC.level l := by
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
    rw [aux1 (Nat.succ l) (fun m j ↦ ↑(hC.map m j) '' ball 0 1)]
    rw [hl]
    nth_rewrite 2 [CWComplex.level]
    norm_cast
    symm
    calc
      ⋃ m, ⋃ (_ : m < Nat.succ l + 1), ⋃ j, ↑(hC.map m j) '' closedBall 0 1
      = (⋃ (j : hC.cell (l + 1)), ↑(hC.map (l + 1) j) '' closedBall 0 1) ∪ ⋃ m, ⋃ (_ : Nat.cast m < ↑l + 1), ⋃ j, ↑(hC.map m j) '' closedBall 0 1 := by
        apply aux1 (l + 1) (fun m j ↦ ↑(hC.map m j) '' closedBall 0 1)
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
        have : (⋃ (j : hC.cell (l + 1)), ↑(hC.map (l + 1) j) '' sphere 0 1) ∪ hC.level l = hC.level l := union_eq_right.2 (hC.iUnion_map_sphere_subset_level l)
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
  exact aux1 (n + 1) (fun m j ↦ ↑(hC.map m j) '' closedBall 0 1)

/- The following lemmas are already hard! -/

lemma map_closedBall_subset_level (n : ℕ) (j : hC.cell n) : (hC.map n j) '' closedBall 0 1 ⊆ hC.level n := by
  rw [CWComplex.level]
  intro x xmem
  simp only [mem_iUnion, exists_prop]
  use n
  norm_cast
  exact ⟨lt_add_one n, ⟨j,xmem⟩⟩

lemma map_ball_subset_level (n : ℕ) (j : hC.cell n) : (hC.map n j) '' ball 0 1 ⊆ hC.level n := subset_trans (image_mono Metric.ball_subset_closedBall) (hC.map_closedBall_subset_level n j)

lemma map_ball_subset_complex (n : ℕ) (j : hC.cell n) : (hC.map n j) '' ball 0 1 ⊆ C := by
  apply subset_trans (hC.map_ball_subset_level n j) (by simp_rw [← hC.level_top]; apply hC.level_subset_level_of_le le_top)


/- State some more properties: e.g.
* `C` is closed -- done
* the disjoint union of two CW-complexes (in the same space `X`) is a CW-complex
  (maybe you need to require that the subspaces are separated by neighborhoods)
-/

/- Define subcomplexes, quotients and products -/

/- Prove some of the results in Hatcher, appendix A. -/
