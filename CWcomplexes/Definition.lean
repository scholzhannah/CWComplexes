import CWcomplexes.auxiliary
import Mathlib.Analysis.NormedSpace.Real

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open Metric Set

variable {X : Type*} [t : TopologicalSpace X]

--think about making this a class and converting stuff into instances
--examples spheres

/- Characterizing when a set is a CW-complex. See [Hatcher, Proposition A.2].
Generally we will need `[T2Space X]`.
Note that we are changing the definition a little bit: we are saying that a subspace `C` of `X` is a
`CW-complex`. -/
class CWComplex.{u} {X : Type u} [TopologicalSpace X] (C : Set X) where
  cell (n : ℕ) : Type u -- can I put Type*?
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
  -- create lemma with C explicit
  closed (A : Set X) (asubc : A ⊆ C) : IsClosed A ↔ ∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)
  union : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C

--create constructor if the CWComplex is finite

variable [T2Space X] (C : Set X) [CWComplex C]



namespace CWComplex

/-- A non-standard definition of the levels useful for induction.
  The typical level is defined in terms of levelaux.-/
def levelaux (n : ℕ∞) : Set X :=
  ⋃ (m : ℕ) (hm : m < n) (j : cell C m), map m j '' closedBall 0 1

/-- The `n`-th level of a CW-complex, for `n ∈ ℕ ∪ ∞`. -/
def level (n : ℕ∞) : Set X :=
  levelaux C (n + 1)

lemma levelaux_zero_eq_empty : levelaux C 0 = ∅ := by
  unfold levelaux
  simp only [isEmpty_Prop, not_lt, zero_le, iUnion_of_empty, iUnion_empty]

-- finite type seperately

class Finite.{u} {X : Type u} [TopologicalSpace X] (C : Set X) [cwcomplex : CWComplex C] : Prop where
  finitelevels : ∀ᶠ n in Filter.atTop, IsEmpty (cwcomplex.cell n)
  finitecells (n : ℕ) : Finite (cwcomplex.cell n)

@[simp] lemma levelaux_top : levelaux C ⊤ = C := by
  simp only [levelaux, lt_top_iff_ne_top, ne_eq, ENat.coe_ne_top, not_false_eq_true, iUnion_true, ←
    union]

@[simp] lemma level_top : level C ⊤ = C := by
  simp only [level, top_add, levelaux_top]

lemma levelaux_mono {n m : ℕ∞} (h : m ≤ n) : levelaux C m ⊆ levelaux C n := by
  repeat rw [levelaux]
  intro x xmem
  rw [mem_iUnion] at xmem
  rcases xmem with ⟨l , xmeml⟩
  simp only [mem_iUnion, exists_prop] at xmeml
  rw [mem_iUnion]
  use l
  simp only [mem_iUnion, exists_prop]
  constructor
  · exact lt_of_lt_of_le xmeml.1 h
  · exact xmeml.2

lemma level_mono {n m : ℕ∞} (h : m ≤ n) : level C m ⊆ level C n := by
  simp only [level, levelaux_mono _ (add_le_add_right h 1)]

lemma map_closedBall_subset_levelaux (n : ℕ) (j : cell C n) :
    map n j '' closedBall 0 1 ⊆ levelaux C (n + 1) := by
  rw [levelaux]
  intro x xmem
  simp only [mem_iUnion, exists_prop]
  use n
  norm_cast
  exact ⟨lt_add_one n, ⟨j,xmem⟩⟩

lemma map_closedBall_subset_level (n : ℕ) (j : cell C n) :
    map n j '' closedBall 0 1 ⊆ level C n := by
  rw [level]
  exact map_closedBall_subset_levelaux _ n j

lemma map_closedBall_subset_complex (n : ℕ) (j : cell C n) : map n j '' closedBall 0 1 ⊆ C := by
  apply subset_trans (map_closedBall_subset_level _ n j)
    (by simp_rw [← level_top]; apply level_mono _ le_top)

lemma map_ball_subset_levelaux (n : ℕ) (j : cell C n) : map n j '' ball 0 1 ⊆ levelaux C (n + 1) :=
  subset_trans (image_mono Metric.ball_subset_closedBall) (map_closedBall_subset_levelaux _ n j)

lemma map_ball_subset_level (n : ℕ) (j : cell C n) : map n j '' ball 0 1 ⊆ level C n :=
  subset_trans (image_mono Metric.ball_subset_closedBall) (map_closedBall_subset_level _ n j)

lemma map_ball_subset_complex (n : ℕ) (j : cell C n) : map n j '' ball 0 1 ⊆ C := by
  apply subset_trans (map_ball_subset_level _ n j)
    (by simp_rw [← level_top]; exact level_mono _ le_top)

lemma map_ball_subset_map_closedball {n : ℕ} {j : cell C n} :
  map n j '' ball 0 1 ⊆ map n j '' closedBall 0 1 := image_mono ball_subset_closedBall

lemma map_sphere_subset_levelaux (n : ℕ) (j : cell C n) :
    map n j '' sphere 0 1 ⊆  levelaux C n := by
  rcases mapsto n j with ⟨I, hI⟩
  rw [Set.mapsTo'] at hI
  apply subset_trans hI
  intro x xmem
  simp only [mem_iUnion, exists_prop] at xmem
  rcases xmem with ⟨i, ⟨iltn, ⟨j, ⟨jmemI, xmem⟩⟩⟩⟩
  simp only [CWComplex.levelaux, mem_iUnion, exists_prop]
  use i
  norm_cast
  exact ⟨iltn, ⟨j, xmem⟩⟩

lemma map_sphere_subset_level (n : ℕ) (j : cell C (n + 1)) :
    map (n + 1) j '' sphere 0 1 ⊆ level C n := map_sphere_subset_levelaux C _ _

lemma iUnion_map_sphere_subset_levelaux (l : ℕ) :
    ⋃ (j : cell C l), map l j '' sphere 0 1 ⊆ levelaux C l := by
  rw [CWComplex.levelaux]
  norm_cast
  intro x xmem
  rw [mem_iUnion] at xmem
  rcases xmem with ⟨e, xmeme⟩
  rcases mapsto l e with ⟨I, hI⟩
  apply MapsTo.image_subset at hI
  apply hI at xmeme
  suffices ⋃ m, ⋃ (_ : m < l), ⋃ j ∈ I m, map m j '' closedBall 0 1 ⊆
      ⋃ m, ⋃ (_ : m < l), ⋃ j, map (C := C) m j '' closedBall 0 1 from this xmeme
  apply iUnion_mono
  simp only [iUnion_subset_iff]
  intro i iltl e ememIi y ymem
  simp only [mem_iUnion, exists_prop]
  exact ⟨iltl, ⟨e, ymem⟩⟩

lemma iUnion_map_sphere_subset_level (l : ℕ) :
    ⋃ (j : cell C l), map l j '' sphere 0 1 ⊆ level C l := by
  unfold level
  exact subset_trans (iUnion_map_sphere_subset_levelaux C l)
    (levelaux_mono C le_self_add)

lemma iUnion_levelaux_eq_levelaux (n : ℕ∞) :
    ⋃ (m : ℕ) (hm : m < n + 1), levelaux C m = levelaux C n := by
  apply subset_antisymm
  · simp_rw [iUnion_subset_iff]
    intros i hi
    exact levelaux_mono _ (ENat.le_of_lt_add_one hi)
  · intro x xmem
    rw [mem_iUnion]
    by_cases h : n = ⊤
    · rw [h, top_add]
      rw [h, CWComplex.levelaux, mem_iUnion] at xmem
      rcases xmem with ⟨i, xmemi⟩
      simp only [mem_iUnion, exists_prop] at xmemi
      use i + 1
      simp only [Nat.cast_add, Nat.cast_one, mem_iUnion, exists_prop]
      refine ⟨by rw [← ENat.coe_one, ← ENat.coe_add]; exact ENat.coe_lt_top, ?_⟩
      rw [CWComplex.levelaux, mem_iUnion]
      use i
      simp only [mem_iUnion, exists_prop]
      norm_cast
      exact ⟨lt_add_one i, xmemi.2⟩
    · push_neg at h
      let m := ENat.toNat n
      have coemn: ↑m = n := ENat.coe_toNat h
      rw [← coemn]
      use m
      simp only [mem_iUnion, exists_prop]
      norm_cast
      rw [coemn]
      exact ⟨lt_add_one m, xmem⟩

lemma iUnion_level_eq_level (n : ℕ∞) : ⋃ (m : ℕ) (hm : m < n + 1), level C m = level C n := by
  simp_rw [level, ← iUnion_levelaux_eq_levelaux C (n + 1)]
  ext; simp
  constructor
  · intro ⟨i, hin, hiC⟩
    refine ⟨i + 1, ?_, hiC⟩
    push_cast
    exact ENat.add_coe_lt_add_coe_right.mpr hin
  · intro ⟨i, hin, hiC⟩
    cases' i with i
    · refine ⟨0, ?_, levelaux_mono C (by norm_num) hiC⟩
      norm_cast
      exact ENat.add_one_pos
    · refine ⟨i, ?_, hiC⟩
      push_cast
      exact ENat.add_coe_lt_add_coe_right.mp hin

lemma levelaux_succ_eq_levelaux_union_iUnion (n : ℕ) :
    levelaux C (n + 1) = levelaux C n ∪ ⋃ (j : cell C n), map n j '' closedBall 0 1 := by
  simp_rw [levelaux, Nat.cast_lt]
  norm_cast
  rw [Nat.add_one, union_comm]
  exact aux1 n (fun m j ↦ map m j '' closedBall 0 1)

lemma level_succ_eq_level_union_iUnion (n : ℕ) :
    level C (n + 1) = level C n ∪ ⋃ (j : cell C (↑n + 1)), map (↑n + 1) j '' closedBall 0 1 :=
  levelaux_succ_eq_levelaux_union_iUnion _ (n + 1)

/- We can also define the levels using `ball` instead of `closedBall`, using assumption `mapsto`. -/
lemma iUnion_ball_eq_levelaux (n : ℕ∞) :
    ⋃ (m : ℕ) (hm : m < n) (j : cell C m), map m j '' ball 0 1 = levelaux C n := by
  induction' n using ENat.nat_induction with n hn hn
  · simp [levelaux]
  · norm_cast at hn ⊢
    rw [aux1 n (fun m j ↦ map m j '' ball 0 1), hn]
    nth_rewrite 2 [levelaux]
    symm
    norm_cast
    calc
      ⋃ m, ⋃ (_ : m < Nat.succ n), ⋃ j, map m j '' closedBall 0 1
      = (⋃ (j : cell C n), map n j '' closedBall 0 1) ∪
          ⋃ m, ⋃ (_ : Nat.cast m < ↑n), ⋃ j, map m j '' closedBall 0 1 := by
        apply aux1 n (fun m j ↦ map m j '' closedBall 0 1)
      _ = (⋃ (j : cell C n), map n j '' closedBall 0 1) ∪ levelaux C n := by
        rw [levelaux]
        norm_cast
      _ = (⋃ (j : cell C n), map n j '' (sphere 0 1 ∪ ball 0 1)) ∪ levelaux C n := by
        rw [sphere_union_ball]
      _ = (⋃ (j : cell C n), map n j '' sphere 0 1 ∪ map n j '' ball 0 1) ∪ levelaux C n := by
        congr
        apply iUnion_congr
        intro i
        rw [image_union]
      _ = (⋃ (j : cell C n), map n j '' sphere 0 1) ∪
          (⋃ (j : cell C n), map n j '' ball 0 1) ∪ levelaux C n := by
        rw [iUnion_union_distrib]
      _ = (⋃ (j : cell C n), map n j '' ball 0 1) ∪
          ((⋃ (j : cell C n), map n j '' sphere 0 1) ∪ levelaux C n) := by
        rw [← union_assoc, union_comm (⋃ j, map n j '' sphere 0 1), union_assoc]
      _ = (⋃ j, map n j '' ball 0 1) ∪ levelaux C n := by
        congr
        exact union_eq_right.2 (iUnion_map_sphere_subset_levelaux _ n)
  · have : ⋃ (m : ℕ), ⋃ (_ : ↑m < (⊤ : ℕ∞)), ⋃ (j : cell C m), map m j '' ball 0 1 =
        ⋃ (n : ℕ) (hn : ↑n < (⊤ : ℕ∞)), ⋃ (m : ℕ) (hm : m < n), ⋃ (j : cell C m), map m j '' ball 0 1 := by -- TODO : extract and generalize this in some way
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
          exact ⟨xmemi.1 , (by apply lt_top_iff_ne_top.2 (WithTop.natCast_ne_top 1))⟩
        · use i
          exact ⟨lt_add_one i, xmemi.2⟩
      · intro x xmem
        simp only [mem_iUnion, exists_prop] at xmem
        rcases xmem with ⟨_, ⟨_, ⟨i, ⟨_, xmemi⟩⟩⟩⟩
        simp only [mem_iUnion, exists_prop]
        use i
        exact ⟨(by apply lt_top_iff_ne_top.2 (WithTop.natCast_ne_top i)), xmemi⟩
    rw [this, ← iUnion_levelaux_eq_levelaux _ ⊤, top_add]
    apply iUnion_congr
    intro i
    norm_cast at hn
    rw [hn]

lemma union' : ⋃ (n : ℕ) (j : cell C n), map n j '' ball 0 1 = C := by
  simp only [← levelaux_top, ← iUnion_ball_eq_levelaux, ENat.coe_lt_top, iUnion_true]

lemma not_disjoint_equal {n : ℕ} {j : cell C n} {m : ℕ} {i : cell C m}
    (notdisjoint: ¬ Disjoint (map n j '' ball 0 1) (map m i '' ball 0 1)) :
    (⟨n, j⟩ : (Σ n, cell C n)) = ⟨m, i⟩ := by
  by_contra h'
  push_neg at h'
  apply notdisjoint
  have := pairwiseDisjoint (C := C)
  simp only [PairwiseDisjoint, Set.Pairwise, Function.onFun] at this
  exact this (x := ⟨n, j⟩) (by simp) (y := ⟨m, i⟩) (by simp) h'

lemma iUnion_ball_eq_level (n : ℕ∞) :
    ⋃ (m : ℕ) (hm : m < n + 1) (j : cell C m), map m j '' ball 0 1 = level C n := by
  rw [level]
  exact iUnion_ball_eq_levelaux _ (n + 1)

lemma exists_mem_ball_of_mem_levelaux {n : ℕ∞} {x : X} (xmemlvl : x ∈ levelaux C n) :
    ∃ (m : ℕ) (_ : m < n) (j : cell C m), x ∈ map m j '' ball 0 1 := by
  induction' n using ENat.nat_induction with n hn hn
  · simp [levelaux] at xmemlvl
  · simp only [Nat.cast_succ, levelaux, mem_iUnion, exists_prop] at xmemlvl
    rcases xmemlvl with ⟨m, ⟨mlt, h⟩⟩
    rcases h with ⟨j, xmem⟩
    rw [← Metric.sphere_union_ball, image_union] at xmem
    rcases xmem with h | h
    · apply (map_sphere_subset_levelaux _ m j) at h
      norm_cast at hn mlt ⊢
      rw [Nat.add_one] at mlt
      rcases hn ((levelaux_mono _ (by norm_cast; exact (Nat.le_of_lt_succ mlt))) h) with ⟨m, hm⟩
      simp only [exists_prop] at hm
      use m
      simp only [exists_prop]
      exact ⟨lt_of_lt_of_le hm.1 (Nat.le_succ n), hm.2⟩
    · use m
      simp only [Nat.cast_succ, exists_prop]
      exact ⟨mlt, ⟨j, h⟩⟩
  · rw [← iUnion_levelaux_eq_levelaux] at xmemlvl
    simp at xmemlvl
    rcases xmemlvl with ⟨i, ⟨ilttop, xmemlvli⟩⟩
    rcases (hn i xmemlvli) with ⟨m, hm⟩
    simp only [exists_prop] at hm
    use m
    simp only [exists_prop]
    exact ⟨lt_trans hm.1 ilttop, hm.2⟩

lemma exists_mem_ball_of_mem_level {n : ℕ∞} {x : X} (xmemlvl : x ∈ level C n) :
    ∃ (m : ℕ) (_ : m ≤ n) (j : cell C m), x ∈ map m j '' ball 0 1 := by
  rw [level] at xmemlvl
  rcases exists_mem_ball_of_mem_levelaux _ xmemlvl with ⟨m, hm⟩
  use m
  rw [exists_prop] at *
  exact ⟨ENat.le_of_lt_add_one hm.1, hm.2⟩

lemma levelaux_inter_image_closedBall_eq_levelaux_inter_image_sphere {n : ℕ∞} {m : ℕ}
    {j : cell C m} (nlem : n ≤ m) : levelaux C n ∩ map m j '' closedBall 0 1 =
    levelaux C n ∩ map m j '' sphere 0 1 := by
  ext x
  constructor
  · intro ⟨xmemlevel, xmemball⟩
    refine ⟨xmemlevel, ?_ ⟩
    rw [← Metric.sphere_union_ball, image_union] at xmemball
    rcases xmemball with h | h
    · exact h
    exfalso
    rcases exists_mem_ball_of_mem_levelaux _ xmemlevel with ⟨l, ⟨llen, ⟨i, xmem⟩⟩⟩
    have : ¬ Disjoint (map m j '' ball 0 1) (map l i '' ball 0 1) := by
      rw [not_disjoint_iff]
      use x
    have := not_disjoint_equal _ this
    simp only [Sigma.mk.inj_iff] at this
    rcases this with ⟨eq1, eq2⟩
    subst m
    exact (lt_self_iff_false n).1 (lt_of_le_of_lt nlem llen)
  · intro xmem
    exact ⟨xmem.1,  (Set.image_subset (map m j) Metric.sphere_subset_closedBall) xmem.2⟩

lemma level_inter_image_closedBall_eq_level_inter_image_sphere {n : ℕ∞} {m : ℕ}{j : cell C m}
    (nltm : n < m) : level C n ∩ map m j '' closedBall 0 1 =
    level C n ∩ map m j '' sphere 0 1 := by
  apply Order.succ_le_of_lt at nltm
  rw [ENat.succ_def] at nltm
  simp only [level]
  exact levelaux_inter_image_closedBall_eq_levelaux_inter_image_sphere _ nltm

lemma isClosed_map_sphere {n : ℕ} {i : cell C n} : IsClosed (map n i '' sphere 0 1) :=
  IsCompact.isClosed (IsCompact.image_of_continuousOn (isCompact_sphere _ _)
    (ContinuousOn.mono (cont n i) sphere_subset_closedBall))

lemma isClosed_inter_sphere_succ_of_le_isClosed_inter_closedBall {A : Set X} {n : ℕ}
  (hn : ∀ m ≤ n, ∀ (j : cell C m), IsClosed (A ∩ map m j '' closedBall 0 1)) :
  ∀ (j : cell C (n + 1)), IsClosed (A ∩ map (n + 1) j '' sphere 0 1) := by
  intro j
  rcases mapsto (n + 1) j with ⟨I, hI⟩
  rw [mapsTo'] at hI
  have closedunion : IsClosed (A ∩ ⋃ m, ⋃ (_ : m < n + 1), ⋃ j ∈ I m, map m j '' closedBall 0 1) := by
    simp only [inter_iUnion]
    let N := {m : ℕ // m < n + 1}
    suffices IsClosed (⋃ (i : N), ⋃ (i_1 : I i), A ∩ map (C := C) i i_1 '' closedBall 0 1) by
      convert this using 1
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
    apply isClosed_iUnion_of_finite
    intro i
    apply isClosed_iUnion_of_finite
    intro j
    exact hn i (Nat.le_of_lt_succ i.2) j
  suffices IsClosed (A ∩ (⋃ m, ⋃ (_ : m < n + 1),
      ⋃ j ∈ I m, map m j '' closedBall 0 1) ∩ map (n + 1) j '' sphere 0 1) by
    simpa [inter_assoc, Set.inter_eq_right.2 hI]
  apply IsClosed.inter closedunion (isClosed_map_sphere _)

lemma isCompact_map_closedBall (n : ℕ) (i : cell C n) : IsCompact (map n i '' closedBall 0 1) :=
  IsCompact.image_of_continuousOn (isCompact_closedBall _ _) (cont n i)

lemma isClosed_map_closedBall (n : ℕ) (i : cell C n) : IsClosed (map n i '' closedBall 0 1) :=
  IsCompact.isClosed (isCompact_map_closedBall _ _ _)

lemma isClosed : IsClosed C := by
  rw [closed (C := C) _ (by rfl)]
  intros
  rw [Set.inter_eq_right.2 (map_closedBall_subset_complex _ _ _)]
  exact isClosed_map_closedBall _ _ _

lemma closure_map_ball_eq_map_closedball {n : ℕ} {j : cell C n} :
    closure (map n j '' ball 0 1) = map n j '' closedBall 0 1 := by
  apply subset_antisymm
  · rw [IsClosed.closure_subset_iff (isClosed_map_closedBall _ n j)]
    exact map_ball_subset_map_closedball C
  · have : ContinuousOn (map n j) (closure (ball 0 1)) := by
      rw [closure_ball 0 (by exact one_ne_zero)]
      exact cont n j
    rw [← closure_ball]
    apply ContinuousOn.image_closure this
    exact one_ne_zero

-- could this proof be simplified using `exists_mem_ball_of_mem_level`?
lemma mapsto' (n : ℕ) (i : cell C n) : ∃ I : Π m, Finset (cell C m),
MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j ∈ I m), map m j '' ball 0 1) := by
  induction' n using Nat.case_strong_induction_on with n hn
  · simp [sphere_zero_dim_empty, MapsTo]
  · rcases mapsto (Nat.succ n) i with ⟨J, hJ⟩
    choose p hp using hn
    let I' m := if mltnsucc : m < Nat.succ n then
      (J m).toSet ∪ ⋃ (l : {l : ℕ // l ≤ n}) (y : J l), p l l.2 y m else (J m).toSet
    have : ∀ m, Set.Finite (I' m) := by
      intro m
      simp only [Nat.succ_eq_add_one, dite_eq_ite, I']
      by_cases h : m < Nat.succ n
      · simp only [h, ↓reduceIte, finite_union, Finset.finite_toSet, true_and]
        apply Set.finite_iUnion
        intro ⟨l, llen⟩
        apply Set.finite_iUnion
        intro ⟨x, xmem⟩
        simp only [Finset.finite_toSet]
      · simp only [h, ↓reduceIte, Finset.finite_toSet]
    let I m := Set.Finite.toFinset (this m)
    use I
    rw [MapsTo] at hJ ⊢
    intro x xmem
    replace hJ := hJ xmem
    simp only [mem_iUnion, exists_prop] at hJ ⊢
    rcases hJ with ⟨l, llen , j, jmem, mapxmem⟩
    apply Nat.le_of_lt_succ at llen
    let K := p l llen j
    let hK := hp l llen j
    rw [MapsTo] at hK
    simp only [mem_image] at mapxmem
    rcases mapxmem with ⟨x', x'mem, mapx'⟩
    rw [← Metric.sphere_union_ball] at x'mem
    rcases x'mem with x'mem | x'mem
    · have hK := hK x'mem
      simp only [mem_iUnion, exists_prop] at hK
      rcases hK with ⟨m, mltl, o, omem, mapomem⟩
      use m
      refine ⟨lt_trans mltl (Nat.lt_succ_of_le llen), ?_⟩
      use o
      refine ⟨?_, by rw [← mapx']; exact mapomem⟩
      simp only [Nat.succ_eq_add_one, dite_eq_ite, lt_trans mltl (Nat.lt_succ_of_le llen),
        ↓reduceIte, Finite.mem_toFinset, mem_union, Finset.mem_coe, mem_iUnion, Subtype.exists,
        exists_prop, I, I']
      right
      use l
      use llen
      use j
    · use l
      refine ⟨Nat.lt_succ_of_le llen, ?_ ⟩
      use j
      refine ⟨?_, by rw [← mapx']; exact Set.mem_image_of_mem (map l j) x'mem⟩
      simp only [Nat.succ_eq_add_one, dite_eq_ite, Nat.lt_succ_of_le llen, ↓reduceIte,
        Finite.mem_toFinset, mem_union, Finset.mem_coe, mem_iUnion, Subtype.exists, exists_prop, I,
        I']
      left
      exact jmem

lemma finite_of_finite_cells (finite : _root_.Finite (Σ n, cell C n)) : Finite C where
  finitelevels := by
    by_cases h : IsEmpty (Σ n, cell C n)
    · simp only [Filter.eventually_atTop, ge_iff_le]
      use 0
      intro n _
      simp only [isEmpty_sigma] at h
      exact h n
    rw [not_isEmpty_iff] at h
    have _ := Fintype.ofFinite (Σ n, cell C n)
    classical
    let A := Finset.image (fun ⟨n, j⟩ ↦ n) (Finset.univ : Finset (Σ n, cell C n))
    have nonempty : A.Nonempty := by
      simp only [Finset.image_nonempty, A]
      exact Finset.univ_nonempty
    let n := A.max' nonempty
    simp only [Filter.eventually_atTop, ge_iff_le]
    use n + 1
    intro m nle
    by_contra h'
    have mmem : m ∈ A := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, A]
      simp only [not_isEmpty_iff, ← exists_true_iff_nonempty] at h'
      rcases h' with ⟨j, _⟩
      use ⟨m, j⟩
    have := A.le_max' m mmem
    simp only [ge_iff_le, n] at nle
    linarith
  finitecells := by
    intro n
    let f (j : cell C n) := (⟨n, j⟩ : Σ n, cell C n)
    apply Finite.of_injective f
    simp only [Function.Injective]
    intro i j eq
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and, f] at eq
    exact eq

lemma finite_cells_of_finite (finite : Finite C) : _root_.Finite (Σ n, cell C n) := by
  have finitelvl := finite.finitelevels
  have _ := finite.finitecells
  simp only [Filter.eventually_atTop, ge_iff_le] at finitelvl
  rcases finitelvl with ⟨n, hn⟩
  have : ∀ m (j : cell C m), m < n := by
    intro m j
    by_contra h
    push_neg at h
    replace hn := hn m h
    rw [← not_nonempty_iff, ← exists_true_iff_nonempty] at hn
    apply hn
    use j
  let f : (Σ (m : {m : ℕ // m < n}), cell C m) ≃ Σ m, cell C m := {
    toFun := fun ⟨m, j⟩ ↦ ⟨m, j⟩
    invFun := fun ⟨m, j⟩ ↦ ⟨⟨m, this m j⟩, j⟩
    left_inv := by simp only [Function.LeftInverse, implies_true]
    right_inv := by simp only [Function.RightInverse, Function.LeftInverse, Sigma.eta, implies_true]
  }
  rw [← Equiv.finite_iff f]
  apply Finite.instSigma

lemma finite_iff_finite_cells : Finite C ↔ _root_.Finite (Σ n, cell C n) :=
  ⟨finite_cells_of_finite _, finite_of_finite_cells _⟩
