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
  union : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C

variable [T2Space X] (C : Set X) [hC : CWComplex C]
/- Now that `CWComplex` is a class, try to remove `hC` everywhere, and instead make
`C` explicit if needed (for `map` it's probably fine to have `C` explicit, and have Lean infer `C`
from the type of `i : cell C n`, though sometimes you might have to give it explicitly with
`map (C := C)`
-/
namespace CWComplex



/-- A non-standard definition of the levels useful for induction.
  The typical level is defined in terms of levelaux.-/
def levelaux (n : ℕ∞) : Set X :=
  ⋃ (m : ℕ) (hm : m < n) (j : hC.cell m), hC.map m j '' closedBall 0 1

/-- The `n`-th level of a CW-complex, for `n ∈ ℕ ∪ ∞`. -/
def level (n : ℕ∞) : Set X :=
  hC.levelaux (n + 1)

-- I recommend to avoid a lemma like this (and subtraction on the natural numbers in general),
-- if possible.
-- When you want to apply tris, try to instead rewrite
-- it to `hC.levelaux (m + 1) = hC.level m` which is true by definition.
lemma levelaux_eq_level_sub_one {n : ℕ∞} (npos : n ≠ 0) : hC.levelaux n = hC.level (n - 1) := by
  unfold level
  congrm (hC.levelaux ?_)
  by_cases ntop : n = ⊤
  · simp only [ntop, ENat.top_sub_one, top_add]
  · push_neg at ntop
    let m := ENat.toNat n
    have coemn: ↑m = n := ENat.coe_toNat ntop
    rw [← coemn] at npos ⊢
    norm_cast at npos ⊢
    push_neg at npos
    rw [← Nat.pred_eq_sub_one, ← Nat.succ_eq_add_one]
    rw [Nat.succ_pred npos]

lemma levelaux_zero_eq_empty : hC.levelaux 0 = ∅ := by
  unfold levelaux
  simp only [isEmpty_Prop, not_lt, zero_le, iUnion_of_empty, iUnion_empty]

-- finite type seperately

class Finite.{u} {X : Type u} [TopologicalSpace X] (C : Set X) [cwcomplex : CWComplex C] : Prop where
  finitelevels : ∀ᶠ n in Filter.atTop, IsEmpty (cwcomplex.cell n)
  finitecells (n : ℕ) : Finite (cwcomplex.cell n)

@[simp] lemma levelaux_top : hC.levelaux ⊤ = C := by
  simp only [levelaux, lt_top_iff_ne_top, ne_eq, ENat.coe_ne_top, not_false_eq_true, iUnion_true, ←
    hC.union]

@[simp] lemma level_top : hC.level ⊤ = C := by
  simp only [level, top_add, levelaux_top]

lemma iUnion_map_sphere_subset_levelaux (l : ℕ) : ⋃ (j : hC.cell l), hC.map l j '' sphere 0 1 ⊆ hC.levelaux l := by
  rw [CWComplex.levelaux]
  norm_cast
  intro x xmem
  rw [mem_iUnion] at xmem
  rcases xmem with ⟨e, xmeme⟩
  rcases hC.mapsto l e with ⟨I, hI⟩
  apply MapsTo.image_subset at hI
  apply hI at xmeme
  have : ⋃ m, ⋃ (_ : m < l), ⋃ j ∈ I m, ↑(hC.map m j) '' closedBall 0 1 ⊆ ⋃ m, ⋃ (_ : m < l), ⋃ j, ↑(hC.map m j) '' closedBall 0 1 := by
    apply iUnion_mono
    simp only [iUnion_subset_iff]
    intro i iltl e ememIi y ymem
    simp only [mem_iUnion, exists_prop]
    exact ⟨iltl, ⟨e, ymem⟩⟩
  exact this xmeme

-- fix the statement
lemma iUnion_map_sphere_subset_level (l : ℕ) : ⋃ (j : hC.cell l), ↑(hC.map l j) '' sphere 0 1 ⊆ hC.levelaux l := by
  simp only [level, iUnion_map_sphere_subset_levelaux]

-- rename: levelaux_mono (the idea is that this statement is equivalent to `Monotone (hC.levelaux)`,
-- even though you probably don't want to state it like that).
lemma levelaux_subset_levelaux_of_le {n m : ℕ∞} (h : m ≤ n) : hC.levelaux m ⊆ hC.levelaux n := by
  repeat rw [CWComplex.levelaux]
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

lemma level_subset_level_of_le {n m : ℕ∞} (h : m ≤ n) : hC.level m ⊆ hC.level n := by
  simp only [level, hC.levelaux_subset_levelaux_of_le (add_le_add_right h 1)]

lemma iUnion_levelaux_eq_levelaux (n : ℕ∞) : ⋃ (m : ℕ) (hm : m < n + 1), hC.levelaux m = hC.levelaux n := by
  apply subset_antisymm
  · simp_rw [iUnion_subset_iff]
    intros i hi
    exact levelaux_subset_levelaux_of_le _ (ENat.le_of_lt_add_one hi)
  · intro x xmem
    rw [mem_iUnion]
    by_cases h : n = ⊤
    · rw [h, top_add]
      rw [h, CWComplex.levelaux, mem_iUnion] at xmem
      rcases xmem with ⟨i, xmemi⟩
      simp only [mem_iUnion, exists_prop] at xmemi
      use i + 1
      simp
      constructor
      · rw [WithTop.add_lt_top]
        exact ⟨xmemi.1 , (by apply lt_top_iff_ne_top.2 (WithTop.natCast_ne_top 1))⟩
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
      simp
      norm_cast
      rw [coemn]
      exact ⟨lt_add_one m, xmem⟩

-- is this really missing? move to auxiliary
lemma ENat.add_coe_lt_add_coe_right {n m : ℕ∞} {k : ℕ} : n + k < m + k ↔ n < m := by
  cases' n with n
  · simp
  cases' m with m
  · norm_cast; simp [ENat.coe_lt_top, -Nat.cast_add]
  · norm_cast; simp_all

-- Here is a different proof, but this was more painful than I thought
lemma iUnion_level_eq_level (n : ℕ∞) : ⋃ (m : ℕ) (hm : m < n + 1), hC.level m = hC.level n := by
  simp_rw [level, ← iUnion_levelaux_eq_levelaux C (n + 1)]
  ext; simp
  constructor
  · intro ⟨i, hin, hiC⟩
    refine ⟨i + 1, ?_, hiC⟩
    push_cast
    exact ENat.add_coe_lt_add_coe_right.mpr hin
  · intro ⟨i, hin, hiC⟩
    cases' i with i
    · refine ⟨0, ?_, levelaux_subset_levelaux_of_le C (by norm_num) hiC⟩
      norm_cast
      -- this should be a lemma
      rw [← ENat.one_le_iff_pos]
      exact le_add_self
    · refine ⟨i, ?_, hiC⟩
      push_cast
      exact ENat.add_coe_lt_add_coe_right.mp hin

/- separate out some lemmas, e.g.
hC.map m j '' closedBall 0 1 ⊆ hC.map m j '' ball 0 1 ∪ levelaux C m
and/or
levelaux C (m + 1) = levelaux C m ∪ ⋃ (j : hC.cell m), hC.map m j '' closedBall 0 1
and/or
levelaux C (m + 1) = levelaux C m ∪ ⋃ (j : hC.cell m), hC.map m j '' ball 0 1

Maybe you're already doing some of that below, without relying on this?
Also, maybe the induction is a little easier if you just do the hard inclusion by induction (and the easy inclusion without induction)
-/

/- We can also define the levels using `ball` instead of `closedBall`, using assumption `mapsto`. -/
lemma iUnion_ball_eq_levelaux (n : ℕ∞) : ⋃ (m : ℕ) (hm : m < n) (j : hC.cell m), hC.map m j '' ball 0 1 = hC.levelaux n := by
  induction' n using ENat.nat_induction with n hn hn
  · simp [levelaux]
  · norm_cast at *
    rw [aux1 n (fun m j ↦ ↑(hC.map m j) '' ball 0 1)]
    rw [hn]
    nth_rewrite 2 [CWComplex.levelaux]
    symm
    norm_cast
    calc
      ⋃ m, ⋃ (_ : m < Nat.succ n), ⋃ j, ↑(hC.map m j) '' closedBall 0 1
      = (⋃ (j : hC.cell n), ↑(hC.map n j) '' closedBall 0 1) ∪ ⋃ m, ⋃ (_ : Nat.cast m < ↑n), ⋃ j, ↑(hC.map m j) '' closedBall 0 1 := by
        apply aux1 n (fun m j ↦ ↑(hC.map m j) '' closedBall 0 1)
      _ = (⋃ (j : hC.cell n), ↑(hC.map n j) '' closedBall 0 1) ∪ hC.levelaux n := by
        rw [CWComplex.levelaux]
        norm_cast
      _ = (⋃ (j : hC.cell n), ↑(hC.map n j) '' (sphere 0 1 ∪ ball 0 1)) ∪ hC.levelaux n := by rw [sphere_union_ball]
      _ = (⋃ (j : hC.cell n), ↑(hC.map n j) '' sphere 0 1 ∪ ↑(hC.map n j) '' ball 0 1) ∪ hC.levelaux n := by
        have : ⋃ (j : hC.cell n), ↑(hC.map n j) '' (sphere 0 1 ∪ ball 0 1) = ⋃ (j : hC.cell n), ↑(hC.map n j) '' sphere 0 1 ∪ ↑(hC.map n j) '' ball 0 1 := by
          apply iUnion_congr
          intro i
          rw [image_union]
        rw [this]
      _ = (⋃ (j : hC.cell n), ↑(hC.map n j) '' sphere 0 1) ∪ (⋃ (j : hC.cell n), ↑(hC.map n j) '' ball 0 1) ∪ hC.levelaux n := by
        rw [iUnion_union_distrib]
      _ = (⋃ (j : hC.cell n), ↑(hC.map n j) '' ball 0 1) ∪ ((⋃ (j : hC.cell n), ↑(hC.map n j) '' sphere 0 1) ∪ hC.levelaux n) := by
        rw [← union_assoc, union_comm (⋃ j, ↑(hC.map n j) '' sphere 0 1), union_assoc]
      _ = (⋃ j, ↑(hC.map n j) '' ball 0 1) ∪ hC.levelaux ↑n := by
        have : (⋃ (j : hC.cell n), ↑(hC.map n j) '' sphere 0 1) ∪ hC.levelaux n = hC.levelaux n := union_eq_right.2 (hC.iUnion_map_sphere_subset_levelaux n)
        rw [this]
  · have : ⋃ (m : ℕ), ⋃ (_ : ↑m < (⊤ : ℕ∞)), ⋃ j, ↑(hC.map m j) '' ball 0 1 = ⋃ (n : ℕ) (hn : ↑n < (⊤ : ℕ∞)), ⋃ (m : ℕ) (hm : m < n), ⋃ j, ↑(hC.map m j) '' ball 0 1 := by -- TODO : extract and generalize this in some way
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
    rw [this, ← hC.iUnion_levelaux_eq_levelaux ⊤, top_add]
    apply iUnion_congr
    intro i
    norm_cast at hn
    rw [hn]

lemma union' : ⋃ (n : ℕ) (j : hC.cell n), hC.map n j '' ball 0 1 = C := by
  simp only [← hC.levelaux_top, ← hC.iUnion_ball_eq_levelaux, ENat.coe_lt_top, iUnion_true]

-- rename to `eq_cell_of_not_disjoint` or similar
lemma not_disjoint_equal {n : ℕ} {j : hC.cell n} {m : ℕ} {i : hC.cell m} (notdisjoint: ¬ Disjoint (↑(hC.map n j) '' ball 0 1) (↑(hC.map m i) '' ball 0 1)) :
(⟨n, j⟩ : (Σ n, hC.cell n)) = ⟨m, i⟩ := by
  by_contra h'
  push_neg at h'
  apply notdisjoint
  have := hC.pairwiseDisjoint
  simp only [PairwiseDisjoint, Set.Pairwise, Function.onFun] at this
  exact @this ⟨n, j⟩ (by simp) ⟨m, i⟩ (by simp) h'

lemma iUnion_ball_eq_level (n : ℕ∞) : ⋃ (m : ℕ) (hm : m < n + 1) (j : hC.cell m), hC.map m j '' ball 0 1 = hC.level n := by
  rw [level]
  exact hC.iUnion_ball_eq_levelaux (n + 1)

lemma mapsto_sphere_levelaux (n : ℕ) (j : hC.cell n) (nnezero : n ≠ 0) : MapsTo (hC.map n j) (sphere 0 1) (hC.levelaux  n) := by
  rcases hC.mapsto n j with ⟨I, hI⟩
  rw [Set.mapsTo'] at *
  apply subset_trans hI
  intro x xmem
  simp only [mem_iUnion, exists_prop] at xmem
  rcases xmem with ⟨i, ⟨iltn, ⟨j, ⟨jmemI, xmem⟩⟩⟩⟩
  simp only [CWComplex.levelaux, mem_iUnion, exists_prop]
  use i
  norm_cast
  exact ⟨iltn, ⟨j, xmem⟩⟩

-- Use the command `#lint` here: it will tell you that `nnezero` is not used in the above proof.
-- I recommend writing `#lint` at the bottom of each of your files, and looking at the output.
-- (you can ignore the request for documentation strings, at least until you make a PR to mathlib)
-- This makes the case distinction in `exists_mem_ball_of_mem_levelaux` unnecessary.

lemma mapsto_sphere_level (n : ℕ) (j : hC.cell n) (nnezero : n ≠ 0) : MapsTo (hC.map n j) (sphere 0 1) (hC.level (Nat.pred n)) := by
  norm_cast
  rw [level, ← ENat.coe_one, ← ENat.coe_add, Nat.add_one, Nat.succ_pred nnezero]
  exact hC.mapsto_sphere_levelaux n j nnezero

lemma exists_mem_ball_of_mem_levelaux {n : ℕ∞} {x : X} (xmemlvl : x ∈ hC.levelaux n) : ∃ (m : ℕ) (_ : m < n) (j : hC.cell m), x ∈ ↑(hC.map m j) '' ball 0 1 := by
  induction' n using ENat.nat_induction with n hn hn
  · simp [levelaux] at xmemlvl
  · simp only [Nat.cast_succ, levelaux, mem_iUnion, exists_prop] at xmemlvl
    rcases xmemlvl with ⟨m, ⟨mlt, h⟩⟩
    by_cases h': m = 0
    · use 0
      simp only [Nat.cast_zero, Nat.cast_succ, zero_le, exists_const]
      rw [h'] at h
      rcases h with ⟨j, hj⟩
      norm_cast at *
      rw [h'] at mlt
      use mlt
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
    · have := hC.mapsto_sphere_levelaux m j h'
      rw [Set.mapsTo'] at this
      apply this at h
      norm_cast at *
      rw [Nat.add_one] at mlt
      rcases hn ((hC.levelaux_subset_levelaux_of_le (by norm_cast; exact (Nat.le_of_lt_succ mlt))) h) with ⟨m, hm⟩
      simp only [exists_prop] at hm
      use m
      simp only [exists_prop]
      exact ⟨lt_of_lt_of_le hm.1 (Nat.le_succ n), hm.2⟩
    · use m
      simp only [Nat.cast_succ, exists_prop]
      exact ⟨mlt, ⟨j, h⟩⟩
  · rw [← hC.iUnion_levelaux_eq_levelaux] at xmemlvl
    simp at xmemlvl
    rcases xmemlvl with ⟨i, ⟨ilttop, xmemlvli⟩⟩
    rcases (hn i xmemlvli) with ⟨m, hm⟩
    simp only [exists_prop] at hm
    use m
    simp only [exists_prop]
    exact ⟨lt_trans hm.1 ilttop, hm.2⟩

lemma exists_mem_ball_of_mem_level {n : ℕ∞} {x : X} (xmemlvl : x ∈ hC.level n) : ∃ (m : ℕ) (_ : m ≤ n) (j : hC.cell m), x ∈ ↑(hC.map m j) '' ball 0 1 := by
  rw [level] at xmemlvl
  rcases hC.exists_mem_ball_of_mem_levelaux xmemlvl with ⟨m, hm⟩
  use m
  rw [exists_prop] at *
  exact ⟨ENat.le_of_lt_add_one hm.1, hm.2⟩

lemma levelaux_inter_image_closedBall_eq_levelaux_inter_image_sphere {n : ℕ∞} {m : ℕ}{j : hC.cell m} (nlem : n ≤ m) : hC.levelaux n ∩ ↑(hC.map m j) '' closedBall 0 1 = hC.levelaux n ∩ ↑(hC.map m j) '' sphere 0 1 := by
  ext x
  constructor
  · intro ⟨xmemlevel, xmemball⟩
    constructor
    · exact xmemlevel
    rw [← Metric.sphere_union_ball, image_union] at xmemball
    rcases xmemball with h | h
    · exact h
    exfalso
    rcases hC.exists_mem_ball_of_mem_levelaux xmemlevel with ⟨l, ⟨llen, ⟨i, xmem⟩⟩⟩
    have : ¬ Disjoint (↑(hC.map m j) '' ball 0 1) (↑(hC.map l i) '' ball 0 1) := by
      rw [not_disjoint_iff]
      use x
    have := hC.not_disjoint_equal this
    simp at this
    rcases this with ⟨eq1, eq2⟩
    subst m
    exact (lt_self_iff_false n).1 (lt_of_le_of_lt nlem llen)
  · intro xmem
    exact ⟨xmem.1,  (Set.image_subset ↑(hC.map m j) Metric.sphere_subset_closedBall) xmem.2⟩

lemma level_inter_image_closedBall_eq_level_inter_image_sphere {n : ℕ∞} {m : ℕ}{j : hC.cell m} (nltm : n < m) : hC.level n ∩ ↑(hC.map m j) '' closedBall 0 1 = hC.level n ∩ ↑(hC.map m j) '' sphere 0 1 := by
  apply Order.succ_le_of_lt at nltm
  rw [ENat.succ_def] at nltm
  simp only [level]
  exact hC.levelaux_inter_image_closedBall_eq_levelaux_inter_image_sphere nltm

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

lemma isCompact_map_closedBall (n : ℕ) (i : hC.cell n) : IsCompact (hC.map n i '' closedBall 0 1) := by
  apply IsCompact.image_of_continuousOn
  apply isCompact_closedBall
  exact hC.cont n i

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

lemma levelaux_succ_eq_levelaux_union_iUnion (n : ℕ) : hC.levelaux (↑n + 1) = hC.levelaux ↑n ∪ ⋃ (j : hC.cell ↑n), hC.map ↑n j '' closedBall 0 1 := by
  simp [CWComplex.levelaux]
  norm_cast
  rw [Nat.add_one, union_comm]
  exact aux1 n (fun m j ↦ ↑(hC.map m j) '' closedBall 0 1)

lemma level_succ_eq_level_union_iUnion (n : ℕ) : hC.level (↑n + 1) = hC.level ↑n ∪ ⋃ (j : hC.cell (↑n + 1)), hC.map (↑n + 1) j '' closedBall 0 1 := by
  simp [CWComplex.level]
  exact hC.levelaux_succ_eq_levelaux_union_iUnion (n + 1)

lemma map_closedBall_subset_levelaux (n : ℕ) (j : hC.cell n) : (hC.map n j) '' closedBall 0 1 ⊆ hC.levelaux (n + 1) := by
  rw [CWComplex.levelaux]
  intro x xmem
  simp only [mem_iUnion, exists_prop]
  use n
  norm_cast
  exact ⟨lt_add_one n, ⟨j,xmem⟩⟩

lemma map_closedBall_subset_level (n : ℕ) (j : hC.cell n) : (hC.map n j) '' closedBall 0 1 ⊆ hC.level n := by
  rw [CWComplex.level]
  exact hC.map_closedBall_subset_levelaux n j

lemma map_closedBall_subset_complex (n : ℕ) (j : hC.cell n) : (hC.map n j) '' closedBall 0 1 ⊆ C := by
  apply subset_trans (hC.map_closedBall_subset_level n j) (by simp_rw [← hC.level_top]; apply hC.level_subset_level_of_le le_top)

lemma map_ball_subset_levelaux (n : ℕ) (j : hC.cell n) : (hC.map n j) '' ball 0 1 ⊆ hC.levelaux (n + 1) := subset_trans (image_mono Metric.ball_subset_closedBall) (hC.map_closedBall_subset_levelaux n j)

lemma map_ball_subset_level (n : ℕ) (j : hC.cell n) : (hC.map n j) '' ball 0 1 ⊆ hC.level n := subset_trans (image_mono Metric.ball_subset_closedBall) (hC.map_closedBall_subset_level n j)

lemma map_ball_subset_complex (n : ℕ) (j : hC.cell n) : (hC.map n j) '' ball 0 1 ⊆ C := by
  apply subset_trans (hC.map_ball_subset_level n j) (by simp_rw [← hC.level_top]; apply hC.level_subset_level_of_le le_top)

lemma map_ball_subset_map_closedball {n : ℕ} {j : hC.cell n} : hC.map n j '' ball 0 1 ⊆ hC.map n j '' closedBall 0 1 := image_mono ball_subset_closedBall

lemma closure_map_ball_eq_map_closedball {n : ℕ} {j : hC.cell n} : closure (hC.map n j '' ball 0 1) = hC.map n j '' closedBall 0 1 := by
  apply subset_antisymm
  · rw [IsClosed.closure_subset_iff (hC.isClosed_map_closedBall n j)]
    exact hC.map_ball_subset_map_closedball
  · have : ContinuousOn (hC.map n j) (closure (ball 0 1)) := by
      rw [closure_ball]
      exact hC.cont n j
      simp
    rw [← closure_ball]
    apply ContinuousOn.image_closure this
    simp

-- I think this proof should be moved up, since it can be used to prove some easier estimates that are used earlier.

-- could this proof be simplified using `exists_mem_ball_of_mem_level`?
lemma mapsto' (n : ℕ) (i : hC.cell n) : ∃ I : Π m, Finset (hC.cell m),
MapsTo (hC.map n i) (sphere 0 1) (⋃ (m < n) (j ∈ I m), hC.map m j '' ball 0 1) := by
  induction' n using Nat.case_strong_induction_on with n hn
  · simp [sphere_zero_dim_empty, MapsTo]
  · rcases hC.mapsto (Nat.succ n) i with ⟨J, hJ⟩
    -- use the `choose` tactic on `hn`
    let p (x : Σ' (m : {m : ℕ // m ≤ n}), J m) := Classical.choose (hn x.1 (x.1).2 x.2)
    let I' m := if mltnsucc : m < Nat.succ n then (J m).toSet ∪ ⋃ (l : {l : ℕ // l ≤ n}) (y : J l), p ⟨⟨l, l.2⟩, y⟩ m else (J m).toSet
    have : ∀ m, Set.Finite (I' m) := by
      intro m
      simp [I']
      by_cases h : m < Nat.succ n
      · simp [h]
        apply Set.finite_iUnion
        intro ⟨l, llen⟩
        apply Set.finite_iUnion
        intro ⟨x, xmem⟩
        simp only [Finset.finite_toSet]
      · simp [h]
    let I m := Set.Finite.toFinset (this m)
    use I
    rw [MapsTo] at *
    intro x xmem
    have hJ := hJ xmem
    simp only [mem_iUnion, exists_prop] at *
    rcases hJ with ⟨l, llen , j, jmem, mapxmem⟩
    apply Nat.le_of_lt_succ at llen
    let K := Classical.choose (hn l llen j)
    let hK := Classical.choose_spec (hn l llen j)
    rw [MapsTo] at hK
    simp only [mem_image] at mapxmem
    rcases mapxmem with ⟨x', x'mem, mapx'⟩
    rw [← Metric.sphere_union_ball] at x'mem
    rcases x'mem with x'mem | x'mem
    · have hK := hK x'mem
      simp only [mem_iUnion, exists_prop] at hK
      rcases hK with ⟨m, mltl, o, omem, mapomem⟩
      use m
      constructor
      · exact lt_trans mltl (Nat.lt_succ_of_le llen)
      use o
      constructor
      · simp [I, I', lt_trans mltl (Nat.lt_succ_of_le llen)]
        right
        use l
        use llen
        use j
        use jmem
      rw [← mapx']
      exact mapomem
    · use l
      constructor
      · exact Nat.lt_succ_of_le llen
      use j
      constructor
      · simp [I, I', Nat.lt_succ_of_le llen]
        left
        exact jmem
      rw [← mapx']
      exact Set.mem_image_of_mem (hC.map l j) x'mem

lemma finite_of_finite_cells (finite : _root_.Finite (Σ n, hC.cell n)) : Finite C where
  finitelevels := by
    by_cases h : IsEmpty (Σ n, hC.cell n)
    · simp only [Filter.eventually_atTop, ge_iff_le]
      use 0
      intro n _
      simp only [isEmpty_sigma] at h
      exact h n
    rw [not_isEmpty_iff] at h
    have _ := Fintype.ofFinite (Σ n, hC.cell n)
    classical
    let A := Finset.image (fun ⟨n, j⟩ ↦ n) (Finset.univ : Finset (Σ n, hC.cell n))
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
    simp [n] at nle
    linarith
  finitecells := by
    intro n
    let f (j : hC.cell n) := (⟨n, j⟩ : Σ n, hC.cell n)
    apply Finite.of_injective f
    simp only [Function.Injective]
    intro i j eq
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and, f] at eq
    exact eq

lemma finite_cells_of_finite (finite : Finite C) : _root_.Finite (Σ n, hC.cell n) := by
  have finitelvl := finite.finitelevels
  have _ := finite.finitecells
  simp only [Filter.eventually_atTop, ge_iff_le] at finitelvl
  rcases finitelvl with ⟨n, hn⟩
  have : ∀ m (j : hC.cell m), m < n := by
    intro m j
    by_contra h
    push_neg at h
    replace hn := hn m h
    rw [← not_nonempty_iff, ← exists_true_iff_nonempty] at hn
    apply hn
    use j
  let f : (Σ (m : {m : ℕ // m < n}), hC.cell m) ≃ Σ m, hC.cell m := {
    toFun := fun ⟨m, j⟩ ↦ ⟨m, j⟩
    invFun := fun ⟨m, j⟩ ↦ ⟨⟨m, this m j⟩, j⟩
    left_inv := by simp only [Function.LeftInverse, implies_true]
    right_inv := by simp only [Function.RightInverse, Function.LeftInverse, Sigma.eta, implies_true]
  }
  rw [← Equiv.finite_iff f]
  apply Finite.instSigma

lemma finite_iff_finite_cells : Finite C ↔ _root_.Finite (Σ n, hC.cell n) :=
  ⟨hC.finite_cells_of_finite, hC.finite_of_finite_cells⟩
