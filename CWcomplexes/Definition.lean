import CWcomplexes.auxiliary
import Mathlib.Analysis.NormedSpace.Real

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open Metric Set

variable {X : Type*} [t : TopologicalSpace X]

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
  pairwiseDisjoint' :
    (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1)
  mapsto (n : ℕ) (i : cell n) : ∃ I : Π m, Finset (cell m),
    MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j ∈ I m), map m j '' closedBall 0 1)
  closed' (A : Set X) (asubc : A ⊆ C) : IsClosed A ↔ ∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)
  union' : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C


variable [T2Space X] {C : Set X} [CWComplex C]


namespace CWComplex

def ocell (n : ℕ) (i : cell C n) : Set X := map n i '' ball 0 1

def ccell (n : ℕ) (i : cell C n) : Set X := map n i '' closedBall 0 1

--maybe I should have named this fcell instead? Should I change it?
def ecell (n : ℕ) (i : cell C n) : Set X := map n i '' sphere 0 1

lemma pairwiseDisjoint :
  (univ : Set (Σ n, cell C n)).PairwiseDisjoint (fun ni ↦ ocell ni.1 ni.2) := pairwiseDisjoint'

lemma ecell_subset (n : ℕ) (i : cell C n) : ∃ I : Π m, Finset (cell C m),
    ecell n i ⊆ (⋃ (m < n) (j ∈ I m), ccell m j) := by
  rcases mapsto n i with ⟨I, hI⟩
  use I
  rw [mapsTo'] at hI
  exact hI

lemma closed (A : Set X) (asubc : A ⊆ C) :
    IsClosed A ↔ ∀ n (j : cell C n), IsClosed (A ∩ ccell n j) :=
  closed' A asubc

lemma union : ⋃ (n : ℕ) (j : cell C n), ccell n j = C := union'

lemma ocell_subset_ccell (n : ℕ) (i : cell C n) : ocell n i ⊆ ccell n i :=
  image_mono Metric.ball_subset_closedBall

lemma ecell_subset_ccell (n : ℕ) (i : cell C n) : ecell n i ⊆ ccell n i :=
  image_mono Metric.sphere_subset_closedBall

lemma ecell_union_ocell_eq_ccell (n : ℕ) (i :cell C n) : ecell n i ∪ ocell n i = ccell n i := by
  simp_rw [ecell, ocell, ccell, ← image_union]
  congrm map n i '' ?_
  exact sphere_union_ball

/-- A non-standard definition of the levels useful for induction.
  The typical level is defined in terms of levelaux.-/
def levelaux (C : Set X) [CWComplex C] (n : ℕ∞) : Set X :=
  ⋃ (m : ℕ) (hm : m < n) (j : cell C m), ccell m j

/-- The `n`-th level of a CW-complex, for `n ∈ ℕ ∪ ∞`. -/
def level (C : Set X) [CWComplex C] (n : ℕ∞) : Set X :=
  levelaux C (n + 1)

lemma levelaux_zero_eq_empty : levelaux C 0 = ∅ := by
  unfold levelaux
  simp only [isEmpty_Prop, not_lt, zero_le, iUnion_of_empty, iUnion_empty]

lemma isCompact_ccell {n : ℕ} {i : cell C n} : IsCompact (ccell n i) :=
  (isCompact_closedBall _ _).image_of_continuousOn (cont n i)

lemma isClosed_ccell {n : ℕ} {i : cell C n} : IsClosed (ccell n i) := isCompact_ccell.isClosed

lemma isCompact_ecell {n : ℕ} {i : cell C n} : IsCompact (ecell n i) :=
  (isCompact_sphere _ _).image_of_continuousOn
    (ContinuousOn.mono (cont n i) sphere_subset_closedBall)

lemma isClosed_ecell {n : ℕ} {i : cell C n} : IsClosed (ecell n i) := isCompact_ecell.isClosed

lemma closure_ocell_eq_ccell {n : ℕ} {j : cell C n} : closure (ocell n j) = ccell n j := by
  apply subset_antisymm
    ((IsClosed.closure_subset_iff isClosed_ccell).2 (ocell_subset_ccell n j))
  have : ContinuousOn (map n j) (closure (ball 0 1)) := by
    rw [closure_ball 0 (by exact one_ne_zero)]
    exact cont n j
  rw [ccell, ← closure_ball 0 (by exact one_ne_zero)]
  apply ContinuousOn.image_closure this

class FiniteDimensional.{u} {X : Type u} [TopologicalSpace X] (C : Set X) [CWComplex C] : Prop where
  finitelevels : ∀ᶠ n in Filter.atTop, IsEmpty (cell C n)

class FiniteType.{u} {X : Type u} [TopologicalSpace X] (C : Set X) [CWComplex C] : Prop where
  finitecells (n : ℕ) : Finite (cell C n)

class Finite.{u} {X : Type u} [TopologicalSpace X] (C : Set X) [CWComplex C] : Prop where
  finitelevels : ∀ᶠ n in Filter.atTop, IsEmpty (cell C n)
  finitecells (n : ℕ) : Finite (cell C n)

def CWComplexFiniteType.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (cell : (n : ℕ) → Type u) (map : (n : ℕ)  → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (finitecells : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = closedBall 0 1)
    (cont : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (cont_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (mapsto : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (closed' :
      ∀ (A : Set X) (asubc : A ⊆ C),  IsClosed A ↔ ∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1))
    (union' : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
    CWComplex C where
  cell := cell
  map := map
  source_eq := source_eq
  cont := cont
  cont_symm := cont_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  mapsto n i := by
    let I m := Finite.toFinset (s := (univ : Set (cell m))) (Set.finite_univ)
    use I
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true, I]
    exact mapsto n i
  closed' := closed'
  union' := union'

def CWComplexFinite.{u} {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X)
    (cell : (n : ℕ) → Type u) (map : (n : ℕ)  → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (finitelevels : ∀ᶠ n in Filter.atTop, IsEmpty (cell n))
    (finitecells : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = closedBall 0 1)
    (cont : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (cont_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (mapsto : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (union' : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
    CWComplex C where
  cell := cell
  map := map
  source_eq := source_eq
  cont := cont
  cont_symm := cont_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  mapsto n i := by
    let I m := Finite.toFinset (s := (univ : Set (cell m))) (Set.finite_univ)
    use I
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true, I]
    exact mapsto n i
  closed' A asubc := by
    constructor
    · intro closedA n j
      exact IsClosed.inter closedA
        (IsCompact.image_of_continuousOn (isCompact_closedBall _ _) (cont n j)).isClosed
    intro h
    rw [← inter_eq_left.2 asubc]
    simp only [Filter.eventually_atTop, ge_iff_le] at finitelevels
    obtain ⟨N, hN⟩ := finitelevels
    have union'' : ⋃ (n : {n : ℕ // n < N}), ⋃ j, ↑(map n j) '' closedBall 0 1 = C := by
      rw [← union', iUnion_subtype]
      apply iUnion_congr
      intro n
      ext x
      rw [mem_iUnion]
      refine ⟨fun ⟨_, h⟩ ↦ h, ?_ ⟩
      intro xmem
      have : n < N := by
        by_contra h
        push_neg at h
        simp only [hN n h, iUnion_of_empty, mem_empty_iff_false] at xmem
      use this
    simp_rw [← union'', inter_iUnion]
    apply isClosed_iUnion_of_finite
    intro ⟨n, _⟩
    apply isClosed_iUnion_of_finite
    intro i
    exact h n i
  union' := union'

@[simp] lemma levelaux_top : levelaux C ⊤ = C := by
  simp only [levelaux, lt_top_iff_ne_top, ne_eq, ENat.coe_ne_top, not_false_eq_true, iUnion_true, ←
    union]

@[simp] lemma level_top : level C ⊤ = C := by
  simp only [level, top_add, levelaux_top]

lemma levelaux_mono {n m : ℕ∞} (h : m ≤ n) : levelaux C m ⊆ levelaux C n := by
  simp_rw [levelaux]
  intro x xmem
  rw [mem_iUnion] at xmem
  rcases xmem with ⟨l , xmeml⟩
  simp only [mem_iUnion, exists_prop] at xmeml
  rw [mem_iUnion]
  use l
  simp only [mem_iUnion, exists_prop]
  exact ⟨lt_of_lt_of_le xmeml.1 h, xmeml.2⟩

lemma level_mono {n m : ℕ∞} (h : m ≤ n) : level C m ⊆ level C n := by
  simp only [level, levelaux_mono (add_le_add_right h 1)]

lemma ccell_subset_levelaux (n : ℕ) (j : cell C n) :
    ccell n j ⊆ levelaux C (n + 1) := by
  rw [levelaux]
  intro x xmem
  simp only [mem_iUnion, exists_prop]
  use n
  norm_cast
  exact ⟨lt_add_one n, ⟨j,xmem⟩⟩

lemma ccell_subset_level (n : ℕ) (j : cell C n) :
    ccell n j ⊆ level C n := ccell_subset_levelaux n j

lemma ccell_subset_complex (n : ℕ) (j : cell C n) : ccell n j ⊆ C := by
  apply subset_trans (ccell_subset_level n j)
    (by simp_rw [← level_top]; apply level_mono le_top)

lemma ocell_subset_levelaux (n : ℕ) (j : cell C n) : ocell n j ⊆ levelaux C (n + 1) :=
  subset_trans (ocell_subset_ccell _ _) (ccell_subset_levelaux _ _ )

lemma ocell_subset_level (n : ℕ) (j : cell C n) : ocell n j ⊆ level C n :=
  subset_trans (ocell_subset_ccell _ _) (ccell_subset_level _ _)

lemma ocell_subset_complex (n : ℕ) (j : cell C n) : map n j '' ball 0 1 ⊆ C := by
  apply subset_trans (ocell_subset_level _ _)
    (by simp_rw [← level_top]; exact level_mono le_top)

lemma ecell_subset_levelaux (n : ℕ) (j : cell C n) :
    ecell n j ⊆  levelaux C n := by
  rcases ecell_subset n j with ⟨I, hI⟩
  apply subset_trans hI
  intro x xmem
  simp only [mem_iUnion, exists_prop] at xmem
  rcases xmem with ⟨i, ⟨iltn, ⟨j, ⟨jmemI, xmem⟩⟩⟩⟩
  simp only [levelaux, mem_iUnion, exists_prop]
  use i
  norm_cast
  exact ⟨iltn, ⟨j, xmem⟩⟩

lemma ecell_subset_level (n : ℕ) (j : cell C (n + 1)) :
    ecell (n + 1) j ⊆ level C n := ecell_subset_levelaux _ _

lemma iUnion_ecell_subset_levelaux (l : ℕ) :
    ⋃ (j : cell C l), ecell l j ⊆ levelaux C l :=
  iUnion_subset  (fun _ ↦ ecell_subset_levelaux l _)

lemma iUnion_ecell_subset_level (l : ℕ) :
    ⋃ (j : cell C l), ecell l j ⊆ level C l :=
  subset_trans (iUnion_ecell_subset_levelaux l) (levelaux_mono le_self_add)

lemma ccell_zero_eq_singleton {j : cell C 0} : ccell 0 j = {map 0 j ![]} := by
  simp [ccell, Matrix.empty_eq]

lemma ocell_zero_eq_singleton {j : cell C 0} : ocell 0 j = {map 0 j ![]} := by
  simp [ocell, Matrix.empty_eq]

lemma ecell_zero_eq_empty {j : cell C 0} : ecell 0 j = ∅ := by
  simp [ecell, sphere_zero_dim_empty]

lemma iUnion_levelaux_eq_levelaux (n : ℕ∞) :
    ⋃ (m : ℕ) (hm : m < n + 1), levelaux C m = levelaux C n := by
  apply subset_antisymm
  · simp_rw [iUnion_subset_iff]
    intros i hi
    exact levelaux_mono (ENat.le_of_lt_add_one hi)
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
  simp_rw [level, ← iUnion_levelaux_eq_levelaux (n + 1)]
  ext; simp
  constructor
  · intro ⟨i, hin, hiC⟩
    refine ⟨i + 1, ?_, hiC⟩
    push_cast
    exact ENat.add_coe_lt_add_coe_right.mpr hin
  · intro ⟨i, hin, hiC⟩
    cases' i with i
    · refine ⟨0, ?_, levelaux_mono (by norm_num) hiC⟩
      norm_cast
      exact ENat.add_one_pos
    · refine ⟨i, ?_, hiC⟩
      push_cast
      exact ENat.add_coe_lt_add_coe_right.mp hin

lemma levelaux_succ_eq_levelaux_union_iUnion_ccell (n : ℕ) :
    levelaux C (n + 1) = levelaux C n ∪ ⋃ (j : cell C n), ccell n j := by
  simp_rw [levelaux, Nat.cast_lt]
  norm_cast
  rw [Nat.add_one]
  exact biUnion_lt_succ _ _

lemma level_succ_eq_level_union_iUnion (n : ℕ) :
    level C (n + 1) = level C n ∪ ⋃ (j : cell C (↑n + 1)), ccell (n + 1) j :=
  levelaux_succ_eq_levelaux_union_iUnion_ccell (n + 1)

lemma iUnion_ocell_eq_levelaux (n : ℕ∞) :
    ⋃ (m : ℕ) (hm : m < n) (j : cell C m), ocell m j = levelaux C n := by
  induction' n using ENat.nat_induction with n hn hn
  · simp [levelaux]
  · calc
      ⋃ (m : ℕ), ⋃ (_ : (m : ℕ∞) < ↑n.succ), ⋃ (j : cell C m), ocell m j
      _ = (⋃ m, ⋃ (_ : m < n), ⋃ j, ocell m j) ∪ ⋃ (j : cell C n), ocell n j := by
        norm_cast
        exact biUnion_lt_succ _ _
      _ = levelaux C n ∪ ⋃ (j : cell C n), ocell n j := by
        rw [← hn]
        norm_cast
      _ = levelaux C n ∪ (⋃ (j : cell C n), ecell n j) ∪ ⋃ (j : cell C n), ocell n j := by
        congr
        exact (union_eq_left.2 (iUnion_ecell_subset_levelaux n)).symm
      _ = levelaux C n ∪ ⋃ (j : cell C n), ccell n j := by
        simp_rw [union_assoc, ← iUnion_union_distrib, ecell_union_ocell_eq_ccell]
      _ = (⋃ m, ⋃ (_ : m < n), ⋃ (j : cell C m), ccell m j) ∪ ⋃ (j : cell C n), ccell n j := by
        rw [levelaux]
        norm_cast
      _ = levelaux C n.succ := by
        unfold levelaux
        norm_cast
        exact (biUnion_lt_succ _ _).symm
  · calc
      ⋃ (m : ℕ), ⋃ (_ : (m : ℕ∞) < ⊤), ⋃ j, ocell m j
      _ = ⋃ m, ⋃ (j : cell C m), ocell m j := by
        simp_rw [ENat.coe_lt_top, iUnion_true]
      _ = ⋃ m, ⋃ l, ⋃ (_ : l < m), ⋃ (j : cell C l), ocell l j := (biUnion_lt_eq_iUnion _).symm
      _ = ⋃ (m : ℕ), levelaux C m := by
        apply iUnion_congr
        intro n
        norm_cast at hn
        exact hn n
      _ = ⋃ m, ⋃ l, ⋃ (_ : l < m), ⋃ (j : cell C l), ccell l j := by
        unfold levelaux
        norm_cast
      _ = ⋃ m, ⋃ (j : cell C m), ccell m j := biUnion_lt_eq_iUnion _
      _ = levelaux C ⊤ := by rw [levelaux_top, union]

lemma union_ocell : ⋃ (n : ℕ) (j : cell C n), ocell n j = C := by
  simp only [← levelaux_top, ← iUnion_ocell_eq_levelaux, ENat.coe_lt_top, iUnion_true]

lemma eq_cell_of_not_disjoint {n : ℕ} {j : cell C n} {m : ℕ} {i : cell C m}
    (notdisjoint: ¬ Disjoint (ocell n j) (ocell m i)) :
    (⟨n, j⟩ : (Σ n, cell C n)) = ⟨m, i⟩ := by
  by_contra h'
  push_neg at h'
  apply notdisjoint
  have := pairwiseDisjoint (C := C)
  simp only [PairwiseDisjoint, Set.Pairwise, Function.onFun] at this
  exact this (x := ⟨n, j⟩) (mem_univ _) (y := ⟨m, i⟩) (mem_univ _) h'

lemma iUnion_ocell_eq_level (n : ℕ∞) :
    ⋃ (m : ℕ) (hm : m < n + 1) (j : cell C m), ocell m j = level C n :=
  iUnion_ocell_eq_levelaux (n + 1)

lemma exists_mem_ocell_of_mem_levelaux {n : ℕ∞} {x : X} (xmemlvl : x ∈ levelaux C n) :
    ∃ (m : ℕ) (_ : m < n) (j : cell C m), x ∈ ocell m j := by
  simp_rw [← iUnion_ocell_eq_levelaux, mem_iUnion] at xmemlvl
  obtain ⟨m, mltn, j, _⟩ := xmemlvl
  use m,  mltn, j

lemma exists_mem_ocell_of_mem_level {n : ℕ∞} {x : X} (xmemlvl : x ∈ level C n) :
    ∃ (m : ℕ) (_ : m ≤ n) (j : cell C m), x ∈ ocell m j := by
  rw [level] at xmemlvl
  rcases exists_mem_ocell_of_mem_levelaux xmemlvl with ⟨m, mlen, _⟩
  use m, ENat.le_of_lt_add_one mlen

-- should this go in the thesis?
lemma levelaux_inter_ccell_eq_levelaux_inter_ecell {n : ℕ∞} {m : ℕ}
    {j : cell C m} (nlem : n ≤ m) : levelaux C n ∩ ccell m j =
    levelaux C n ∩ ecell m j := by
  ext x
  constructor
  · intro ⟨xmemlevel, xmemball⟩
    refine ⟨xmemlevel, ?_ ⟩
    rw [← ecell_union_ocell_eq_ccell] at xmemball
    rcases xmemball with h | h
    · exact h
    exfalso
    rcases exists_mem_ocell_of_mem_levelaux xmemlevel with ⟨l, ⟨llen, ⟨i, xmem⟩⟩⟩
    have : ¬ Disjoint (ocell m j) (ocell l i) := by
      rw [not_disjoint_iff]
      use x
    have := eq_cell_of_not_disjoint this
    simp only [Sigma.mk.inj_iff] at this
    rcases this with ⟨eq1, eq2⟩
    subst m
    exact (lt_self_iff_false n).1 (lt_of_le_of_lt nlem llen)
  · intro xmem
    exact ⟨xmem.1,  ecell_subset_ccell _ _ xmem.2⟩

lemma level_inter_ccell_eq_level_inter_ecell {n : ℕ∞} {m : ℕ} {j : cell C m}
    (nltm : n < m) : level C n ∩ ccell m j =
    level C n ∩ ecell m j := by
  apply Order.succ_le_of_lt at nltm
  rw [ENat.succ_def] at nltm
  exact levelaux_inter_ccell_eq_levelaux_inter_ecell nltm

lemma levelaux_inter_ocell_eq_empty {n : ℕ∞} {m : ℕ}
    {j : cell C m} (nlem : n ≤ m) : levelaux C n ∩ ocell m j = ∅ := by
  simp_rw [← iUnion_ocell_eq_levelaux, iUnion_inter, iUnion_eq_empty]
  intro l llt i
  have ne : (⟨l, i⟩ : Σ n, cell C n) ≠ ⟨m, j⟩ := by
    intro eq
    rw [Sigma.mk.inj_iff] at eq
    obtain ⟨eq1, eq2⟩ := eq
    subst l
    simp at eq2
    subst i
    exact LT.lt.false (LT.lt.trans_le llt nlem)
  have := pairwiseDisjoint (C := C)
  simp only [PairwiseDisjoint, Set.Pairwise, Function.onFun, disjoint_iff_inter_eq_empty] at this
  exact this (mem_univ _) (mem_univ _) ne

lemma isClosed_inter_ecell_succ_of_le_isClosed_inter_ccell {A : Set X} {n : ℕ}
  (hn : ∀ m ≤ n, ∀ (j : cell C m), IsClosed (A ∩ ccell m j)) :
  ∀ (j : cell C (n + 1)), IsClosed (A ∩ ecell (n + 1) j) := by
  intro j
  rcases ecell_subset (n + 1) j with ⟨I, hI⟩
  have closedunion : IsClosed (A ∩ ⋃ m, ⋃ (_ : m < n + 1), ⋃ j ∈ I m, ccell m j) := by
    simp only [inter_iUnion]
    let N := {m : ℕ // m < n + 1}
    suffices IsClosed (⋃ (i : N), ⋃ (i_1 : I i), A ∩ ccell (C := C) i i_1) by
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
  suffices IsClosed (A ∩ (⋃ m, ⋃ (_ : m < n + 1), ⋃ j ∈ I m, ccell m j) ∩ ecell (n + 1) j) by
    simpa [inter_assoc, inter_eq_right.2 hI]
  apply closedunion.inter (isClosed_ecell)

lemma strong_induction_isClosed {A : Set X} (asub : A ⊆ C)
    (step : ∀ n, (∀ m ≤ n, ∀ (j : cell C m), IsClosed (A ∩ ccell m j)) →
    ∀ (j : cell C (n + 1)), IsClosed (A ∩ ocell (n + 1) j)) :
    IsClosed A := by
  rw [closed A asub]
  intro n j
  induction' n using Nat.case_strong_induction_on with n hn
  · rw [ccell_zero_eq_singleton]
    exact isClosed_inter_singleton
  replace step := step n hn j
  rw [← ecell_union_ocell_eq_ccell, inter_union_distrib_left]
  exact (isClosed_inter_ecell_succ_of_le_isClosed_inter_ccell hn j).union step

lemma isClosed : IsClosed C := by
  rw [closed (C := C) _ (by rfl)]
  intros
  rw [Set.inter_eq_right.2 (ccell_subset_complex _ _)]
  exact isClosed_ccell

-- could this proof be simplified using `exists_mem_ball_of_mem_level`?
lemma ecell_subset' (n : ℕ) (i : cell C n) : ∃ I : Π m, Finset (cell C m),
    ecell n i ⊆  (⋃ (m < n) (j ∈ I m), ocell m j) := by
  induction' n using Nat.case_strong_induction_on with n hn
  · simp [ecell_zero_eq_empty]
  · rcases ecell_subset (Nat.succ n) i with ⟨J, hJ⟩
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
    intro x xmem
    replace hJ := hJ xmem
    simp only [mem_iUnion, exists_prop] at hJ ⊢
    rcases hJ with ⟨l, llen , j, jmem, mapxmem⟩
    apply Nat.le_of_lt_succ at llen
    let K := p l llen j
    let hK := hp l llen j
    rw [← ecell_union_ocell_eq_ccell] at mapxmem
    rcases mapxmem with mapxmem | mapxmem
    · have hK := hK mapxmem
      simp only [mem_iUnion, exists_prop] at hK
      rcases hK with ⟨m, mltl, o, omem, mapomem⟩
      use m
      refine ⟨lt_trans mltl (Nat.lt_succ_of_le llen), ?_⟩
      use o
      refine ⟨?_, mapomem⟩
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
      refine ⟨?_, mapxmem⟩
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
  ⟨finite_cells_of_finite, finite_of_finite_cells⟩
