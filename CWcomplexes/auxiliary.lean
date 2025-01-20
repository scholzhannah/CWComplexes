import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finite.Sum
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Auxiliary lemmas and definitions

In this file we have auxiliary lemmas that are not in mathlib but do not have any direct relation
to CW-complexes.
They are sorted by topics.
At the bottom of the file there are lemmas that are not used in this project but relate to
definitions and lemmas in this file.
-/

noncomputable section

/-! ### Basic logic and set theory-/

-- it looks like I should rewrite anything that needs this anyways
-- generalization?
--needed in this file
lemma inter_eq_inter_iff_compl {X : Type*} {A B C : Set X} : A ∩ B = C ∩ B ↔ Aᶜ ∩ B = Cᶜ ∩ B := by
  constructor <;> (intro; simp_all [Set.ext_iff, not_iff_not])

/-! ### Different maps -/

-- needed in this file and in examples file
/-- `Function.const` as a `PartialEquiv`.
  It consists of two constant maps in opposite directions. -/
@[simps]
def PartialEquiv.single {X Y : Type*} (x : X) (y : Y) : PartialEquiv X Y where
  toFun := Function.const X y
  invFun := Function.const Y x
  source := {x}
  target := {y}
  map_source' := fun _ _ ↦ by rfl
  map_target' := fun _ _ ↦ by rfl
  left_inv' := fun x' x'mem  ↦ by rw [Set.eq_of_mem_singleton x'mem]; rfl
  right_inv' := fun y' y'mem ↦ by rw [Set.eq_of_mem_singleton y'mem]; rfl

/-! ### Topology -/

-- probably not needed after refactor of kspace
-- needed in kification file
/-- This lemma states that a set `A` is open in a set `B` iff `Aᶜ` is closed in `B`.-/
lemma open_in_iff_compl_closed_in {X : Type*} [TopologicalSpace X] {A B : Set X} :
    (∃ (C : Set X), IsOpen C ∧ A ∩ B = C ∩ B) ↔
    ∃ (C : Set X), IsClosed C ∧ Aᶜ ∩ B = C ∩ B := by
  constructor
  · intro ⟨C, openC, hC⟩
    use Cᶜ
    rw [inter_eq_inter_iff_compl, compl_compl, compl_compl]
    exact ⟨isClosed_compl_iff.2 openC, hC⟩
  · intro ⟨C, closedC, hC⟩
    use Cᶜ
    rw [inter_eq_inter_iff_compl, compl_compl]
    exact ⟨isOpen_compl_iff.2 closedC, hC⟩


-- write an equivalence version

lemma isClosed_left_of_isClosed_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : SeparatedNhds A B) (hAB' : IsClosed (A ∪ B)) : IsClosed A := by
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := hAB
  rw [← isOpen_compl_iff] at hAB' ⊢
  suffices Aᶜ = (A ∪ B)ᶜ ∪ V from this ▸ hAB'.union hV
  have : B ∩ Vᶜ = ∅ := by aesop
  rw [← compl_inj_iff, Set.compl_union, compl_compl, compl_compl, Set.union_inter_distrib_right,
    this, Set.union_empty, Set.left_eq_inter, Set.subset_compl_comm]
  exact (hUV.mono_left hAU).subset_compl_left

lemma isClosed_right_of_isClosed_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : SeparatedNhds A B) (closedAB : IsClosed (A ∪ B)) : IsClosed B :=
  isClosed_left_of_isClosed_union hAB.symm (Set.union_comm _ _ ▸ closedAB)

lemma isClosed_union_iff_isClosed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : SeparatedNhds A B) : IsClosed (A ∪ B) ↔ IsClosed A ∧ IsClosed B :=
  ⟨fun h ↦ ⟨isClosed_left_of_isClosed_union hAB h, isClosed_right_of_isClosed_union hAB h⟩,
    fun ⟨h1, h2⟩ ↦ h1.union h2⟩

/-! ### ↓∩-/

-- what would the notation be called in lemma names

open Set.Notation

--use subtype_val in names

lemma test {X : Type*} {s t : Set X} : (s ↓∩ t)ᶜ = s ↓∩ tᶜ := rfl

lemma IsOpen.subtype_val {X : Type*} [TopologicalSpace X] {s t : Set X}
    (ht : IsOpen t) : IsOpen (s ↓∩ t) := isOpen_induced ht

lemma IsClosed.subtype_val {X : Type*} [TopologicalSpace X] {s t : Set X}
    (ht : IsClosed t) : IsClosed (s ↓∩ t) := by
  rw [← isOpen_compl_iff] at ht ⊢
  exact IsOpen.subtype_val ht

lemma isOpen_inter_of_isOpen_subtype_val {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : IsOpen s) (hst : IsOpen (s ↓∩ t)) : IsOpen (s ∩ t) := by
  rw [isOpen_induced_iff] at hst
  obtain ⟨u, hu, hust⟩ := hst
  rw [Subtype.preimage_val_eq_preimage_val_iff] at hust
  rw [← hust]
  exact hs.inter hu

lemma isClosed_inter_of_isClosed_subtype_val {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : IsClosed s) (hst : IsClosed (s ↓∩ t)) : IsClosed (s ∩ t) := by
  rw [isClosed_induced_iff] at hst
  obtain ⟨u, hu, hust⟩ := hst
  rw [Subtype.preimage_val_eq_preimage_val_iff] at hust
  rw [← hust]
  exact hs.inter hu

/-! ### Random-/

example {α : Sort*} [Finite α] : Finite (PLift α) := by exact instFinitePLift


-- **PR**
-- set_option trace.Meta.synthInstance true
-- use PLift
instance Finite.instPSum {α β : Sort*} [Finite α] [Finite β] : Finite (α ⊕' β) :=
  of_equiv _ ((Equiv.psumEquivSum _ _).symm.trans (Equiv.plift.psumCongr Equiv.plift))

-- not needed anymore but probably still good to contribute?
@[elab_as_elim]
theorem ENat.nat_strong_induction {P : ℕ∞ → Prop} (a : ℕ∞) (h0 : P 0)
    (hsuc : ∀ n : ℕ, (∀ m (_ : m ≤ n), P m) → P n.succ)
    (htop : (∀ n : ℕ, P n) → P ⊤) : P a := by
  have A : ∀ n : ℕ, P n := fun n => Nat.caseStrongRecOn n h0 hsuc
  cases a
  · exact htop A
  · exact A _

-- this isnt really what I want. Need to find a different version ...
-- something with Inhabited probably

def PartialEquiv.restrict {X Y : Type*} (e : PartialEquiv X Y) (A : Set X) (B : Set Y)
    (hA : e.symm '' B ⊆ A) (hB : e '' A ⊆ B) : PartialEquiv A B where
  toFun := fun x ↦ ⟨e x, hB (Set.mem_image_of_mem e x.2)⟩
  invFun := fun x ↦ ⟨e.symm x, hA (Set.mem_image_of_mem e.symm x.2)⟩
  source := A ↓∩ e.source
  target := B ↓∩ e.target
  map_source' := by simp_all
  map_target' := by simp_all
  left_inv' := by simp_all
  right_inv' := by simp_all

-- image of coercion
lemma Int.ceil_eq_floor_add_one_iff {α : Type*} [LinearOrderedRing α] [FloorRing α] (a : α) :
    ⌈a⌉ = ⌊a⌋ + 1 ↔ (¬ ∃ (z : ℤ), z = a) := by
  constructor
  · intro h ⟨z, hz⟩
    subst a
    simp_all
  · intro h
    apply le_antisymm (Int.ceil_le_floor_add_one a)
    rw [Int.add_one_le_ceil_iff]
    by_contra h'
    rw [not_lt_iff_eq_or_lt, ← not_le] at h'
    rcases h' with h' | h'
    · exact h ⟨⌊a⌋, h'⟩
    · exact h' (Int.floor_le a)

-- turns out I should not be using any of this


example (x : ℝ) (h : ¬ |x| ≥ 1) : 1 - x ^ 2 ≥ 0 := by
  rw [ge_iff_le, sub_nonneg, sq_le_one_iff_abs_le_one]
  exact le_of_not_ge h

example (n : ℕ) (i : Fin (n + 1)) (h : ¬ i = n) : (i : ℕ) < n := by
  simp_all only [Fin.natCast_eq_last]
  exact Fin.lt_last_iff_ne_last.mpr h

def scalecoord (x : ℝ) (h : ¬ |x| ≥ 1) : ℝ :=
  (x + 1) / (2 * NNReal.sqrt ⟨(1 - x ^ 2),
  by rw [sub_nonneg, sq_le_one_iff_abs_le_one]; exact le_of_not_ge h⟩)

def lastcoord {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  2 * NNReal.sqrt (∑ (j : Fin n), ⟨(y j) ^ 2, sq_nonneg _⟩) - 1

lemma sum_eq_lastcoord {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) :
    ∑ (i : Fin n), (y i) ^ 2 = ((lastcoord y + 1) ^ 2) / 4 := by
  simp only [lastcoord, sub_add_cancel, mul_pow]
  norm_cast
  simp [NNReal.sq_sqrt]

lemma lastcoord_lt_one_of_ball {n : ℕ} (y : EuclideanSpace ℝ (Fin n))
    (h : y ∈ Metric.ball 0 1) : lastcoord y < 1 := by
  simp only [lastcoord, Real.coe_sqrt, NNReal.coe_sum, NNReal.coe_mk, sub_lt_iff_lt_add,
    (by norm_num : (1 : ℝ) + 1 = 2)]
  apply mul_lt_of_lt_one_right zero_lt_two
  simp_all [EuclideanSpace.norm_eq]

lemma abs_lastcoord_le_one_of_ball {n : ℕ} (y : EuclideanSpace ℝ (Fin n))
    (h : y ∈ Metric.ball 0 1) : |lastcoord y| ≤ 1 := by
  rw [abs_le]
  refine ⟨?_, (lastcoord_lt_one_of_ball y h).le⟩
  simp [lastcoord]

open Metric in
def sphereToDisc (n : ℕ) :
    PartialEquiv (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin n)) where
  toFun x i := if h : |x (Fin.last n)| ≥ 1 then 0
    else (scalecoord (x (Fin.last n)) h) * x i.castSucc
  invFun y i := if h : i = Fin.last n then lastcoord y
    else if lastcoord y = - 1 then 0
    else (2 * Real.sqrt (1 - (lastcoord y) ^ 2) / (lastcoord y + 1))
    * y ⟨i, Fin.lt_last_iff_ne_last.mpr h⟩
  source := sphere 0 1 \ {(fun i ↦ if i = Fin.last n then 1
    else 0 : EuclideanSpace ℝ (Fin (n + 1)))}
  target := ball 0 1
  map_source' := by
    intro x ⟨hx1, _⟩
    by_cases h : |x (Fin.last n)| ≥ 1
    · simp [h, EuclideanSpace.norm_eq]
    · simp only [mem_sphere_iff_norm, sub_zero, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs,
        Real.sqrt_eq_one, ge_iff_le, h, ↓reduceDIte, mem_ball, dist_zero_right, norm_mul,
        gt_iff_lt] at hx1 ⊢
      nth_rw 6 [← Real.sqrt_one]
      rw [Real.sqrt_lt_sqrt_iff (by positivity)]
      simp_rw [mul_pow, ← Finset.mul_sum, sq_abs, scalecoord, div_pow, mul_pow]
      norm_cast
      simp only [Nat.reducePow, Nat.cast_ofNat, NNReal.sq_sqrt, NNReal.coe_mul, NNReal.coe_ofNat,
        NNReal.coe_mk]
      have : ∑ x_1 : Fin n, x x_1.castSucc ^ 2 = 1 - (x (Fin.last n)) ^ 2 := by
        simp_rw [← hx1, Fin.sum_univ_castSucc, add_sub_assoc, sub_self, add_zero]
      rw [← this]
      have : ∑ x_1 : Fin n, x x_1.castSucc ^ 2 > 0 := by
        rw [this, gt_iff_lt, sub_pos]
        nth_rw 5 [← one_pow (n := 2)]
        rw [sq_lt_sq, abs_one]
        exact lt_of_not_ge h
      rw [div_mul_eq_mul_div₀, mul_div_mul_right _ _ this.ne.symm,
        div_lt_iff₀ (by norm_num), one_mul, (by norm_num : (4 : ℝ) = 2 ^ 2), sq_lt_sq]
      apply lt_of_le_of_lt (abs_add_le _ _)
      simp [← lt_tsub_iff_right, (by norm_num : (2 : ℝ) - 1 = 1), lt_of_not_ge h]
  map_target' := by
    intro y hy
    constructor
    · have h1 : 0 ≤ 1 - lastcoord y ^ 2 := by
        rw [sub_nonneg, (by norm_num : (1 : ℝ) = 1 ^ 2), sq_le_sq, abs_one]
        exact abs_lastcoord_le_one_of_ball y hy
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_castSucc, (Fin.castSucc_lt_last _).ne, mul_pow,
        ← Finset.mul_sum, sum_eq_lastcoord, div_pow]
      rw [Real.sq_sqrt h1, ← mul_div, mul_assoc]
      by_cases h : lastcoord y = - 1
      · simp [h]
      · have h2 : (lastcoord y + 1) ^ 2 ≠ 0 := by
          intro h'
          apply h
          rw [sq_eq_zero_iff] at h'
          exact eq_neg_of_add_eq_zero_left h'
        simp [h]
        rw [div_mul_div_cancel₀ h2, (by norm_num : (2 : ℝ) ^ 2 = 4),
          mul_div_cancel₀ _ (by norm_num), sub_add_cancel]
    · simp only [ne_eq, Set.mem_singleton_iff]
      intro h
      replace h := congrFun h (Fin.last n)
      have := lastcoord_lt_one_of_ball _ hy
      simp only [↓reduceDIte, ↓reduceIte] at h
      linarith
  left_inv' x hx := sorry
  right_inv' := sorry

lemma abs_le_of_norm_le {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) {r : NNReal} (h : ‖x‖ ≤ r)
    (i : Fin n) : |x i| ≤ r := by
  rw [← abs_norm] at h
  rw [← NNReal.abs_eq, ← sq_le_sq] at h ⊢
  simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (x := ∑ x_1 : Fin n, x x_1 ^ 2)
      (by apply Finset.sum_nonneg'; exact fun i ↦ sq_nonneg (x i))] at h
  calc
    x i ^ 2 ≤ ∑ x_1 : Fin n, x x_1 ^ 2 := by
      refine Finset.single_le_sum (f := fun j ↦ x j ^ 2) ?_ (Finset.mem_univ i)
      intro i _
      exact sq_nonneg (x i)
    _ ≤ r ^ 2 := h

#check Finset.sum_eq_zero_iff_of_nonneg

lemma eq_single_of_norm_eq_abs {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : Fin n)
    (hx : ‖x‖ = |x i|) (hxi : x i ≥ 0) : x = EuclideanSpace.single i |x i| := by
  rw [← abs_norm, ← sq_eq_sq_iff_abs_eq_abs, EuclideanSpace.norm_eq] at hx
  simp only [Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (x := ∑ x_1 : Fin n, x x_1 ^ 2)
      (by apply Finset.sum_nonneg'; exact fun i ↦ sq_nonneg (x i))] at hx
  have h' : ∑ x_1 ∈ (Finset.univ : Finset (Fin n)) \ {i}, x x_1 ^ 2 = 0 := by simp [hx]
  ext j
  by_cases hj : j = i
  · rw [hj]
    simp [abs_of_nonneg hxi]
  · simp only [EuclideanSpace.single_apply, hj, ↓reduceIte]
    rw [← sq_eq_zero_iff]
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).1 h' j (by simp [hj])
    intro i _
    exact sq_nonneg (x i)

lemma eq_single_of_norm_eq_abs' {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : Fin n)
    (hx : ‖x‖ = |x i|) (hxi : x i < 0) : x = EuclideanSpace.single i (-|x i|) := by
  rw [← abs_norm, ← sq_eq_sq_iff_abs_eq_abs, EuclideanSpace.norm_eq] at hx
  simp only [Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (x := ∑ x_1 : Fin n, x x_1 ^ 2)
      (by apply Finset.sum_nonneg'; exact fun i ↦ sq_nonneg (x i))] at hx
  have h' : ∑ x_1 ∈ (Finset.univ : Finset (Fin n)) \ {i}, x x_1 ^ 2 = 0 := by simp [hx]
  ext j
  by_cases hj : j = i
  · rw [hj]
    simp [abs_of_neg hxi]
  · simp only [EuclideanSpace.single_apply, hj, ↓reduceIte]
    rw [← sq_eq_zero_iff]
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).1 h' j (by simp [hj])
    intro i _
    exact sq_nonneg (x i)

lemma norm_eq_abs_iff_eq_single {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ‖x‖ = |x i| ↔ x = EuclideanSpace.single i |x i| ∨ x = EuclideanSpace.single i (-|x i|) := by
  constructor
  · intro h
    by_cases hxi : x i ≥ 0
    · left
      exact eq_single_of_norm_eq_abs x i h hxi
    · right
      exact eq_single_of_norm_eq_abs' x i h (lt_of_not_ge hxi)
  · intro h
    rcases h with h | h
    · rw [h]
      simp
    · rw [h]
      simp

open Metric in
def sphereToDisc' (n : ℕ) :
    PartialEquiv (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin n)) where
  toFun x i := if h : |x (Fin.last n)| ≥ 1 then 0
    else (scalecoord (x (Fin.last n)) h) * x i.castSucc
  invFun y i := if h : i = Fin.last n then lastcoord y
    else if lastcoord y = - 1 then 0
    else (2 * Real.sqrt (1 - (lastcoord y) ^ 2) / (lastcoord y + 1))
    * y ⟨i, Fin.lt_last_iff_ne_last.mpr h⟩
  source := sphere 0 1 \ {EuclideanSpace.single (Fin.last n) 1}
  target := ball 0 1
  map_source' := sorry
  map_target' := sorry
  left_inv' x  := by
    intro ⟨hx1, hx2⟩
    ext i
    by_cases h : |x (Fin.last n)| ≥ 1
    · simp [h]
      by_cases h' : i = Fin.last n
      · subst i
        simp only [↓reduceIte, lastcoord, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, NNReal.mk_zero, Finset.sum_const_zero, NNReal.sqrt_zero, NNReal.coe_zero,
        mul_zero, zero_sub]
        rw [ge_iff_le, le_abs] at h
        rcases h with h | h
        · simp [EuclideanSpace.norm_eq] at hx1
          exfalso
          apply hx2
          simp only [Set.mem_singleton_iff]
          have : 1 = |x (Fin.last n)| := by sorry
          rw [this]
          apply eq_single_of_norm_eq_abs
          · sorry
          · sorry
        · sorry
      · simp [h']
        sorry
    · sorry
  right_inv' := sorry
