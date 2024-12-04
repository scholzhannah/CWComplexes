import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Fintype.Lattice

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

--needed in product file
lemma Set.subset_product {α β : Type*} {s : Set (α × β)} :
    s ⊆ (Prod.fst '' s) ×ˢ (Prod.snd '' s) :=
  fun _ hp ↦ mem_prod.2 ⟨mem_image_of_mem _ hp, mem_image_of_mem _ hp⟩

/-! ### Different maps -/

-- needed in this file and in examples file
/-- `Function.const` as a `PartialEquiv`.
  It consists of two constant maps in opposite directions. -/
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

-- needed in examples file
lemma affineHomeomorph_trans {𝕜 : Type*} [Field 𝕜] [NoZeroDivisors 𝕜] [TopologicalSpace 𝕜]
    [TopologicalRing 𝕜] (a b c d : 𝕜) (h1 : a ≠ 0) (h2 : c ≠ 0) :
    (affineHomeomorph a b h1).trans (affineHomeomorph c d h2) =
    affineHomeomorph (c * a) (c * b + d) (mul_ne_zero h2 h1)  := by
  ext
  simp_rw [Homeomorph.trans_apply, affineHomeomorph_apply]
  ring

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

instance {α β : Sort*} [Finite α] [Finite β] : Finite (α ⊕' β) := by
  sorry

-- not needed anymore but probably still good to contribute?
@[elab_as_elim]
theorem ENat.nat_strong_induction {P : ℕ∞ → Prop} (a : ℕ∞) (h0 : P 0)
    (hsuc : ∀ n : ℕ, (∀ m (_ : m ≤ n), P m) → P n.succ)
    (htop : (∀ n : ℕ, P n) → P ⊤) : P a := by
  have A : ∀ n : ℕ, P n := fun n => Nat.caseStrongRecOn n h0 hsuc
  cases a
  · exact htop A
  · exact A _
