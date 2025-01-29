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

-- write an equivalence version

-- used in constructions
lemma isClosed_left_of_isClosed_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : SeparatedNhds A B) (hAB' : IsClosed (A ∪ B)) : IsClosed A := by
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := hAB
  rw [← isOpen_compl_iff] at hAB' ⊢
  suffices Aᶜ = (A ∪ B)ᶜ ∪ V from this ▸ hAB'.union hV
  have : B ∩ Vᶜ = ∅ := by aesop
  rw [← compl_inj_iff, Set.compl_union, compl_compl, compl_compl, Set.union_inter_distrib_right,
    this, Set.union_empty, Set.left_eq_inter, Set.subset_compl_comm]
  exact (hUV.mono_left hAU).subset_compl_left

-- used in constructions
lemma isClosed_right_of_isClosed_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : SeparatedNhds A B) (closedAB : IsClosed (A ∪ B)) : IsClosed B :=
  isClosed_left_of_isClosed_union hAB.symm (Set.union_comm _ _ ▸ closedAB)

-- completeness
lemma isClosed_union_iff_isClosed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : SeparatedNhds A B) : IsClosed (A ∪ B) ↔ IsClosed A ∧ IsClosed B :=
  ⟨fun h ↦ ⟨isClosed_left_of_isClosed_union hAB h, isClosed_right_of_isClosed_union hAB h⟩,
    fun ⟨h1, h2⟩ ↦ h1.union h2⟩

/-! ### ↓∩-/

open Set.Notation

--**PR**
-- this file
lemma IsOpen.subtype_val {X : Type*} [TopologicalSpace X] {s t : Set X}
    (ht : IsOpen t) : IsOpen (s ↓∩ t) := isOpen_induced ht

-- **PR**
--kspace file
lemma IsClosed.subtype_val {X : Type*} [TopologicalSpace X] {s t : Set X}
    (ht : IsClosed t) : IsClosed (s ↓∩ t) := by
  rw [← isOpen_compl_iff] at ht ⊢
  exact IsOpen.subtype_val ht

-- **PR**
--for completeness
lemma isOpen_inter_of_isOpen_subtype_val {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : IsOpen s) (hst : IsOpen (s ↓∩ t)) : IsOpen (s ∩ t) := by
  rw [isOpen_induced_iff] at hst
  obtain ⟨u, hu, hust⟩ := hst
  rw [Subtype.preimage_val_eq_preimage_val_iff] at hust
  rw [← hust]
  exact hs.inter hu

-- **PR**
--needed in constructions file and Homeomorph file
lemma isClosed_inter_of_isClosed_subtype_val {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : IsClosed s) (hst : IsClosed (s ↓∩ t)) : IsClosed (s ∩ t) := by
  rw [isClosed_induced_iff] at hst
  obtain ⟨u, hu, hust⟩ := hst
  rw [Subtype.preimage_val_eq_preimage_val_iff] at hust
  rw [← hust]
  exact hs.inter hu

/-! ### Random-/

example {α : Sort*} [Finite α] : Finite (PLift α) := by exact instFinitePLift


-- **mathlib**
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

-- needed in examples file
-- should rewrite this as a being in the image
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
