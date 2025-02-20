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

--**mathlib**
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
lemma IsOpen.preimage_val {X : Type*} [TopologicalSpace X] {s t : Set X}
    (ht : IsOpen t) : IsOpen (s ↓∩ t) := isOpen_induced ht

-- **PR**
--kspace file
lemma IsClosed.preimage_val {X : Type*} [TopologicalSpace X] {s t : Set X}
    (ht : IsClosed t) : IsClosed (s ↓∩ t) := by
  rw [← isOpen_compl_iff] at ht ⊢
  exact IsOpen.preimage_val ht

--**PR**
lemma IsOpen.inter_preimage_val_iff {X : Type*} [TopologicalSpace X] {s t : Set X} (hs : IsOpen s) :
    IsOpen (s ↓∩ t) ↔ IsOpen (s ∩ t) :=
  ⟨fun h ↦ by simpa using hs.isOpenMap_subtype_val _ h,
    fun h ↦ (Subtype.preimage_coe_self_inter _ _).symm ▸ h.preimage_val⟩

--**PR**
lemma IsClosed.inter_preimage_val_iff {X : Type*} [TopologicalSpace X]  {s t : Set X}
    (hs : IsClosed s) : IsClosed (s ↓∩ t) ↔ IsClosed (s ∩ t) :=
  ⟨fun h ↦ by simpa using hs.isClosedMap_subtype_val _ h,
    fun h ↦ (Subtype.preimage_coe_self_inter _ _).symm ▸ h.preimage_val⟩

/-- A partial bijection that is continuous on the source and the target restricts to a
  homeomorphism.-/
@[simps]
def PartialEquiv.toHomeomorph {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (e : PartialEquiv α β) (he1 : ContinuousOn e e.source)
    (he2 : ContinuousOn e.symm e.target) : e.source ≃ₜ e.target where
  toFun := e.toEquiv
  invFun := e.toEquiv.symm
  left_inv x := by simp
  right_inv y := by simp
  continuous_toFun := by
    simp only [PartialEquiv.toEquiv, Equiv.coe_fn_mk]
    apply Continuous.subtype_mk
    have : (fun (x : e.source) ↦ e ↑x) = e.source.restrict e := by
      ext
      simp
    rw [this, ← continuousOn_iff_continuous_restrict]
    exact he1
  continuous_invFun := by
    simp only [PartialEquiv.toEquiv, Equiv.coe_fn_mk]
    apply Continuous.subtype_mk
    have : (fun (x : e.target) ↦ e.symm ↑x) = e.target.restrict e.symm := by
      ext
      simp
    rw [this, ← continuousOn_iff_continuous_restrict]
    exact he2

open Set in
/-- A partial bijection that is continuous on both source and target and where the source and
  the target are closed is a closed map when restricting to the source. -/
lemma PartialEquiv.isClosed_of_isClosed_preimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : PartialEquiv X Y) (h1 : ContinuousOn e e.source)
    (h2 : ContinuousOn e.symm e.target)
    (he1 : IsClosed e.target) (he2 : IsClosed e.source)
    (A : Set Y) (hAe : A ⊆ e.target) (hA : IsClosed (e.source ∩ e ⁻¹' A)) : IsClosed A := by
  rw [← inter_eq_right.2 hAe]
  rw [← he1.inter_preimage_val_iff]
  let g : e.source ≃ₜ e.target := e.toHomeomorph h1 h2
  rw [← g.isClosed_preimage]
  have : ⇑g ⁻¹' (Subtype.val ⁻¹' A) = e.source ∩ ↑e ⁻¹' A := by
    ext x
    simp [mem_image, mem_preimage, PartialEquiv.toHomeomorph_apply, Subtype.exists,
      exists_and_right, exists_eq_right, mem_inter_iff, g, PartialEquiv.toEquiv, and_comm]
  rw [Topology.IsClosedEmbedding.isClosed_iff_image_isClosed he2.isClosedEmbedding_subtypeVal, this]
  exact hA


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
