import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Sets.Compacts

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

-- I feel like this proof should be wayyy shorter. Correct usage of protected?
lemma aux1 (l : ℕ) {X : Type*} {s : ℕ →  Type*} (Y : (m : ℕ) → s m → Set X):
    ⋃ m, ⋃ (_ : m < Nat.succ l), ⋃ j, Y m j = (⋃ (j : s l), Y l j) ∪ ⋃ m, ⋃ (_ : m < l), ⋃ j, Y m j := by
  ext x
  simp only [Set.mem_iUnion, exists_prop, Set.mem_union]
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

lemma ENat.coe_lt_top {n : ℕ} : ↑n < (⊤ : ℕ∞) := Ne.lt_top (ENat.coe_ne_top n)

lemma isClosed_inter_singleton {X : Type*} [TopologicalSpace X] [T1Space X] {A : Set X} {a : X} : IsClosed (A ∩ {a}) := by
  by_cases h : a ∈ A
  · have : A ∩ {a} = {a} := by simp only [Set.inter_eq_right, Set.singleton_subset_iff, h]
    rw [this]
    exact isClosed_singleton
  · have : A ∩ {a} = ∅ := by simp only [Set.inter_singleton_eq_empty, h, not_false_eq_true]
    rw [this]
    exact isClosed_empty

lemma sphere_zero_dim_empty {X : Type*} {h : PseudoMetricSpace (Fin 0 → X)}: (Metric.sphere ![] 1 : Set (Fin 0 → X)) = ∅ := by
  simp [Metric.sphere, Matrix.empty_eq]


def kification (X : Type*) := X

instance instkification {X : Type*} [t : TopologicalSpace X] : TopologicalSpace (kification X) where
  IsOpen A := ∀ (B : t.Compacts), ∃ (C: t.Opens), A ∩ B.1 = C.1 ∩ B.1
  isOpen_univ := fun B ↦ (by use ⟨Set.univ, isOpen_univ⟩)
  isOpen_inter := by
    intro A1 A2 h1 h2 B
    rcases h1 B with ⟨C1, g1⟩
    rcases h2 B with ⟨C2, g2⟩
    use ⟨C1.1 ∩ C2.1, IsOpen.inter C1.2 C2.2⟩
    simp
    calc
      A1 ∩ A2 ∩ B.1 = (A1 ∩ B.1) ∩ (A2 ∩ B.1) := by simp [Set.inter_assoc, Set.inter_comm]
      _ = (C1.1 ∩ B.1) ∩ (C2.1 ∩ B.1) := by rw [g1, g2]
      _ = C1.1 ∩ C2.1 ∩ B.1 := by simp [← Set.inter_assoc, Set.inter_comm]
  isOpen_sUnion := by
    intro s h B
    simp at h
    let f := fun (t1 : s) ↦ Classical.choose (h t1 (by simp only [Subtype.coe_prop]) B)
    use ⟨⋃ (t : s), (f t).1 , isOpen_iUnion (fun t ↦ (f t).2)⟩
    simp_rw [Set.sUnion_eq_iUnion, Set.iUnion_inter]
    apply Set.iUnion_congr
    intro i
    simp [f]
    exact Classical.choose_spec (h i (by simp only [Subtype.coe_prop]) B)

def tokification (X : Type*) : X ≃ kification X := ⟨fun x ↦ x, fun x ↦ x, fun _ ↦ rfl, fun _ ↦ rfl⟩

def fromkification (X : Type*) : kification X ≃ X := ⟨fun x ↦ x, fun x ↦ x, fun _ ↦ rfl, fun _ ↦ rfl⟩

lemma continuous_fromkification {X : Type*} [t : TopologicalSpace X] : Continuous (fromkification X) where
isOpen_preimage A hA := by
  unfold fromkification
  simp only [instkification, Equiv.coe_fn_mk, Set.preimage_id', IsOpen]
  intro B
  use ⟨A, hA⟩

lemma isopenmap_tokification {X : Type*} [t: TopologicalSpace X] : IsOpenMap (tokification X) := by
  unfold IsOpenMap tokification
  intro A hA
  simp [instkification, IsOpen]
  intro B
  use ⟨A, hA⟩
  simp only [TopologicalSpace.Opens.coe_mk]
