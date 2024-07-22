import CWcomplexes.kification

noncomputable section

namespace Kification

lemma kification_eq_self_of_WeaklyLocallyCompactSpace' {X : Type*} [t : TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] : instkification = t := by
  apply le_antisymm
  · exact kification_le
  intro A hA
  simp only [IsOpen, instkification, TopologicalSpace.Compacts.carrier_eq_coe,
    TopologicalSpace.Opens.carrier_eq_coe] at hA
  simp_rw [kification, isOpen_iff_mem_nhds]
  intro x xmemA
  rcases WeaklyLocallyCompactSpace.exists_compact_mem_nhds x with ⟨C, compact, Cnhds⟩
  simp_rw [mem_nhds_iff, kification] at Cnhds ⊢
  rcases Cnhds with ⟨U, Usub, openU, xmemU⟩
  use A ∩ U
  refine ⟨Set.inter_subset_left, ?_, ⟨xmemA, xmemU⟩⟩
  rcases hA ⟨C, compact⟩ with ⟨⟨V, openV⟩, hV⟩
  simp only [TopologicalSpace.Compacts.coe_mk, TopologicalSpace.Opens.coe_mk] at hV
  rw [← Set.inter_eq_right.2 Usub, ← Set.inter_assoc, hV,
    Set.inter_assoc, Set.inter_eq_right.2 Usub]
  exact IsOpen.inter openV openU
