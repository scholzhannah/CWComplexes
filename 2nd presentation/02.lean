import CWcomplexes.kification

noncomputable section

namespace Kification

lemma continuous_compact_to_kification' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] (f : X → Y) (cont : Continuous f) : Continuous (tokification Y ∘ f) := by
  simp_rw [continuous_iff_isClosed]
  intro s closeds
  simp_rw [kification.closed_iff, kification] at closeds
  rcases closeds ⟨Set.range f, isCompact_range cont⟩ with ⟨u, hu⟩
  simp only at hu
  rw [Set.preimage_comp, tokification, Equiv.coe_fn_mk, Set.preimage_id']
  suffices IsClosed (f ⁻¹' (s ∩ Set.range f)) by
    simpa only [Set.preimage_inter, Set.preimage_range, Set.inter_univ]
  rw [hu, Set.preimage_inter, Set.preimage_range, Set.inter_univ]
  exact IsClosed.preimage cont u.2
