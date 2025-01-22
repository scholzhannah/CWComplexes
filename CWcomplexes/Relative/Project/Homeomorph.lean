import CWcomplexes.Relative.RelFinite
import Mathlib.Analysis.NormedSpace.Real
import CWcomplexes.Auxiliary
import Mathlib.Data.ENat.Basic

noncomputable section

open Metric Set

variable {X : Type*} [t : TopologicalSpace X] [T2Space X] {C D : Set X}

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

lemma PartialEquiv.isClosed_of_isClosed_preimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : PartialEquiv X Y) (h1 : ContinuousOn e e.source)
    (h2 : ContinuousOn e.symm e.target)
    (he1 : IsClosed e.target) (he2 : IsClosed e.source)
    (A : Set Y) (hAe : A ⊆ e.target) (hA : IsClosed (e.source ∩ e ⁻¹' A)) : IsClosed A := by
  rw [← inter_eq_right.2 hAe]
  apply isClosed_inter_of_isClosed_subtype_val he1
  let g : e.source ≃ₜ e.target := e.toHomeomorph h1 h2
  rw [← g.isClosed_preimage]
  have : ⇑g ⁻¹' (Subtype.val ⁻¹' A) = e.source ∩ ↑e ⁻¹' A := by
    ext x
    simp [mem_image, mem_preimage, PartialEquiv.toHomeomorph_apply, Subtype.exists,
      exists_and_right, exists_eq_right, mem_inter_iff, g, PartialEquiv.toEquiv, and_comm]
  rw [Topology.IsClosedEmbedding.isClosed_iff_image_isClosed he2.isClosedEmbedding_subtypeVal, this]
  exact hA

def RelCWComplex.ofPartialEquiv.{u} {X Y : Type u} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y} [RelCWComplex C D]
    (hC : IsClosed C) (hE : IsClosed E)
    (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E) (hDF : f '' D = F)
    (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E)  :
    RelCWComplex E F where
  cell := cell C
  map n i := (map n i).trans' (f.restr (map n i).target) (by
    simp only [← PartialEquiv.image_source_eq_target, PartialEquiv.restr_source, right_eq_inter,
    source_eq n i, hfC1]
    exact openCell_subset_complex n i)
  source_eq n i := by simp [source_eq n i]
  continuousOn n i := by
    simp only [PartialEquiv.trans', PartialEquiv.restr_coe, PartialEquiv.restr_coe_symm,
      PartialEquiv.restr_target]
    apply hfC2.comp (continuousOn n i)
    rw [mapsTo']
    exact closedCell_subset_complex n i
  continuousOn_symm n i := by
    simp only [PartialEquiv.trans', PartialEquiv.restr_coe, PartialEquiv.restr_coe_symm,
      PartialEquiv.restr_target, PartialEquiv.coe_symm_mk]
    apply (continuousOn_symm n i).comp
    · apply hfE2.mono
      simp [hfE1]
    · simp [mapsTo']
  pairwiseDisjoint' := by
    have := pairwiseDisjoint' (C := C)
    simp only [PairwiseDisjoint, Set.Pairwise, mem_univ, ne_eq, Function.onFun, forall_const,
      PartialEquiv.trans'_apply, PartialEquiv.restr_coe, Function.comp_apply] at this ⊢
    intro x y hxy
    simp_rw [← image_image]
    apply (this hxy).image (u := C)
    · rw [← hfC1]
      exact f.injOn
    · exact openCell_subset_complex _ _
    · exact openCell_subset_complex _ _
  disjointBase' n i := by
    simp only [PartialEquiv.trans'_apply, PartialEquiv.restr_coe, Function.comp_apply]
    simp_rw [← image_image, ← hDF]
    apply (disjointBase' n i).image (u := C)
    · rw [← hfC1]
      exact f.injOn
    · exact openCell_subset_complex _ _
    · exact base_subset_complex
  mapsto n i := by
    obtain ⟨I, hI⟩ := mapsto n i
    use I
    rw [mapsTo'] at hI ⊢
    simp only [PartialEquiv.trans'_apply, PartialEquiv.restr_coe, Function.comp_apply,
      ← image_image, ← image_iUnion (f := f), ← hDF, ← image_union]
    apply image_mono
    exact hI
  closed' A hA := by
    intro ⟨hA1, hA2⟩
    apply f.isClosed_of_isClosed_preimage (hfC1 ▸ hfC2) (hfE1 ▸ hfE2) (hfE1 ▸ hE) (hfC1 ▸ hC)
    · exact hfE1 ▸ hA
    rw [closed (C := C) _ (hfC1 ▸ inter_subset_left)]
    constructor
    · intro n i
      specialize hA1 n i
      simp only [PartialEquiv.trans'_apply, PartialEquiv.restr_coe, Function.comp_apply,
        ← image_image] at hA1
      rw [hfC1, inter_assoc, inter_comm, inter_assoc]
      have : closedCell n i ∩ C = f ⁻¹' (f '' closedCell n i) ∩ C := by
        simp_rw [← hfC1]
        rw [inter_comm, inter_comm _ f.source]
        symm
        apply PartialEquiv.IsImage.preimage_eq
        apply PartialEquiv.IsImage.of_image_eq
        rw [hfC1, inter_eq_right.2 (closedCell_subset_complex n i), hfE1, ← hfE1,
          ← f.image_source_eq_target, hfC1, ← f.injOn.image_inter (by rw [hfC1])
          (by rw [hfC1]; exact closedCell_subset_complex n i),
          inter_eq_right.2 (closedCell_subset_complex n i)]
      rw [this, ← inter_assoc, ← preimage_inter, inter_comm]
      exact hfC2.preimage_isClosed_of_isClosed hC hA1
    · rw [hfC1, inter_assoc, inter_comm, inter_assoc]
      have : D ∩ C = f ⁻¹' F ∩ C := by
        rw [← hfC1, inter_comm, inter_comm (↑f ⁻¹' F)]
        symm
        apply PartialEquiv.IsImage.preimage_eq
        apply PartialEquiv.IsImage.of_image_eq
        rw [hfC1, inter_eq_right.2 base_subset_complex, hfE1, ← hDF, ← hfE1,
          ← f.image_source_eq_target, hfC1, ← f.injOn.image_inter (by rw [hfC1])
          (by rw [hfC1]; exact base_subset_complex), inter_eq_right.2 base_subset_complex]
      rw [this, ← inter_assoc, ← preimage_inter, inter_comm]
      exact hfC2.preimage_isClosed_of_isClosed hC hA2
  isClosedBase := by
    rw [← hDF]
    apply f.isClosed_of_isClosed_preimage (hfC1 ▸ hfC2) (hfE1 ▸ hfE2) (hfE1 ▸ hE) (hfC1 ▸ hC)
    · rw [← PartialEquiv.image_source_eq_target]
      apply image_mono
      rw [hfC1]
      exact base_subset_complex
    rw [hfC1]
    have : C ∩ ↑f ⁻¹' (↑f '' D) = C ∩ D := by
      rw [← hfC1, hDF]
      apply PartialEquiv.IsImage.preimage_eq
      apply PartialEquiv.IsImage.of_image_eq
      rw [hfC1, inter_eq_right.2 base_subset_complex, hfE1, ← hDF, ← hfE1,
        ← f.image_source_eq_target, hfC1, ← f.injOn.image_inter (by rw [hfC1])
        (by rw [hfC1]; exact base_subset_complex), inter_eq_right.2 base_subset_complex]
    rw [this, inter_eq_right.2 base_subset_complex]
    exact isClosedBase C
  union' := by
    simp only [PartialEquiv.trans'_apply, PartialEquiv.restr_coe, Function.comp_apply,
      ← image_image, ← image_iUnion (f := f), ← hDF, ← image_union, ← hfE1,
      ← f.image_source_eq_target, hfC1, union']

lemma RelCWComplex.FiniteDimensional_ofPartialEquiv.{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y}
    [RelCWComplex C D] [FiniteDimensional C] (hC : IsClosed C) (hE : IsClosed E)
    (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E) (hDF : f '' D = F)
    (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E) :
    letI := ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
    FiniteDimensional E :=
  let _ := ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
  {eventually_isEmpty_cell := FiniteDimensional.eventually_isEmpty_cell (C := C)}

lemma RelCWComplex.FiniteType_ofPartialEquiv.{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y}
    [RelCWComplex C D] [FiniteType C] (hC : IsClosed C) (hE : IsClosed E)
    (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E) (hDF : f '' D = F)
    (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E) :
    letI := ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
    FiniteType E :=
  let _ := ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
  {finite_cell := FiniteType.finite_cell (C := C)}

lemma RelCWComplex.Finite_ofPartialEquiv.{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y}
    [RelCWComplex C D] [Finite C] (hC : IsClosed C) (hE : IsClosed E)
    (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E) (hDF : f '' D = F)
    (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E) :
    letI := ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
    Finite E :=
  let _ := ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
  let _ := FiniteDimensional_ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
  let _ := FiniteType_ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
  inferInstance

def ClasCWComplex.ofPartialEquiv.{u} {X Y : Type u} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] (C : Set X) (E : Set Y) [ClasCWComplex C] (hC : IsClosed C)
    (hE : IsClosed E) (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E)
    (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E)  :
    ClasCWComplex E :=
  RelCWComplex.ofPartialEquiv C E hC hE f hfC1 hfE1 (image_empty f)  hfC2 hfE2

lemma ClasCWComplex.FiniteDimensional_ofPartialEquiv .{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) (E : Set Y) [ClasCWComplex C] [FiniteDimensional C]
    (hC : IsClosed C) (hE : IsClosed E) (f : PartialEquiv X Y) (hfC1 : f.source = C)
    (hfE1 : f.target = E) (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E)  :
    letI := ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
    FiniteDimensional E :=
  let _ := ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
  { eventually_isEmpty_cell := FiniteDimensional.eventually_isEmpty_cell (C := C) }

lemma ClasCWComplex.FiniteType_ofPartialEquiv .{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) (E : Set Y) [ClasCWComplex C] [FiniteType C]
    (hC : IsClosed C) (hE : IsClosed E) (f : PartialEquiv X Y) (hfC1 : f.source = C)
    (hfE1 : f.target = E) (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E)  :
    letI := ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
    FiniteType E :=
  let _ := ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
  { finite_cell := FiniteType.finite_cell (C := C) }

lemma ClasCWComplex.Finite_ofPartialEquiv .{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) (E : Set Y) [ClasCWComplex C] [Finite C]
    (hC : IsClosed C) (hE : IsClosed E) (f : PartialEquiv X Y) (hfC1 : f.source = C)
    (hfE1 : f.target = E) (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E)  :
    letI := ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
    Finite E :=
  let _ := ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
  let _ := FiniteDimensional_ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
  let _ := FiniteType_ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
  inferInstance
