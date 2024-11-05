import CWcomplexes.Finite
import Mathlib.Analysis.NormedSpace.Real

/-!
# Constructions with CW-complexes

In this file we show that some basic constructions preserve CW-complexes:
* `CWComplex_level`: The levels of a CW-complex are again CW-complexes.
* `CWComplex_disjointUnion`: The disjoint union of two CW-complexes is again a CW-complex.
* `CWComplex_of_Homeomorph`: The image of a CW-complex under a homeomorphism is again a CW-complex.
-/

noncomputable section

open Metric Set

namespace CWComplex

variable {X : Type*} [t : TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]

section

/-- `levelaux n` is a CW-complex for every `n : ℕ∞`.-/
instance CWComplex_levelaux (n : ℕ∞) : CWComplex (levelaux C n) where
  cell l := {x : cell C l // l < n}
  map l i := map (C := C) l i
  source_eq l i:= source_eq (C := C) l i
  cont l i := cont (C := C) l i
  cont_symm l i := cont_symm (C := C) l i
  pairwiseDisjoint' := by
    simp_rw [PairwiseDisjoint, Set.Pairwise, Function.onFun, disjoint_iff_inter_eq_empty]
    intro ⟨a, ja, _⟩ _ ⟨b, jb, map_mk⟩ _ ne
    exact disjoint_openCell_of_ne (by aesop)
  mapsto := by
    intro l ⟨i, lltn⟩
    obtain ⟨I, hI⟩ := cellFrontier_subset_finite_closedCell (C := C) l i
    use fun (m : ℕ) ↦ (I m).subtype (fun _ ↦ m < n)
    simp_rw [mapsTo', iUnion_subtype]
    apply subset_trans hI (iUnion_mono fun m ↦ iUnion_mono fun mltl ↦ iUnion_mono fun j ↦ ?_ )
    simp_all only [(Nat.cast_lt.2 mltl).trans lltn, Finset.mem_subtype, iUnion_true,
      iUnion_subset_iff]
    exact fun _ ↦ by rfl
  closed' A asublevel := by
    have : A ⊆ C := by
      apply asublevel.trans
      simp_rw [← levelaux_top]
      exact levelaux_mono le_top
    refine ⟨fun _ _ _ ↦ by simp only [(closed' A this).1], ?_⟩
    -- This follows from `isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell`
    -- and `levelaux_inter_openCell_eq_empty`.
    intro h
    simp_rw [Subtype.forall] at h
    apply isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell this
    intro m _ j
    by_cases mlt : m < n
    · exact Or.intro_right _ (h m j mlt)
    left
    push_neg at mlt
    rw [← inter_eq_left.2 asublevel, inter_assoc, levelaux_inter_openCell_eq_empty mlt, inter_empty]
    exact isClosed_empty
  union' := by
    apply iUnion_congr fun m ↦ ?_
    rw [iUnion_subtype, iUnion_comm]
    rfl

/-- `level n` is a CW-complex for every `n : ℕ∞`.-/
instance CWComplex_level (n : ℕ∞) : CWComplex (level C n) := CWComplex_levelaux _ _

variable {D : Set X} [CWComplex D]

/-- The union of two disjoint CW-complexes is again a CW-complex.-/
def CWComplex_disjointUnion (disjoint : Disjoint C D) : CWComplex (C ∪ D) where
  cell n := Sum (cell C n) (cell D n)
  map n := Sum.elim (map (C := C) n) (map (C := D) n)
  source_eq n i := match i with
    | Sum.inl x => source_eq n x
    | Sum.inr x => source_eq n x
  cont n i := match i with
    | Sum.inl x => cont n x
    | Sum.inr x => cont n x
  cont_symm n i := match i with
    | Sum.inl x => cont_symm n x
    | Sum.inr x => cont_symm n x
  pairwiseDisjoint' := by
    simp_rw [PairwiseDisjoint, Set.Pairwise, Function.onFun, disjoint_iff_inter_eq_empty]
    intro ⟨n, cn⟩ _ ⟨m, cm⟩ _ ne
    rcases cn with cn | cn
    rcases cm with cm | cm
    · exact disjoint_openCell_of_ne (by aesop)
    · exact subset_eq_empty (inter_subset_inter (openCell_subset_complex n cn)
        (openCell_subset_complex m cm)) (disjoint_iff_inter_eq_empty.1 disjoint)
    rcases cm with cm | cm
    · exact subset_eq_empty (inter_subset_inter (openCell_subset_complex n cn)
        (openCell_subset_complex m cm)) (disjoint_iff_inter_eq_empty.1 (disjoint_comm.1 disjoint))
    · exact disjoint_openCell_of_ne (by aesop)
  mapsto n i := by
    classical
    rcases i with ic | id
    · obtain ⟨I, hI⟩ := cellFrontier_subset_finite_closedCell n ic
      use fun m ↦ (I m).image Sum.inl
      rw [mapsTo']
      apply hI.trans
      simp only [Finset.mem_image, iUnion_exists, biUnion_and', iUnion_iUnion_eq_right]
      rfl
    · obtain ⟨I, hI⟩ := cellFrontier_subset_finite_closedCell n id
      use fun m ↦ (I m).image Sum.inr
      rw [mapsTo']
      apply hI.trans
      simp only [Finset.mem_image, iUnion_exists, biUnion_and', iUnion_iUnion_eq_right]
      rfl
  closed' A asubcd := by
    constructor
    · intro closedA n j
      rcases j with j | j
      · exact closedA.inter isClosed_closedCell
      · exact closedA.inter isClosed_closedCell
    · intro h
      -- We show closedness separately for `A ∩ C` and `A ∩ D` which then follow from
      -- the property `closed'` of `C` and `D`.
      suffices IsClosed ((A ∩ C) ∪ (A ∩ D)) by
        convert this using 1
        simp only [union_inter_distrib_left, union_eq_right.2 inter_subset_left,
          inter_union_distrib_right, left_eq_inter, subset_inter_iff, subset_union_left, asubcd,
          and_self]
      apply IsClosed.union
      · rw [closed (A ∩ C) inter_subset_right]
        intro n j
        rw [inter_right_comm]
        exact (h n (Sum.inl j)).inter isClosed
      · rw [closed (A ∩ D) inter_subset_right]
        intro n j
        rw [inter_right_comm]
        exact (h n (Sum.inr j)).inter isClosed
  union' := by
    simp_rw [← union (C := C), ← union (C := D), ← iUnion_union_distrib, iUnion_sum]
    rfl

end

-- assume that C and D are closed and only require the homeomorphism on C and D

/-- The image of a CW-complex under a homeomorphisms is again a CW-complex.-/
def CWComplex_of_Homeomorph.{u} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (C : Set X) (D : Set Y) [CWComplex C] (f : X ≃ₜ Y) (imf : f '' C = D) :
    CWComplex D where
  cell := cell C
  map n i := (map (C := C) n i).transEquiv f
  source_eq n i := by simp [PartialEquiv.transEquiv, source_eq (C := C) n i]
  cont n i := by simp [PartialEquiv.transEquiv_eq_trans, cont (C := C) n i]
  cont_symm n i := by
    simp only [PartialEquiv.transEquiv_eq_trans, PartialEquiv.trans_target,
      Equiv.toPartialEquiv_symm_apply, ← image_equiv_eq_preimage_symm]
    refine ContinuousOn.image_comp_continuous (f := f.invFun) ?_ f.continuous_invFun
    simp [Equiv.invFun_as_coe, Homeomorph.coe_symm_toEquiv, Set.image_image, cont_symm (C := C)]
  pairwiseDisjoint' := by
    have := pairwiseDisjoint' (C := C)
    simp only [PairwiseDisjoint, Set.Pairwise, mem_univ, ne_eq, Function.onFun,
      PartialEquiv.transEquiv_apply, EquivLike.coe_coe, ← image_image] at this ⊢
    intro ⟨n, j⟩ _ ⟨m, i⟩ _ ne
    exact disjoint_image_of_injective f.injective
      (this (x := ⟨n, j⟩) trivial (y := ⟨m, i⟩) trivial ne)
  mapsto n i := by
    obtain ⟨I, hI⟩ := mapsto (C := C) n i
    use I
    rw [mapsTo'] at hI ⊢
    simp only [PartialEquiv.transEquiv_apply, EquivLike.coe_coe, ← image_image, ←
      image_iUnion (f := f)]
    exact image_mono hI
  closed' A AsubD := by
    have preAsubC : f ⁻¹' A ⊆ C := by
      simp only [← Homeomorph.image_symm, image_subset_iff, Homeomorph.symm_symm, imf, AsubD]
    calc
      IsClosed A
      _ ↔ IsClosed (f ⁻¹' A) := f.isClosed_preimage.symm
      _ ↔ ∀ n (j : cell C n), IsClosed ((f ⁻¹' A) ∩ map n j '' closedBall 0 1) := by
        rw [closed' (C := C) (f ⁻¹' A) preAsubC]
      _ ↔ ∀ n (j : cell C n),
          IsClosed (A ∩ ((map n j).transEquiv ↑f) '' closedBall 0 1) := by
        apply forall_congr' fun n ↦ forall_congr' fun j ↦ ?_
        simp only [PartialEquiv.transEquiv_apply, EquivLike.coe_coe, ← image_image]
        nth_rw 2 [← f.image_preimage A]
        simp only [← image_inter f.injective]
        exact f.isClosed_image.symm
  union' := by simp [← image_image, ← image_iUnion (f := f), union' (C := C), imf]
