import CWcomplexes.Definition
import Mathlib.Analysis.NormedSpace.Real

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open Metric Set

namespace CWComplex

variable {X : Type*} [t : TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]

section

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
    obtain ⟨I, hI⟩ := cellFrontier_subset (C := C) l i
    use fun (m : ℕ) ↦ (I m).subtype (fun j ↦ m < n)
    simp_rw [mapsTo', iUnion_subtype]
    apply subset_trans hI (iUnion_mono fun m ↦ iUnion_mono fun mltl ↦ iUnion_mono fun j ↦ ?_ )
    simp_all only [(ENat.coe_lt_of_lt mltl).trans lltn, Finset.mem_subtype, iUnion_true,
      iUnion_subset_iff]
    exact fun _ ↦ by rfl
  closed' A asublevel := by
    have : A ⊆ C := by
      apply asublevel.trans
      simp_rw [← levelaux_top]
      exact levelaux_mono le_top
    refine ⟨fun _ _ _ ↦ by simp only [(closed' A this).1], ?_⟩
    intro h
    simp_rw [Subtype.forall] at h
    apply strong_induction_isClosed this
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

instance CWComplex_level (n : ℕ∞) : CWComplex (level C n) := CWComplex_levelaux _ _

variable {D : Set X} [CWComplex D]

instance CWComplex_disjointUnion (disjoint : Disjoint C D) : CWComplex (C ∪ D) where
  cell n := Sum (cell C n) (cell D n)
  map n := Sum.elim (map (C := C) n) (map (C := D) n)
  source_eq n i := match i with
    | Sum.inl x => source_eq n x
    | Sum.inr x => source_eq n x
  cont n i := match i with -- should something like this be a lemma?
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
    · obtain ⟨I, hI⟩ := cellFrontier_subset n ic
      use fun m ↦ (I m).image Sum.inl
      rw [mapsTo']
      apply hI.trans
      simp only [Finset.mem_image, iUnion_exists, biUnion_and', iUnion_iUnion_eq_right]
      rfl
    · obtain ⟨I, hI⟩ := cellFrontier_subset n id
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
