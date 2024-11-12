import CWcomplexes.Relative.RelFinite
import Mathlib.Analysis.NormedSpace.Real
import CWcomplexes.Auxiliary

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

variable {X : Type*} [t : TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]

section


/-- `levelaux n` is a CW-complex for every `n : ℕ∞`.-/
instance RelCWComplex_levelaux (n : ℕ∞) : RelCWComplex (levelaux C D n) D where
  cell l := {x : cell C D l // l < n}
  map l i := map (C := C) (D := D) l i
  source_eq l i:= source_eq (C := C) (D := D) l i
  cont l i := cont (C := C) (D := D) l i
  cont_symm l i := cont_symm (C := C) (D := D) l i
  pairwiseDisjoint' := by
    simp_rw [PairwiseDisjoint, Set.Pairwise, Function.onFun, disjoint_iff_inter_eq_empty]
    intro ⟨a, ja, _⟩ _ ⟨b, jb, map_mk⟩ _ ne
    exact disjoint_openCell_of_ne (by aesop)
  disjointBase' := fun l ⟨i, _⟩ ↦ disjointBase l i
  mapsto := by
    intro l ⟨i, lltn⟩
    obtain ⟨I, hI⟩ := cellFrontier_subset_finite_closedCell (C := C) l i
    use fun (m : ℕ) ↦ (I m).subtype (fun _ ↦ m < n)
    simp_rw [mapsTo', iUnion_subtype]
    refine subset_trans hI (union_subset_union_right _ ?_)
    apply (iUnion_mono fun m ↦ iUnion_mono fun mltl ↦ iUnion_mono fun j ↦ ?_ )
    simp_all only [(Nat.cast_lt.2 mltl).trans lltn, Finset.mem_subtype, iUnion_true,
      iUnion_subset_iff]
    exact fun _ ↦ by rfl
  closed' A asublevel := by
    have : A ⊆ C := asublevel.trans levelaux_subset_complex
    -- This follows from `isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell`
    -- and `levelaux_inter_openCell_eq_empty`.
    intro ⟨h1, h2⟩
    simp_rw [Subtype.forall] at h1
    apply isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell this h2
    intro m _ j
    by_cases mlt : m < n
    · exact Or.intro_right _ (h1 m j mlt)
    left
    push_neg at mlt
    rw [← inter_eq_left.2 asublevel, inter_assoc, levelaux_inter_openCell_eq_empty mlt, inter_empty]
    exact isClosed_empty
  isClosedBase := isClosedBase C
  union' := by
    congr
    apply iUnion_congr fun m ↦ ?_
    rw [iUnion_subtype, iUnion_comm]
    rfl

/-- `level n` is a CW-complex for every `n : ℕ∞`.-/
instance RelCWComplex_level (n : ℕ∞) : RelCWComplex (level C D n) D :=
  RelCWComplex_levelaux _

variable {E F : Set X} [RelCWComplex E F]

/-- The union of two disjoint CW-complexes is again a CW-complex.-/
def CWComplex_disjointUnion (disjoint : Disjoint C E) (hDF : SeparatedNhds D F) :
    RelCWComplex (C ∪ E) (D ∪ F) where
  cell n := Sum (cell C D n) (cell E F n)
  map n := Sum.elim (map (C := C) n) (map (C := E) n)
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
  disjointBase' := by
    intro n cn
    rcases cn with cn | cn
    · exact (disjointBase (C := C) (D := D) _ _).union_right
       (disjoint.mono (openCell_subset_complex _ _) base_subset_complex)
    · exact (disjoint.symm.mono (openCell_subset_complex n cn) base_subset_complex).union_right
        (disjointBase (C := E) (D := F) _ _)
  mapsto n i := by
    classical
    rcases i with ic | id
    · obtain ⟨I, hI⟩ := cellFrontier_subset_finite_closedCell n ic
      use fun m ↦ (I m).image Sum.inl
      rw [mapsTo', union_assoc]
      apply hI.trans
      apply union_subset_union_right
      apply subset_union_of_subset_right
      simp only [Finset.mem_image, iUnion_exists, biUnion_and', iUnion_iUnion_eq_right]
      rfl
    · obtain ⟨I, hI⟩ := cellFrontier_subset_finite_closedCell n id
      use fun m ↦ (I m).image Sum.inr
      rw [mapsTo', union_comm D, union_assoc]
      apply hI.trans
      apply union_subset_union_right
      apply subset_union_of_subset_right
      simp only [Finset.mem_image, iUnion_exists, biUnion_and', iUnion_iUnion_eq_right]
      rfl
  closed' A asubce := by
    intro ⟨h1, h2⟩
    -- We show closedness separately for `A ∩ C` and `A ∩ D` which then follow from
    -- the property `closed'` of `C` and `D`.
    suffices IsClosed ((A ∩ C) ∪ (A ∩ E)) by
      convert this using 1
      simp only [union_inter_distrib_left, union_eq_right.2 inter_subset_left,
        inter_union_distrib_right, left_eq_inter, subset_inter_iff, subset_union_left, asubce,
        and_self]
    rw [inter_union_distrib_left] at h2
    have : SeparatedNhds (A ∩ D) (A ∩ F) := hDF.mono inter_subset_right inter_subset_right
    apply IsClosed.union
    · rw [closed C D (A ∩ C) inter_subset_right]
      constructor
      · intro n j
        rw [inter_right_comm]
        exact (h1 n (Sum.inl j)).inter (isClosed (D := D))
      · rw [inter_assoc, (inter_eq_right (s := C)).2 base_subset_complex]
        exact isClosed_left_of_isClosed_union this h2
    · rw [closed E F (A ∩ E) inter_subset_right]
      constructor
      · intro n j
        rw [inter_right_comm]
        exact (h1 n (Sum.inr j)).inter (isClosed (D := F))
      · rw [inter_assoc, (inter_eq_right (s := E)).2 base_subset_complex]
        exact isClosed_right_of_isClosed_union this h2
  isClosedBase := (isClosedBase C).union (isClosedBase E)
  union' := by
    simp_rw [← union (C := C) (D := D), ← union (C := E) (D := F), ← union_assoc,
      union_right_comm D _ F, union_assoc (D ∪ F), ← iUnion_union_distrib, iUnion_sum]
    rfl


end

def RelCWComplex_of_Homeomorph.{u} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (C D : Set X) (E F : Set Y) [RelCWComplex C D] (hC : IsClosed C) (hD : IsClosed D)
    (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E) (hDF : f '' D = F)
    (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E)  :
    RelCWComplex E F where
  cell := cell C D
  map n i := (map n i).trans f
  source_eq n i := sorry
  cont n i := by
    apply hfC2.comp (cont n i)
    rw [mapsTo']
    exact closedCell_subset_complex n i
  cont_symm n i := by
    rw [PartialEquiv.coe_trans_symm, PartialEquiv.trans_target'', hfC1,
      ← PartialEquiv.image_source_eq_target, source_eq n i, inter_eq_right.2
      (by exact closedCell_subset_complex n i)]
    refine ((cont_symm n i).comp (hfE2.mono ?_) ?_)
    · rw [← hfE1, ← f.image_source_eq_target, hfC1]
      exact image_mono (closedCell_subset_complex n i)
    · rw [mapsTo', f.symm_image_image_of_subset_source
        (by rw [hfC1]; exact closedCell_subset_complex n i), ← PartialEquiv.image_source_eq_target,
        source_eq n i]
  pairwiseDisjoint' := by
    have := pairwiseDisjoint (C := C) (D := D)
    simp only [PairwiseDisjoint, Set.Pairwise, mem_univ, ne_eq, Function.onFun,
      PartialEquiv.coe_trans, Function.comp_apply, forall_const] at this ⊢
    intro ⟨n, j⟩ ⟨m, i⟩ ne
    simp only [PartialEquiv.coe_trans, Function.comp_apply, ← image_image]
    refine (this ne).image ?_ (openCell_subset_complex n j) (openCell_subset_complex m i)
    rw [← hfC1]
    exact f.injOn
  disjointBase' n i := by
    simp only [PartialEquiv.coe_trans, Function.comp_apply, ← hDF, ← image_image]
    refine (RelCWComplex.disjointBase' n i).image ?_ (openCell_subset_complex n i)
      base_subset_complex
    rw [← hfC1]
    exact f.injOn
  mapsto n i := by
    obtain ⟨I, hI⟩ := mapsto (C := C) n i
    use I
    rw [mapsTo'] at hI ⊢
    simp only [PartialEquiv.coe_trans, Function.comp_apply, ← image_image, ← image_iUnion (f := f),
      preimage_union, ← hDF, ← image_union]
    exact image_mono hI
  closed' := sorry
  isClosedBase := sorry -- does this even hold?
  union' := sorry
