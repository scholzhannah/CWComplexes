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

variable {X : Type*} [t : TopologicalSpace X] [T2Space X] {C D : Set X}

section


/-- `levelaux n` is a CW-complex for every `n : ℕ∞`.-/
instance RelCWComplex_levelaux [RelCWComplex C D] (n : ℕ∞) : RelCWComplex (levelaux C D n) D where
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
    obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell (C := C) l i
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
instance RelCWComplex_level [RelCWComplex C D] (n : ℕ∞) : RelCWComplex (level C D n) D :=
  RelCWComplex_levelaux _

/-- The union of two disjoint CW-complexes is again a CW-complex.-/
def RelCWComplex_disjointUnion [RelCWComplex C D] {E F : Set X} [RelCWComplex E F]
    (disjoint : Disjoint C E) (hDF : SeparatedNhds D F) : RelCWComplex (C ∪ E) (D ∪ F) where
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
    · obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell n ic
      use fun m ↦ (I m).image Sum.inl
      rw [mapsTo', union_assoc]
      apply hI.trans
      apply union_subset_union_right
      apply subset_union_of_subset_right
      simp only [Finset.mem_image, iUnion_exists, biUnion_and', iUnion_iUnion_eq_right]
      rfl
    · obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell n id
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

-- The union of two disjoint CW-complexes is again a CW-complex.-/
def CWComplex_disjointUnion [CWComplex C] [CWComplex E] (disjoint : Disjoint C E) :
    CWComplex (C ∪ E) := CWComplex.mk (C ∪ E)
  (cell := fun n ↦ Sum (cell C ∅ n) (cell E ∅ n))
  (map := fun n ↦ Sum.elim (map (C := C) n) (map (C := E) n))
  (source_eq := fun n i ↦ match i with
    | Sum.inl x => source_eq n x
    | Sum.inr x => source_eq n x)
  (cont := fun n i ↦ match i with
    | Sum.inl x => cont n x
    | Sum.inr x => cont n x)
  (cont_symm := fun n i ↦ match i with
    | Sum.inl x => cont_symm n x
    | Sum.inr x => cont_symm n x)
  (pairwiseDisjoint' := by
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
    · exact disjoint_openCell_of_ne (by aesop))
  (mapsto := by
    classical
    intro n i
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
      rfl)
  (closed' := by
    intro A Asub h
    -- We show closedness separately for `A ∩ C` and `A ∩ D` which then follow from
    -- the property `closed'` of `C` and `D`.
    suffices IsClosed ((A ∩ C) ∪ (A ∩ E)) by
      convert this using 1
      simp only [union_inter_distrib_left, union_eq_right.2 inter_subset_left,
        inter_union_distrib_right, left_eq_inter, subset_inter_iff, subset_union_left, Asub,
        and_self]
    apply IsClosed.union
    · rw [closedAB C (A ∩ C) inter_subset_right]
      intro n j
      rw [inter_right_comm]
      exact (h n (Sum.inl j)).inter (isClosed (C := C) (D := ∅))
    · rw [closedAB E (A ∩ E) inter_subset_right]
      intro n j
      rw [inter_right_comm]
      exact (h n (Sum.inr j)).inter (isClosed (C := E) (D := ∅)))
  (union' := by
    simp_rw [← unionAB (C := C), ← unionAB (C := E), ← iUnion_union_distrib, iUnion_sum]
    rfl)

end

def RelCWComplex_attach_cell.{u} {X : Type u} [TopologicalSpace X] [T2Space X] (C D : Set X)
    [RelCWComplex C D]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = closedBall 0 1)
    (cont' : ContinuousOn map' (closedBall 0 1))
    (cont_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C D m), Disjoint (map' '' ball 0 1) (openCell m i))
    (disjointBase' : Disjoint (map' '' ball 0 1) D)
    (mapsto' : ∃ I : Π m, Finset (cell C D m),
      MapsTo map' (sphere 0 1) (D ∪ ⋃ (m < n) (j ∈ I m), closedCell m j)) :
    RelCWComplex (map' '' closedBall 0 1 ∪ C) D where
  cell m := cell (C := C) (D := D) m ⊕ {x : PUnit.{u + 1} // m = n}
  map m i := match i with
    | Sum.inl j => map m j
    | Sum.inr ⟨j, hj⟩ => hj ▸ map'
  source_eq m i := match i with
    | Sum.inl j => source_eq m j
    | Sum.inr ⟨j, hj⟩ => hj ▸ source_eq'
  cont m i := match i with
    | Sum.inl j => cont m j
    | Sum.inr ⟨j, hj⟩ => hj ▸ cont'
  cont_symm m i := match i with
    | Sum.inl j => cont_symm m j
    | Sum.inr ⟨j, hj⟩ => hj ▸ cont_symm'
  pairwiseDisjoint' := by
    rw [PairwiseDisjoint, Set.Pairwise]
    exact fun ⟨n1, j1⟩ _ ⟨n2, j2⟩ _ ↦ match j1 with
      | Sum.inl j1 => match j2 with
        | Sum.inl j2 => by
          have := RelCWComplex.pairwiseDisjoint' (C := C) (D := D)
          rw [PairwiseDisjoint, Set.Pairwise] at this
          intro ne
          apply @this ⟨n1, j1⟩ (mem_univ _) ⟨n2, j2⟩ (mem_univ _)
          aesop
        | Sum.inr ⟨j2, hj2⟩ => by
          intro _
          subst n2
          simp_rw [disjoint_comm]
          exact disjoint' n1 j1
      | Sum.inr ⟨j1, hj1⟩ => match j2 with
        | Sum.inl j2 => by
          intro _
          subst n1
          exact disjoint' n2 j2
        | Sum.inr ⟨j2, hj2⟩ => by
          intro ne
          subst hj1 hj2
          simp_all only [mem_univ, ne_eq, not_true_eq_false]
  disjointBase' m i := match i with
    | Sum.inl j => RelCWComplex.disjointBase' m j
    | Sum.inr ⟨j, hj⟩ => hj ▸ disjointBase'
  mapsto m i := match i with
    | Sum.inl j => by
      classical
      obtain ⟨I, hI⟩ := mapsto m j
      use fun m ↦ (I m).image Sum.inl
      simp [hI]
    | Sum.inr ⟨j, hj⟩ => by
      classical
      subst hj
      obtain ⟨I, hI⟩ := mapsto'
      use fun m ↦ (I m).image Sum.inl
      simpa
  closed' A Asub := by
    intro ⟨h1, h2⟩
    have : A = A ∩ map' '' closedBall 0 1 ∪ A ∩ C := by
      rw [← inter_union_distrib_left, inter_eq_left.2 Asub]
    rw [this]
    apply (h1 n (.inr ⟨PUnit.unit, rfl⟩)).union
    rw [closed C D (A := A ∩ C) inter_subset_right]
    constructor
    · intro n j
      rw [inter_assoc, inter_eq_right.2 (closedCell_subset_complex n j)]
      exact h1 n (.inl j)
    · rw [inter_assoc, inter_eq_right.2 (base_subset_complex (C := C))]
      exact h2
  isClosedBase := isClosedBase (C := C) (D := D)
  union' := by
    simp_rw [← union (C := C) (D := D), ← union_assoc, union_comm _ D, union_assoc]
    congrm D ∪ ?_
    ext
    simp only [mem_iUnion, Sum.exists, Subtype.exists, mem_union]
    constructor
    · intro ⟨m, h⟩
      rcases h with ⟨j, hj⟩ | ⟨j, rfl, hj⟩
      · exact .inr ⟨m, ⟨j, hj⟩⟩
      · exact .inl hj
    · intro h
      rcases h with hj | ⟨m, j, hj⟩
      · exact ⟨n, .inr ⟨PUnit.unit, ⟨rfl, hj⟩⟩⟩
      · exact ⟨m, .inl ⟨j, hj⟩⟩



-- this is getting way to ugly. Somehow one needs to avoid working with the PartialEquiv and
-- instead restrict to a Homeomorphism

def RelCWComplex_of_Homeomorph.{u} {X Y : Type u} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    (C D : Set X) (E F : Set Y) [RelCWComplex C D] (hC : IsClosed C) (hE : IsClosed E)
    (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E) (hDF : f '' D = F)
    (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E)  :
    RelCWComplex E F where
  cell := cell C D
  map n i := (map n i).trans f
  source_eq n i := by
    rw [PartialEquiv.trans_source, source_eq, inter_eq_left, hfC1, ← image_subset_iff]
    exact closedCell_subset_complex n i
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
  closed' A Asub := by
    have hDF' : f.IsImage D F := by
      apply PartialEquiv.IsImage.of_image_eq
      rw [hfC1, inter_eq_right.2 base_subset_complex, hfE1, ← hDF, ← hfE1,
        ← f.image_source_eq_target, hfC1, ← f.injOn.image_inter (by rw [hfC1])
        (by rw [hfC1]; exact base_subset_complex), inter_eq_right.2 base_subset_complex]
    intro ⟨h1, h2⟩
    have : f.IsImage (f.symm '' A) A := by sorry
    have : f '' (f.symm '' A) = A := by
      rw [← (inter_eq_right (s := f.source) (t := f.symm '' A)).2
      (by rw [← f.symm_image_target_eq_source, hfE1]; exact image_mono Asub),
      this.image_eq, inter_eq_right, hfE1]
      exact Asub
    have : A = E ∩ f.symm ⁻¹' (f.symm '' A) := by
      sorry
    rw [this]
    apply hfE2.preimage_isClosed_of_isClosed hE
    rw [closed C D]
    · constructor
      · intro n j
        specialize h1 n j
        simp at h1
        have : f.symm '' F = D := by
          rw [← (inter_eq_right (s := f.target) (t := F)).2
            (by rw [← hDF, ← f.image_source_eq_target, hfC1]; exact image_mono base_subset_complex),
            hDF'.symm_image_eq, inter_eq_right, hfC1]
          exact base_subset_complex

        sorry
      ·
        sorry
    · sorry
  isClosedBase := by
    have : f.IsImage D F := by
      apply PartialEquiv.IsImage.of_image_eq
      rw [hfC1, inter_eq_right.2 base_subset_complex, hfE1, ← hDF, ← hfE1,
        ← f.image_source_eq_target, hfC1, ← f.injOn.image_inter (by rw [hfC1])
        (by rw [hfC1]; exact base_subset_complex), inter_eq_right.2 base_subset_complex]
    have : f.symm ⁻¹' D ∩ E = F := by
      calc
        f.symm ⁻¹' D ∩ E = f.symm.source ∩ f.symm ⁻¹' D := by rw [inter_comm, f.symm_source, hfE1]
        _ = f.symm.source ∩ F := by
          rw [← PartialEquiv.IsImage.iff_preimage_eq, PartialEquiv.IsImage.symm_iff]
          exact this
        _ = F := by simp only [PartialEquiv.symm_source, ← f.image_source_eq_target, hfC1, ← hDF,
          inter_eq_right, image_mono base_subset_complex]
    rw [← this, inter_comm]
    exact hfE2.preimage_isClosed_of_isClosed hE (isClosedBase C)
  union' := by
    simp [← hDF, ← hfE1, ← f.image_source_eq_target, hfC1, ← RelCWComplex.union' (C := C) (D := D),
      image_union, image_iUnion, ← image_image]
