import CWcomplexes.Relative.RelFinite
import Mathlib.Analysis.NormedSpace.Real
import CWcomplexes.Auxiliary
import Mathlib.Data.ENat.Basic

/-!
# Constructions with CW-complexes

In this file we show that some basic constructions preserve CW-complexes:
* `CWComplex_disjointUnion`: The disjoint union of two CW-complexes is again a CW-complex.
* `CWComplex_of_Homeomorph`: The image of a CW-complex under a homeomorphism is again a CW-complex.
-/

noncomputable section

open Metric Set

variable {X : Type*} [t : TopologicalSpace X] [T2Space X] {C D : Set X}

section

/-- The union of two disjoint CW-complexes is again a CW-complex.-/
@[simps]
def RelCWComplex.disjointUnion [RelCWComplex C D] {E F : Set X} [RelCWComplex E F]
    (disjoint : Disjoint C E) (hDF : SeparatedNhds D F) : RelCWComplex (C ∪ E) (D ∪ F) where
  cell n := Sum (cell C n) (cell E n)
  map n := Sum.elim (map (C := C) n) (map (C := E) n)
  source_eq n i := match i with
    | Sum.inl x => source_eq n x
    | Sum.inr x => source_eq n x
  continuousOn n i := match i with
    | Sum.inl x => continuousOn n x
    | Sum.inr x => continuousOn n x
  continuousOn_symm n i := match i with
    | Sum.inl x => continuousOn_symm n x
    | Sum.inr x => continuousOn_symm n x
  pairwiseDisjoint' := by
    simp_rw [PairwiseDisjoint, Set.Pairwise, Function.onFun, disjoint_iff_inter_eq_empty]
    intro ⟨n, cn⟩ _ ⟨m, cm⟩ _ ne
    rcases cn with cn | cn
    · rcases cm with cm | cm
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
    · rw [closed C (A ∩ C) inter_subset_right]
      constructor
      · intro n j
        rw [inter_right_comm]
        exact (h1 n (Sum.inl j)).inter (isClosed (D := D))
      · rw [inter_assoc, (inter_eq_right (s := C)).2 base_subset_complex]
        exact isClosed_left_of_isClosed_union this h2
    · rw [closed E (A ∩ E) inter_subset_right]
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
@[simps!]
def ClasCWComplex.disjointUnion {E : Set X} [ClasCWComplex C] [ClasCWComplex E]
    (disjoint : Disjoint C E) : ClasCWComplex (C ∪ E) := ClasCWComplex.mk (C ∪ E)
  (cell := fun n ↦ Sum (cell C n) (cell E n))
  (map := fun n ↦ Sum.elim (map (C := C) n) (map (C := E) n))
  (source_eq := fun n i ↦ match i with
    | Sum.inl x => source_eq n x
    | Sum.inr x => source_eq n x)
  (continuousOn := fun n i ↦ match i with
    | Sum.inl x => continuousOn n x
    | Sum.inr x => continuousOn n x)
  (continuousOn_symm := fun n i ↦ match i with
    | Sum.inl x => continuousOn_symm n x
    | Sum.inr x => continuousOn_symm n x)
  (pairwiseDisjoint' := by
    simp_rw [PairwiseDisjoint, Set.Pairwise, Function.onFun, disjoint_iff_inter_eq_empty]
    intro ⟨n, cn⟩ _ ⟨m, cm⟩ _ ne
    rcases cn with cn | cn
    · rcases cm with cm | cm
      · exact disjoint_openCell_of_ne (by aesop)
      · exact subset_eq_empty (inter_subset_inter (openCell_subset_complex n cn)
          (openCell_subset_complex m cm)) (disjoint_iff_inter_eq_empty.1 disjoint)
    · rcases cm with cm | cm
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
    · rw [closed C (A ∩ C) inter_subset_right]
      intro n j
      rw [inter_right_comm]
      exact (h n (Sum.inl j)).inter (isClosed (C := C) (D := ∅))
    · rw [closed E (A ∩ E) inter_subset_right]
      intro n j
      rw [inter_right_comm]
      exact (h n (Sum.inr j)).inter (isClosed (C := E) (D := ∅)))
  (union' := by
    simp_rw [← union (C := C), ← union (C := E), ← iUnion_union_distrib, iUnion_sum]
    rfl)

lemma RelCWComplex.FiniteDimensional_disjointUnion [RelCWComplex C D] {E F : Set X}
    [RelCWComplex E F] [FiniteDimensional C] [FiniteDimensional E]
    (disjoint : Disjoint C E) (hDF : SeparatedNhds D F) :
    letI _complex := RelCWComplex.disjointUnion disjoint hDF
    FiniteDimensional (C ∪ E) :=
  let _complex := RelCWComplex.disjointUnion disjoint hDF
  {eventually_isEmpty_cell := by
    have h1 := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)
    have h2 := FiniteDimensional.eventually_isEmpty_cell (C := E) (D := F)
    simp only [Filter.eventually_atTop, ge_iff_le, RelCWComplex.disjointUnion_cell,
      isEmpty_sum] at h1 h2 ⊢
    obtain ⟨N1, hN1⟩ := h1
    obtain ⟨N2, hN2⟩ := h2
    use N1 ⊔ N2
    intro b hN1N2b
    exact ⟨hN1 b (le_of_max_le_left hN1N2b), hN2 b (le_of_max_le_right hN1N2b)⟩}

lemma ClasCWComplex.FiniteDimensional_disjointUnion [ClasCWComplex C] {E : Set X}
    [ClasCWComplex E] [FiniteDimensional C] [FiniteDimensional E]
    (disjoint : Disjoint C E) :
    letI _complex := disjointUnion disjoint
    FiniteDimensional (C ∪ E) :=
  let _complex := disjointUnion disjoint
  {eventually_isEmpty_cell := by
    -- why can I not write `FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅)`
    have h1 := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅)
    have h2 := FiniteDimensional.eventually_isEmpty_cell (C := E) (D := ∅)
    simp only [Filter.eventually_atTop, ge_iff_le, disjointUnion_cell, isEmpty_sum]
      at h1 h2 ⊢
    obtain ⟨N1, hN1⟩ := h1
    obtain ⟨N2, hN2⟩ := h2
    use N1 ⊔ N2
    intro b hN1N2b
    exact ⟨hN1 b (le_of_max_le_left hN1N2b), hN2 b (le_of_max_le_right hN1N2b)⟩}

lemma RelCWComplex.FiniteType_disjointUnion [RelCWComplex C D] {E F : Set X}
    [RelCWComplex E F] [FiniteType C] [FiniteType E] (disjoint : Disjoint C E)
    (hDF : SeparatedNhds D F) :
    letI _complex := RelCWComplex.disjointUnion disjoint hDF
    FiniteType (C ∪ E) :=
  let _complex := RelCWComplex.disjointUnion disjoint hDF
  {finite_cell := fun n ↦ by
    simp only [RelCWComplex.disjointUnion_cell]
    infer_instance}

lemma ClasCWComplex.FiniteType_disjointUnion [ClasCWComplex C] {E : Set X} [ClasCWComplex E]
    [FiniteType C]
    [FiniteType E] (disjoint : Disjoint C E) :
    letI _complex := disjointUnion disjoint
    FiniteType (C ∪ E) :=
  let _complex := disjointUnion disjoint
  {finite_cell := fun n ↦ by
    simp only [disjointUnion_cell]
    infer_instance}

lemma RelCWComplex.Finite_disjointUnion [RelCWComplex C D] {E F : Set X}
    [RelCWComplex E F] [Finite C] [Finite E]
    (disjoint : Disjoint C E) (hDF : SeparatedNhds D F) :
    letI _complex := RelCWComplex.disjointUnion disjoint hDF
    Finite (C ∪ E) :=
  let _complex := RelCWComplex.disjointUnion disjoint hDF
  let _finiteDimensional := FiniteDimensional_disjointUnion disjoint hDF
  let _finiteType := FiniteType_disjointUnion disjoint hDF
  inferInstance

lemma ClasCWComplex.Finite_disjointUnion [ClasCWComplex C] {E : Set X}
    [ClasCWComplex E] [Finite C] [Finite E] (disjoint : Disjoint C E) :
    letI _complex := disjointUnion disjoint
    Finite (C ∪ E) :=
  let _complex := disjointUnion disjoint
  let _finiteDimensional := FiniteDimensional_disjointUnion disjoint
  let _finiteType := FiniteType_disjointUnion disjoint
  inferInstance

end

@[simps]
def RelCWComplex.attachCell.{u} {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X)
    {D : Set X} [RelCWComplex C D]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = closedBall 0 1)
    (continuousOn' : ContinuousOn map' (closedBall 0 1))
    (continuousOn_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (disjointBase' : Disjoint (map' '' ball 0 1) D)
    (mapsto' : ∃ I : Π m, Finset (cell C m),
      MapsTo map' (sphere 0 1) (D ∪ ⋃ (m < n) (j ∈ I m), closedCell m j)) :
    RelCWComplex (map' '' closedBall 0 1 ∪ C) D where
  cell m := cell C (D := D) m ⊕' m = n
  map m i := match i with
    | .inl j => map m j
    | .inr hj => hj ▸ map'
  source_eq m i := match i with
    | .inl j => source_eq m j
    | .inr hj => hj ▸ source_eq'
  continuousOn m i := match i with
    | .inl j => continuousOn m j
    | .inr hj => hj ▸ continuousOn'
  continuousOn_symm m i := match i with
    | .inl j => continuousOn_symm m j
    | .inr hj => hj ▸ continuousOn_symm'
  pairwiseDisjoint' := by
    rw [PairwiseDisjoint, Set.Pairwise]
    exact fun ⟨n1, j1⟩ _ ⟨n2, j2⟩ _ ↦ match j1 with
      | .inl j1 => match j2 with
        | .inl j2 => by
          have := RelCWComplex.pairwiseDisjoint' (C := C) (D := D)
          rw [PairwiseDisjoint, Set.Pairwise] at this
          intro ne
          apply @this ⟨n1, j1⟩ (mem_univ _) ⟨n2, j2⟩ (mem_univ _)
          aesop
        | .inr hj2 => by
          intro _
          subst n2
          simp_rw [disjoint_comm]
          exact disjoint' n1 j1
      | .inr hj1 => match j2 with
        | .inl j2 => by
          intro _
          subst n1
          exact disjoint' n2 j2
        | .inr hj2 => by
          intro ne
          subst hj1 hj2
          simp_all only [mem_univ, ne_eq, not_true_eq_false]
  disjointBase' m i := match i with
    | .inl j => RelCWComplex.disjointBase' m j
    | .inr hj => hj ▸ disjointBase'
  mapsto m i := match i with
    | .inl j => by
      classical
      obtain ⟨I, hI⟩ := mapsto m j
      use fun m ↦ (I m).image .inl
      simp [hI]
    | .inr hj => by
      classical
      subst hj
      obtain ⟨I, hI⟩ := mapsto'
      use fun m ↦ (I m).image .inl
      simpa
  closed' A Asub := by
    intro ⟨h1, h2⟩
    have : A = A ∩ map' '' closedBall 0 1 ∪ A ∩ C := by
      rw [← inter_union_distrib_left, inter_eq_left.2 Asub]
    rw [this]
    apply (h1 n (.inr rfl)).union
    rw [closed C (A := A ∩ C) inter_subset_right]
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
    · intro ⟨m, i, h⟩
      rcases i with j | h'
      · exact .inr ⟨m, ⟨j, h⟩⟩
      · subst h'
        exact .inl h
    · intro h
      rcases h with hj | ⟨m, j, hj⟩
      · exact ⟨n, .inr rfl, hj⟩
      · exact ⟨m, .inl j, hj⟩

lemma RelCWComplex.FiniteDimensional_attachCell {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : Set X) {D : Set X} [RelCWComplex C D] [FiniteDimensional C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = closedBall 0 1)
    (continuousOn' : ContinuousOn map' (closedBall 0 1))
    (continuousOn_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (disjointBase' : Disjoint (map' '' ball 0 1) D)
    (mapsto' : ∃ I : Π m, Finset (cell C m),
      MapsTo map' (sphere 0 1) (D ∪ ⋃ (m < n) (j ∈ I m), closedCell m j)) :
    letI _complex := RelCWComplex.attachCell C map' source_eq' continuousOn' continuousOn_symm'
      disjoint' disjointBase' mapsto'
    FiniteDimensional (map' '' closedBall 0 1 ∪ C) :=
  let _complex := RelCWComplex.attachCell C map' source_eq' continuousOn' continuousOn_symm'
    disjoint' disjointBase' mapsto'
  {eventually_isEmpty_cell := by
    have h := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)
    simp only [Filter.eventually_atTop, ge_iff_le, RelCWComplex.attachCell, isEmpty_psum,
      isEmpty_Prop] at h ⊢
    obtain ⟨N, hN⟩ := h
    use N ⊔ n.succ
    intro b hb
    exact ⟨hN b (le_of_max_le_left hb) , Nat.ne_of_lt' (le_of_max_le_right hb)⟩}

@[simps!]
def RelCWComplex.attachCellFiniteType.{u} {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) {D : Set X} [RelCWComplex C D] [FiniteType C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = closedBall 0 1)
    (continuousOn' : ContinuousOn map' (closedBall 0 1))
    (continuousOn_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (disjointBase' : Disjoint (map' '' ball 0 1) D)
    (mapsto' : MapsTo map' (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell C m), closedCell m j)) :
    RelCWComplex (map' '' closedBall 0 1 ∪ C) D := RelCWComplex.attachCell C map'
  (source_eq' := source_eq')
  (continuousOn' := continuousOn')
  (continuousOn_symm' := continuousOn_symm')
  (disjoint' := disjoint')
  (disjointBase' := disjointBase')
  (mapsto' := by
    use fun m ↦ finite_univ.toFinset
    simpa)

lemma RelCWComplex.FinteDimensional_attachCellFiniteType {X : Type*} [TopologicalSpace X]
    [T2Space X] (C : Set X) {D : Set X} [RelCWComplex C D] [Finite C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = closedBall 0 1)
    (cont' : ContinuousOn map' (closedBall 0 1))
    (cont_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (disjointBase' : Disjoint (map' '' ball 0 1) D)
    (mapsto' : MapsTo map' (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell C m), closedCell m j)) :
    letI _complex := attachCellFiniteType C map' source_eq' cont' cont_symm'
      disjoint' disjointBase' mapsto'
    FiniteDimensional (map' '' closedBall 0 1 ∪ C) :=
  let _complex := attachCellFiniteType C map' source_eq' cont' cont_symm'
      disjoint' disjointBase' mapsto'
  {eventually_isEmpty_cell := by
    have h := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)
    simp only [Filter.eventually_atTop, ge_iff_le, RelCWComplex.attachCell_cell, isEmpty_psum,
      isEmpty_Prop] at h ⊢
    obtain ⟨N, hN⟩ := h
    use N ⊔ n.succ
    intro b hb
    exact ⟨hN b (le_of_max_le_left hb) , Nat.ne_of_lt' (le_of_max_le_right hb)⟩}

lemma RelCWComplex.FiniteType_attachCellFiniteType {X : Type*} [TopologicalSpace X]
    [T2Space X] (C : Set X) {D : Set X} [RelCWComplex C D] [FiniteType C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = closedBall 0 1)
    (continuousOn' : ContinuousOn map' (closedBall 0 1))
    (continuousOn_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (disjointBase' : Disjoint (map' '' ball 0 1) D)
    (mapsto' : MapsTo map' (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell C m), closedCell m j)) :
    letI _complex := attachCellFiniteType C map' source_eq' continuousOn' continuousOn_symm'
      disjoint' disjointBase' mapsto'
    FiniteType (map' '' closedBall 0 1 ∪ C) :=
  let _complex := attachCellFiniteType C map' source_eq' continuousOn' continuousOn_symm'
      disjoint' disjointBase' mapsto'
  {finite_cell := by
    intro m
    simp only [attachCell_cell]
    infer_instance}

lemma RelCWComplex.Finite_attachCellFiniteType {X : Type*} [TopologicalSpace X]
    [T2Space X] (C : Set X) {D : Set X} [RelCWComplex C D] [Finite C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = closedBall 0 1)
    (cont' : ContinuousOn map' (closedBall 0 1))
    (cont_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (disjointBase' : Disjoint (map' '' ball 0 1) D)
    (mapsto' : MapsTo map' (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell C m), closedCell m j)) :
    letI _complex := attachCellFiniteType C map' source_eq' cont' cont_symm'
      disjoint' disjointBase' mapsto'
    Finite (map' '' closedBall 0 1 ∪ C) :=
  let _complex := attachCellFiniteType C map' source_eq' cont' cont_symm'
      disjoint' disjointBase' mapsto'
  let _finiteDimensional := FinteDimensional_attachCellFiniteType C map'
      source_eq' cont' cont_symm' disjoint' disjointBase' mapsto'
  let _finiteType := FiniteType_attachCellFiniteType C map'
      source_eq' cont' cont_symm' disjoint' disjointBase' mapsto'
  inferInstance

@[simps!]
def ClasCWComplex.attachCell.{u} {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X)
    [ClasCWComplex C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = closedBall 0 1)
    (continuousOn' : ContinuousOn map' (closedBall 0 1))
    (continuousOn_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (mapsto' : ∃ I : Π m, Finset (cell C m),
      MapsTo map' (sphere 0 1) (⋃ (m < n) (j ∈ I m), closedCell m j)) :
    ClasCWComplex (map' '' closedBall 0 1 ∪ C) := RelCWComplex.attachCell C map'
  (source_eq' := source_eq')
  (continuousOn' := continuousOn')
  (continuousOn_symm' := continuousOn_symm')
  (disjoint' := disjoint')
  (disjointBase' := disjoint_empty _)
  (mapsto' := by
    simp_rw [empty_union]
    exact mapsto')

lemma ClasCWComplex.FiniteDimensional_attachCell {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : Set X) [ClasCWComplex C] [FiniteDimensional C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = closedBall 0 1)
    (cont' : ContinuousOn map' (closedBall 0 1))
    (cont_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (mapsto' : ∃ I : Π m, Finset (cell C m),
      MapsTo map' (sphere 0 1) (⋃ (m < n) (j ∈ I m), closedCell m j)) :
    letI _complex := attachCell C map' source_eq' cont' cont_symm' disjoint' mapsto'
    FiniteDimensional (map' '' closedBall 0 1 ∪ C) :=
  let _complex := attachCell C map' source_eq' cont' cont_symm' disjoint' mapsto'
  {eventually_isEmpty_cell := by
    have h := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅)
    simp only [Filter.eventually_atTop, ge_iff_le, RelCWComplex.attachCell_cell, isEmpty_psum,
      isEmpty_Prop] at h ⊢
    obtain ⟨N, hN⟩ := h
    use N ⊔ n.succ
    intro b hb
    exact ⟨hN b (le_of_max_le_left hb) , Nat.ne_of_lt' (le_of_max_le_right hb)⟩}

@[simps!]
def ClasCWComplex.attachCellFiniteType.{u} {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X)
    [ClasCWComplex C] [FiniteType C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = closedBall 0 1)
    (continuousOn' : ContinuousOn map' (closedBall 0 1))
    (continuousOn_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (mapsto' : MapsTo map' (sphere 0 1) (⋃ (m < n) (j : cell C m), closedCell m j)) :
    ClasCWComplex (map' '' closedBall 0 1 ∪ C) := attachCell C map'
  (source_eq' := source_eq')
  (continuousOn' := continuousOn')
  (continuousOn_symm' := continuousOn_symm')
  (disjoint' := disjoint')
  (mapsto' := by
    use fun m ↦ finite_univ.toFinset
    simpa)

lemma ClasCWComplex.FiniteType_attachCellFiniteType {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : Set X) [ClasCWComplex C] [FiniteType C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = closedBall 0 1)
    (continuousOn' : ContinuousOn map' (closedBall 0 1))
    (continuousOn_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (mapsto' : MapsTo map' (sphere 0 1) (⋃ (m < n) (j : cell C m), closedCell m j)) :
  letI _complex := attachCellFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
    mapsto'
  FiniteType (map' '' closedBall 0 1 ∪ C) :=
  let _complex := attachCellFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
    mapsto'
  {finite_cell := by
    intro m
    simp only [attachCell_cell]
    infer_instance}

lemma ClasCWComplex.FiniteDimensional_attachCellFiniteType {X : Type*} [TopologicalSpace X]
    [T2Space X] (C : Set X) [ClasCWComplex C] [Finite C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = closedBall 0 1)
    (continuousOn' : ContinuousOn map' (closedBall 0 1))
    (continuousOn_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (mapsto' : MapsTo map' (sphere 0 1) (⋃ (m < n) (j : cell C m), closedCell m j)) :
  letI _complex := attachCellFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
    mapsto'
  FiniteDimensional (map' '' closedBall 0 1 ∪ C) :=
  let _complex := attachCellFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
    mapsto'
  {eventually_isEmpty_cell := by
    have h := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅)
    simp only [Filter.eventually_atTop, ge_iff_le, attachCell_cell, isEmpty_psum,
      isEmpty_Prop] at h ⊢
    obtain ⟨N, hN⟩ := h
    use N ⊔ n.succ
    intro b hb
    exact ⟨hN b (le_of_max_le_left hb) , Nat.ne_of_lt' (le_of_max_le_right hb)⟩}

lemma ClasCWComplex.Finite_attachCellFiniteType {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : Set X) [ClasCWComplex C] [Finite C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = closedBall 0 1)
    (continuousOn' : ContinuousOn map' (closedBall 0 1))
    (continuousOn_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (mapsto' : MapsTo map' (sphere 0 1) (⋃ (m < n) (j : cell C m), closedCell m j)) :
  letI _complex := attachCellFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
    mapsto'
  Finite (map' '' closedBall 0 1 ∪ C) :=
  let _complex := attachCellFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
    mapsto'
  let _finiteDimensional := FiniteDimensional_attachCellFiniteType C map' source_eq'
    continuousOn' continuousOn_symm' disjoint' mapsto'
  let _finiteType := FiniteType_attachCellFiniteType C map' source_eq' continuousOn'
    continuousOn_symm' disjoint' mapsto'
  inferInstance

def RelCWComplex.ofEq {X : Type*} [TopologicalSpace X] (C D : Set X)
    {E F : Set X} [RelCWComplex C D] (hCE : C = E) (hDF : D = F) : RelCWComplex E F where
  cell := cell C
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  disjointBase' := hDF ▸ disjointBase'
  mapsto := hDF ▸ mapsto
  closed' := hCE ▸ hDF ▸ closed'
  isClosedBase := hDF ▸ isClosedBase C
  union' := hCE ▸ hDF ▸ union'

lemma RelCWComplex.finiteDimensional_ofEq {X : Type*} [TopologicalSpace X] (C D : Set X)
    {E F : Set X} [RelCWComplex C D] [FiniteDimensional C] (hCE : C = E) (hDF : D = F) :
    letI _ := ofEq C D hCE hDF
    FiniteDimensional E :=
  let _ := ofEq C D hCE hDF
  {eventually_isEmpty_cell := FiniteDimensional.eventually_isEmpty_cell (C := C)}

lemma RelCWComplex.finiteType_ofEq {X : Type*} [TopologicalSpace X] (C D : Set X)
    {E F : Set X} [RelCWComplex C D] [FiniteType C] (hCE : C = E) (hDF : D = F) :
    letI _ := ofEq C D hCE hDF
    FiniteType E :=
  let _ := ofEq C D hCE hDF
  {finite_cell := FiniteType.finite_cell (C := C)}

lemma RelCWComplex.finite_ofEq {X : Type*} [TopologicalSpace X] (C D : Set X)
    {E F : Set X} [RelCWComplex C D] [Finite C] (hCE : C = E) (hDF : D = F) :
    letI _ := ofEq C D hCE hDF
    Finite E :=
  let _ := ofEq C D hCE hDF
  let _ := finiteDimensional_ofEq C D hCE hDF
  let _ := finiteType_ofEq C D hCE hDF
  inferInstance

-- this is getting way to ugly. Somehow one needs to avoid working with the PartialEquiv and
-- instead restrict to a Homeomorphism

open Set.Notation in
def RelCWComplex.restrict [RelCWComplex C D] (Y : Set X) (hCY : C ⊆ Y) :
    RelCWComplex (X := Y) (Y ↓∩ C) (Y ↓∩ D) where
  cell := cell C
  map n i :=  sorry --map (C := C) (D := D) n i
  source_eq := sorry
  continuousOn := sorry
  continuousOn_symm := sorry
  pairwiseDisjoint' := sorry
  disjointBase' := sorry
  mapsto := sorry
  closed' := sorry
  isClosedBase := sorry
  union' := sorry

def RelCWComplex.of_Homeomorph.{u} {X Y : Type u} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y} [RelCWComplex C D]
    (hC : IsClosed C) (hE : IsClosed E)
    (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E) (hDF : f '' D = F)
    (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E)  :
    RelCWComplex E F where
  cell := cell C
  map n i := (map n i).trans f
  source_eq n i := by
    rw [PartialEquiv.trans_source, source_eq, inter_eq_left, hfC1, ← image_subset_iff]
    exact closedCell_subset_complex n i
  continuousOn n i := by
    apply hfC2.comp (continuousOn n i)
    rw [mapsTo']
    exact closedCell_subset_complex n i
  continuousOn_symm n i := by
    rw [PartialEquiv.coe_trans_symm, PartialEquiv.trans_target'', hfC1,
      ← PartialEquiv.image_source_eq_target, source_eq n i, inter_eq_right.2
      (by exact closedCell_subset_complex n i)]
    refine ((continuousOn_symm n i).comp (hfE2.mono ?_) ?_)
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
    rw [closed C ]
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
      · sorry
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

namespace ClasCWComplex

export RelCWComplex (ofEq finiteDimensional_ofEq finiteType_ofEq finite_ofEq)

end ClasCWComplex
