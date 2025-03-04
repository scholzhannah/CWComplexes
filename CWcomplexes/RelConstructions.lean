import CWcomplexes.RelFinite
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
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
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
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
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

-- make disjoint' more general: disjointness with the whole original complex
-- write a version where mapsto' is better as well

/-- A version of `RelCWComplex.attachCell`. Assuming that the CW complex is of finite type lets us
  relax the condition `mapsto'`. -/
@[simps!]
def RelCWComplex.attachCellFiniteType.{u} {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) {D : Set X} [RelCWComplex C D] [FiniteType C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
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

lemma RelCWComplex.FiniteDimensional_attachCellFiniteType {X : Type*} [TopologicalSpace X]
    [T2Space X] (C : Set X) {D : Set X} [RelCWComplex C D] [Finite C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
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
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
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
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
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
  let _finiteDimensional := FiniteDimensional_attachCellFiniteType C map'
      source_eq' cont' cont_symm' disjoint' disjointBase' mapsto'
  let _finiteType := FiniteType_attachCellFiniteType C map'
      source_eq' cont' cont_symm' disjoint' disjointBase' mapsto'
  inferInstance

@[simps!]
def ClasCWComplex.attachCell.{u} {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X)
    [ClasCWComplex C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
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
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
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
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
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
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
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
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
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
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
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

@[simps]
def RelCWComplex.attachCells.{u} {X : Type u} [TopologicalSpace X] [T2Space X] (C D : Set X)
    [RelCWComplex C D] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (disjointBase' : ∀ i, Disjoint (map' i '' ball 0 1) D)
    (mapsto' : ∀ i, ∃ I : Π m, Finset (cell C m),
      MapsTo (map' i) (sphere 0 1) (D ∪ ⋃ (m < n) (j ∈ I m), closedCell m j)) :
    RelCWComplex ((⋃ i, map' i '' closedBall 0 1) ∪ C) D where
  cell m := cell C m ⊕ ι ×' m = n
  map m j := match m, j with
    | m, .inl j => map m j
    | _, .inr ⟨j, rfl⟩ => map' j
  source_eq m j := match m, j with
    | m, .inl j => source_eq m j
    | _, .inr ⟨j, rfl⟩ => source_eq' j
  continuousOn m j :=  match m, j with
    | m, .inl j => continuousOn m j
    | _, .inr ⟨j, rfl⟩ => continuousOn' j
  continuousOn_symm m j := match m, j with
    | m, .inl j => continuousOn_symm m j
    | _, .inr ⟨j, rfl⟩ => continuousOn_symm' j
  pairwiseDisjoint' := by
    rw [PairwiseDisjoint, Set.Pairwise]
    exact fun ⟨m1, j1⟩ _ ⟨m2, j2⟩ _ ↦ match m1, j1 with
      | m1, .inl j1 => match m2, j2 with
        | m2, .inl j2 => by
          have := RelCWComplex.pairwiseDisjoint (C := C) (D := D)
          rw [PairwiseDisjoint, Set.Pairwise] at this
          intro h
          apply @this ⟨m1, j1⟩ (mem_univ _) ⟨m2, j2⟩ (mem_univ _)
          aesop
        | _, .inr ⟨j2, rfl⟩ => by
          intro h
          rw [Function.onFun_apply, disjoint_comm]
          exact disjoint' j2 m1 j1
      | _, .inr ⟨j1, rfl⟩ => match m2, j2 with
        | m2, .inl j2 => by
          intro h
          rw [Function.onFun_apply]
          exact disjoint' j1 m2 j2
        | _, .inr ⟨j2, rfl⟩ => by
          intro h
          rw [Function.onFun_apply]
          simp
          apply disjoint'' j1 j2
          aesop
  disjointBase' m j := match m, j with
    | m, .inl j => RelCWComplex.disjointBase' m j
    | _, .inr ⟨j, rfl⟩ => disjointBase' j
  mapsto m j := match m, j with
    | m, .inl j => by
      classical
      obtain ⟨I, hI⟩ := mapsto m j
      use fun l ↦ (I l).image .inl
      simp [hI]
    | _, .inr ⟨j, rfl⟩ => by
      classical
      obtain ⟨I, hI⟩ := mapsto' j
      use fun l ↦ (I l).image .inl
      simp only [Finset.mem_image, iUnion_exists, biUnion_and', iUnion_iUnion_eq_right]
      exact hI
  closed' A hA := by
    intro ⟨hA1, hA2⟩
    have : A = A ∩ (⋃ i, map' i '' closedBall 0 1) ∪ A ∩ C := by
      rw [← inter_union_distrib_left, inter_eq_left.2 hA]
    rw [this]
    apply IsClosed.union
    · rw [inter_iUnion]
      apply isClosed_iUnion_of_finite
      intro i
      exact hA1 n (.inr ⟨i, rfl⟩)
    · rw [closed C (A := A ∩ C) inter_subset_right]
      constructor
      · intro n j
        rw [inter_assoc, inter_eq_right.2 (closedCell_subset_complex n j)]
        exact hA1 n (.inl j)
      · rw [inter_assoc, inter_eq_right.2 (base_subset_complex (C := C))]
        exact hA2
  isClosedBase := isClosedBase C
  union' := by
    simp_rw [union_comm _ C, ← union (C := C), union_assoc]
    congrm D ∪ ?_
    ext x
    simp only [mem_iUnion, Sum.exists, PProd.exists, mem_union]
    constructor
    · intro ⟨m, h⟩
      rcases h with ⟨j, h⟩ | ⟨j, rfl, h⟩
      · exact .inl ⟨m, j, h⟩
      · exact .inr ⟨j, h⟩
    · intro h
      rcases h with ⟨m, j, h⟩ | ⟨j, h⟩
      · exact ⟨m, .inl ⟨j, h⟩⟩
      · exact ⟨n, .inr ⟨j, rfl, h⟩⟩

lemma RelCWComplex.FiniteDimensional_attachCells.{u} {X : Type u} [TopologicalSpace X]
    [T2Space X] (C D : Set X) [RelCWComplex C D] [FiniteDimensional C]
    {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (disjointBase' : ∀ i, Disjoint (map' i '' ball 0 1) D)
    (mapsto' : ∀ i, ∃ I : Π m, Finset (cell C m),
      MapsTo (map' i) (sphere 0 1) (D ∪ ⋃ (m < n) (j ∈ I m), closedCell m j)) :
    letI := attachCells C D map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' disjointBase' mapsto'
    FiniteDimensional ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  let _ := attachCells C D map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' disjointBase' mapsto'
  {eventually_isEmpty_cell := by
    have h := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)
    simp only [Filter.eventually_atTop, ge_iff_le, attachCells_cell, isEmpty_sum, isEmpty_pprod,
      isEmpty_Prop] at h ⊢
    obtain ⟨N, hN⟩ := h
    use N ⊔ n.succ
    intro b hb
    exact ⟨hN b (le_of_max_le_left hb), .inr (Nat.ne_of_lt' (le_of_max_le_right hb))⟩}

/-- A version of `RelCWComplex.attachCells`. Assuming that the CW complex is of finite type lets us
  relax the condition `mapsto'`. -/
@[simps!]
def RelCWComplex.attachCellsFiniteType.{u} {X : Type u} [TopologicalSpace X] [T2Space X]
    (C D : Set X) [RelCWComplex C D] [FiniteType C] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (disjointBase' : ∀ i, Disjoint (map' i '' ball 0 1) D)
    (mapsto' : ∀ i, MapsTo (map' i) (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell C m) , closedCell m j)) :
    RelCWComplex ((⋃ i, map' i '' closedBall 0 1) ∪ C) D :=
  attachCells C D map' source_eq' continuousOn' continuousOn_symm' disjoint' disjoint''
    disjointBase'
    (mapsto' := by
      intro i
      use fun m ↦ finite_univ.toFinset
      simp [mapsto' i])

lemma RelCWComplex.FiniteDimensional_attachCellsFiniteType.{u} {X : Type u} [TopologicalSpace X]
    [T2Space X] (C D : Set X) [RelCWComplex C D] [Finite C] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (disjointBase' : ∀ i, Disjoint (map' i '' ball 0 1) D)
    (mapsto' : ∀ i, MapsTo (map' i) (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell C m) , closedCell m j)) :
    letI := attachCellsFiniteType C D map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' disjointBase' mapsto'
    FiniteDimensional ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  let _ := attachCellsFiniteType C D map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' disjointBase' mapsto'
  {eventually_isEmpty_cell := by
    have h := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)
    simp only [Filter.eventually_atTop, ge_iff_le, attachCells_cell, isEmpty_sum, isEmpty_pprod,
      isEmpty_Prop] at h ⊢
    obtain ⟨N, hN⟩ := h
    use N ⊔ n.succ
    intro b hb
    exact ⟨hN b (le_of_max_le_left hb), .inr (Nat.ne_of_lt' (le_of_max_le_right hb))⟩}

lemma RelCWComplex.FiniteType_attachCellsFiniteType.{u} {X : Type u} [TopologicalSpace X]
    [T2Space X] (C D : Set X) [RelCWComplex C D] [FiniteType C] {n : ℕ} {ι : Type u}
    [_root_.Finite ι] (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (disjointBase' : ∀ i, Disjoint (map' i '' ball 0 1) D)
    (mapsto' : ∀ i, MapsTo (map' i) (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell C m) , closedCell m j)) :
    letI := attachCellsFiniteType C D map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' disjointBase' mapsto'
    FiniteType ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  let _ := attachCellsFiniteType C D map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' disjointBase' mapsto'
  {finite_cell := by
    intro m
    simp only [attachCells_cell]
    infer_instance}

lemma RelCWComplex.Finite_attachCellsFiniteType.{u} {X : Type u} [TopologicalSpace X]
    [T2Space X] (C D : Set X) [RelCWComplex C D] [Finite C] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (disjointBase' : ∀ i, Disjoint (map' i '' ball 0 1) D)
    (mapsto' : ∀ i, MapsTo (map' i) (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell C m) , closedCell m j)) :
    letI := attachCellsFiniteType C D map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' disjointBase' mapsto'
    Finite ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  let _ := attachCellsFiniteType C D map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' disjointBase' mapsto'
  let _ := FiniteDimensional_attachCellsFiniteType C D map' source_eq' continuousOn'
    continuousOn_symm' disjoint' disjoint'' disjointBase' mapsto'
  let _ := FiniteType_attachCellsFiniteType C D map' source_eq' continuousOn' continuousOn_symm'
      disjoint' disjoint'' disjointBase' mapsto'
  inferInstance

@[simps!]
def ClasCWComplex.attachCells.{u} {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X)
    [ClasCWComplex C] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (mapsto' : ∀ i, ∃ I : Π m, Finset (cell C m),
      MapsTo (map' i) (sphere 0 1) (⋃ (m < n) (j ∈ I m), closedCell m j)) :
    ClasCWComplex ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  RelCWComplex.attachCells C ∅ map' source_eq' continuousOn' continuousOn_symm' disjoint' disjoint''
    (disjointBase' := by simp) (mapsto' := by simpa)

lemma ClasCWComplex.FiniteDimensional_attachCells.{u} {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [ClasCWComplex C] [FiniteDimensional C] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (mapsto' : ∀ i, ∃ I : Π m, Finset (cell C m),
      MapsTo (map' i) (sphere 0 1) (⋃ (m < n) (j ∈ I m), closedCell m j)) :
    letI := attachCells C map' source_eq' continuousOn' continuousOn_symm' disjoint' disjoint''
      mapsto'
    FiniteDimensional ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  let _ := attachCells C map' source_eq' continuousOn' continuousOn_symm' disjoint' disjoint''
      mapsto'
  {eventually_isEmpty_cell := by
    have h := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅)
    simp only [Filter.eventually_atTop, ge_iff_le, RelCWComplex.attachCells_cell, isEmpty_sum,
      isEmpty_pprod, isEmpty_Prop] at h ⊢
    obtain ⟨N, hN⟩ := h
    use N ⊔ n.succ
    intro b hb
    exact ⟨hN b (le_of_max_le_left hb), .inr (Nat.ne_of_lt' (le_of_max_le_right hb))⟩}

/-- A version of `RelCWComplex.attachCells`. Assuming that the CW complex is of finite type lets us
  relax the condition `mapsto'`. -/
@[simps!]
def ClasCWComplex.attachCellsFiniteType.{u} {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [ClasCWComplex C] [FiniteType C] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (mapsto' : ∀ i, MapsTo (map' i) (sphere 0 1) (⋃ (m < n) (j : cell C m) , closedCell m j)) :
    ClasCWComplex ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  attachCells C map' source_eq' continuousOn' continuousOn_symm' disjoint' disjoint''
    (mapsto' := by
      intro i
      use fun m ↦ finite_univ.toFinset
      simp [mapsto' i])

lemma ClasCWComplex.FiniteDimensional_attachCellsFiniteType.{u} {X : Type u} [TopologicalSpace X]
    [T2Space X] (C : Set X) [ClasCWComplex C] [Finite C] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (mapsto' : ∀ i, MapsTo (map' i) (sphere 0 1) (⋃ (m < n) (j : cell C m) , closedCell m j)) :
    letI := attachCellsFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' mapsto'
    FiniteDimensional ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  let _ := attachCellsFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
    disjoint'' mapsto'
  {eventually_isEmpty_cell := by
    have h := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅)
    simp only [Filter.eventually_atTop, ge_iff_le, attachCells_cell, isEmpty_sum, isEmpty_pprod,
      isEmpty_Prop] at h ⊢
    obtain ⟨N, hN⟩ := h
    use N ⊔ n.succ
    intro b hb
    exact ⟨hN b (le_of_max_le_left hb), .inr (Nat.ne_of_lt' (le_of_max_le_right hb))⟩}

lemma ClasCWComplex.FiniteType_attachCellsFiniteType.{u} {X : Type u} [TopologicalSpace X]
    [T2Space X] (C : Set X) [ClasCWComplex C] [FiniteType C] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (mapsto' : ∀ i, MapsTo (map' i) (sphere 0 1) (⋃ (m < n) (j : cell C m) , closedCell m j)) :
    letI := attachCellsFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' mapsto'
    FiniteType ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  let _ := attachCellsFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
    disjoint'' mapsto'
  {finite_cell := by
    intro m
    simp only [attachCells_cell]
    infer_instance}

lemma ClasCWComplex.Finite_attachCellsFiniteType.{u} {X : Type u} [TopologicalSpace X]
    [T2Space X] (C : Set X) [ClasCWComplex C] [Finite C] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (mapsto' : ∀ i, MapsTo (map' i) (sphere 0 1) (⋃ (m < n) (j : cell C m) , closedCell m j)) :
    letI := attachCellsFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' mapsto'
    Finite ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  let _ := attachCellsFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
    disjoint'' mapsto'
  let _ := FiniteDimensional_attachCellsFiniteType C map' source_eq' continuousOn'
    continuousOn_symm' disjoint' disjoint'' mapsto'
  let _ := FiniteType_attachCellsFiniteType C map' source_eq' continuousOn'
    continuousOn_symm' disjoint' disjoint'' mapsto'
  inferInstance

@[simps]
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

/-- A partial bijection with closed source and target that is continuous on both source and target
  preserves CW-structures. -/
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

/-- `RelCWComplex.ofPartialEquiv` preserves finite dimensionality. -/
lemma RelCWComplex.FiniteDimensional_ofPartialEquiv.{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y}
    [RelCWComplex C D] [FiniteDimensional C] (hC : IsClosed C) (hE : IsClosed E)
    (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E) (hDF : f '' D = F)
    (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E) :
    letI := ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
    FiniteDimensional E :=
  let _ := ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
  {eventually_isEmpty_cell := FiniteDimensional.eventually_isEmpty_cell (C := C)}

/-- `RelCWComplex.ofPartialEquiv` preserves finite type. -/
lemma RelCWComplex.FiniteType_ofPartialEquiv.{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y}
    [RelCWComplex C D] [FiniteType C] (hC : IsClosed C) (hE : IsClosed E)
    (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E) (hDF : f '' D = F)
    (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E) :
    letI := ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
    FiniteType E :=
  let _ := ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
  {finite_cell := FiniteType.finite_cell (C := C)}

/-- `RelCWComplex.ofPartialEquiv` preserves finiteness. -/
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

/-- A version of `RelCWComplex.ofPartialEquiv` for absolute CW-complexes. -/
def ClasCWComplex.ofPartialEquiv.{u} {X Y : Type u} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] (C : Set X) (E : Set Y) [ClasCWComplex C] (hC : IsClosed C)
    (hE : IsClosed E) (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E)
    (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E)  :
    ClasCWComplex E :=
  RelCWComplex.ofPartialEquiv C E hC hE f hfC1 hfE1 (image_empty f)  hfC2 hfE2

/-- `ClasCWComplex.ofPartialEquiv` preserves finite dimensionality. -/
lemma ClasCWComplex.FiniteDimensional_ofPartialEquiv .{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) (E : Set Y) [ClasCWComplex C] [FiniteDimensional C]
    (hC : IsClosed C) (hE : IsClosed E) (f : PartialEquiv X Y) (hfC1 : f.source = C)
    (hfE1 : f.target = E) (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E)  :
    letI := ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
    FiniteDimensional E :=
  let _ := ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
  { eventually_isEmpty_cell := FiniteDimensional.eventually_isEmpty_cell (C := C) }

/-- `ClasCWComplex.ofPartialEquiv` preserves finite type. -/
lemma ClasCWComplex.FiniteType_ofPartialEquiv .{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) (E : Set Y) [ClasCWComplex C] [FiniteType C]
    (hC : IsClosed C) (hE : IsClosed E) (f : PartialEquiv X Y) (hfC1 : f.source = C)
    (hfE1 : f.target = E) (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E)  :
    letI := ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
    FiniteType E :=
  let _ := ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
  { finite_cell := FiniteType.finite_cell (C := C) }

/-- `ClasCWComplex.ofPartialEquiv` preserves finiteness. -/
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

-- this should probably be proven using the other version
/-- The image of a CW-complex under a homeomorphisms is again a CW-complex.-/
def RelCWComplex.ofHomeomorph.{u} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X]
    (C : Set X) {D : Set X} (E : Set Y) {F : Set Y} [RelCWComplex C D] (f : X ≃ₜ Y)
    (hCE : f '' C = E) (hDF : f '' D = F) :
    RelCWComplex E F :=
  have : f.toPartialEquiv.IsImage C E := by
    rw [← hCE]
    intro
    simp
  ofPartialEquiv C E isClosed (by rw [← hCE, Homeomorph.isClosed_image]; exact isClosed) this.restr
    (by simp) (by simp) (by simp [hDF]) f.continuous.continuousOn f.symm.continuous.continuousOn

lemma RelCWComplex.FiniteDimensional_ofHomeomorph.{u} {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y}
    [RelCWComplex C D] (f : X ≃ₜ Y) (hCE : f '' C = E) (hDF : f '' D = F)
    [FiniteDimensional C] :
    letI := ofHomeomorph C E f hCE hDF
    FiniteDimensional E :=
  let _ := ofHomeomorph C E f hCE hDF
  {eventually_isEmpty_cell := FiniteDimensional.eventually_isEmpty_cell (C := C)}

lemma RelCWComplex.FiniteType_ofHomeomorph.{u} {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y}
    [RelCWComplex C D] (f : X ≃ₜ Y) (hCE : f '' C = E) (hDF : f '' D = F)
    [FiniteType C] :
    letI := ofHomeomorph C E f hCE hDF
    FiniteType E :=
  let _ := ofHomeomorph C E f hCE hDF
  {finite_cell := FiniteType.finite_cell (C := C)}

lemma RelCWComplex.Finite_ofHomeomorph.{u} {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y}
    [RelCWComplex C D] (f : X ≃ₜ Y) (hCE : f '' C = E) (hDF : f '' D = F)
    [Finite C] :
    letI := ofHomeomorph C E f hCE hDF
    Finite E :=
  let _ := ofHomeomorph C E f hCE hDF
  let _ := FiniteDimensional_ofHomeomorph C E f hCE hDF
  let _ := FiniteType_ofHomeomorph C E f hCE hDF
  inferInstance

/-- The image of a CW-complex under a homeomorphisms is again a CW-complex.-/
def ClasCWComplex.ofHomeomorph.{u} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] (C : Set X) (E : Set Y) [ClasCWComplex C] (f : X ≃ₜ Y)
    (hCE : f '' C = E) : ClasCWComplex E :=
  RelCWComplex.ofHomeomorph C E f hCE (image_empty ⇑f)

lemma ClasCWComplex.FiniteDimensional_ofHomeomorph.{u} {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] (C : Set X) (E : Set Y) [ClasCWComplex C] (f : X ≃ₜ Y)
    (hCE : f '' C = E) [FiniteDimensional C] :
    letI := ofHomeomorph C E f hCE
    FiniteDimensional E :=
  let _ := ofHomeomorph C E f hCE
  {eventually_isEmpty_cell := FiniteDimensional.eventually_isEmpty_cell (C := C)}

lemma ClasCWComplex.FiniteType_ofHomeomorph.{u} {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] (C : Set X) (E : Set Y) [ClasCWComplex C] (f : X ≃ₜ Y)
    (hCE : f '' C = E) [FiniteType C] :
    letI := ofHomeomorph C E f hCE
    FiniteType E :=
  let _ := ofHomeomorph C E f hCE
  {finite_cell := FiniteType.finite_cell (C := C)}

lemma ClasCWComplex.Finite_ofHomeomorph.{u} {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] (C : Set X) (E : Set Y) [ClasCWComplex C] (f : X ≃ₜ Y)
    (hCE : f '' C = E) [Finite C] :
    letI := ofHomeomorph C E f hCE
    Finite E :=
  let _ := ofHomeomorph C E f hCE
  let _ := FiniteDimensional_ofHomeomorph C E f hCE
  let _ := FiniteType_ofHomeomorph C E f hCE
  inferInstance

open Set.Notation in
open Classical in
@[simps]
def PartialEquiv.fromSet {X : Type*} (C D : Set X) (hC : C.Nonempty) (hD : D ⊆ C) :
    PartialEquiv C X :=
  letI : Nonempty C := Nonempty.to_subtype hC
  letI : Inhabited C := inhabited_of_nonempty this
  { toFun := Subtype.val
    invFun x := if h : x ∈ C then ⟨x, h⟩ else default
    source := C ↓∩ D
    target := D
    map_source' x := by simp
    map_target' y hy := by simp [hy, hD hy]
    left_inv' x := by simp
    right_inv' y hy := by simp [hy, hD hy]}

lemma PartialEquiv.continuous_fromSet {X : Type*} [TopologicalSpace X] (C D : Set X)
    (hC : C.Nonempty) (hD : D ⊆ C) : Continuous (fromSet C D hC hD) := by
  exact continuous_iff_le_induced.mpr fun U a ↦ a

lemma PartialEquiv.continuousOn_fromSet {X : Type*} [TopologicalSpace X] (C D : Set X)
    (hC : C.Nonempty) (hD : D ⊆ C) : ContinuousOn (fromSet C D hC hD).symm C := by
  simp [fromSet, continuousOn_iff_continuous_restrict, continuous_inclusion]

-- this should be generalized to the case where C can be empty
open Set.Notation in
def RelCWComplex.enlarge_of_nonempty [RelCWComplex (X := C) univ (C ↓∩ D)] (hC : IsClosed C)
    (hC2 : C.Nonempty) (hDC : D ⊆ C) :
    RelCWComplex C D where
  cell := cell (X := C) univ
  map n i := (map n i).trans' (PartialEquiv.fromSet C (map n i).target hC2
    (Subtype.coe_image_subset C (map n i).target))
    (by simp only [PartialEquiv.fromSet_source, Subtype.val_injective, preimage_image_eq])
  source_eq n i := by simp [source_eq n i]
  continuousOn n i := by
    simp only [PartialEquiv.trans', PartialEquiv.fromSet_target]
    apply Continuous.comp_continuousOn
    · exact PartialEquiv.continuous_fromSet ..
    · exact continuousOn n i
  continuousOn_symm n i := by
    simp only [PartialEquiv.trans', PartialEquiv.fromSet_target, PartialEquiv.coe_symm_mk]
    apply ContinuousOn.comp (t := (map n i).target)
    · exact continuousOn_symm n i
    · apply ContinuousOn.mono (s := C)
      · exact PartialEquiv.continuousOn_fromSet C (Subtype.val '' (map n i).target) hC2
          (Subtype.coe_image_subset C (map n i).target)
      · simp
    · simp only [mapsTo', PartialEquiv.fromSet_symm_apply]
      intro x
      simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right, forall_exists_index,
        and_imp]
      intro y hy hy2 hyx
      simp_all
  pairwiseDisjoint' := by
    have := pairwiseDisjoint' (X := C) (C := univ)
    simp_all only [PairwiseDisjoint, Set.Pairwise, mem_univ, ne_eq, Function.onFun,
      forall_const, PartialEquiv.coe_trans, Function.comp_apply,
      PartialEquiv.fromSet_apply]
    intro x y ne
    suffices  Disjoint (Subtype.val '' (↑(map x.fst x.snd) '' ball 0 1))
        (Subtype.val '' (↑(map y.fst y.snd) '' ball 0 1)) by
      rw [image_image, image_image] at this
      exact this
    apply disjoint_image_of_injective Subtype.val_injective
    exact this ne
  disjointBase' n i := by
    have h := disjointBase' (X := C) (C := univ) n i
    have : D = Subtype.val '' C ↓∩ D := by
      simp only [Subtype.image_preimage_coe, right_eq_inter, hDC]
    simp only [PartialEquiv.trans', Function.comp_apply, PartialEquiv.fromSet_apply]
    nth_rw 2 [this]
    rw [← image_image]
    apply disjoint_image_of_injective Subtype.val_injective
    exact h
  mapsto n i := by
    obtain ⟨I, hI⟩ := mapsto (X := C) (C := univ) n i
    use I
    simp only [PartialEquiv.trans', mapsTo', image_comp] at hI ⊢
    apply subset_trans (image_mono hI)
    simp_rw [image_union, image_iUnion]
    apply union_subset_union_left
    apply subset_of_eq
    ext
    simp only [PartialEquiv.fromSet_apply, Subtype.image_preimage_coe, mem_inter_iff,
      and_iff_right_iff_imp]
    exact fun h ↦ hDC h
  closed' A hAC := by
    intro ⟨hA1, hA2⟩
    rw [← inter_eq_right.2 hAC, ← hC.inter_preimage_val_iff]
    rw [closed (X := C) (C := univ) _ (subset_univ _)]
    constructor
    · intro n i
      rw [Topology.IsClosedEmbedding.isClosed_iff_image_isClosed
        hC.isClosedEmbedding_subtypeVal]
      simp only [image_val_inter, Subtype.image_preimage_coe, inter_eq_right.2 hAC]
      convert hA1 n i
      ext x
      simp [closedCell, PartialEquiv.trans']
    · rw [Topology.IsClosedEmbedding.isClosed_iff_image_isClosed
        hC.isClosedEmbedding_subtypeVal]
      simp [inter_eq_right.2 hAC, inter_eq_right.2 hDC, hA2]
  isClosedBase := by
    rw [← inter_eq_right.2 hDC, ← hC.inter_preimage_val_iff]
    exact isClosedBase univ
  union' := by
    have := union' (X := C) (C := univ)
    rw [← image_eq_image Subtype.val_injective] at this
    simp only [image_val_union, Subtype.image_preimage_coe, inter_eq_right.2 hDC, image_val_iUnion,
      image_univ, Subtype.range_coe_subtype, setOf_mem_eq] at this
    nth_rw 127 [← this]
    congrm D ∪ ⋃ n, ⋃ i, ?_
    ext
    simp

open Set.Notation in
open Classical in
def RelCWComplex.enlarge [RelCWComplex (X := C) univ (C ↓∩ D)] (hC : IsClosed C)
    (hDC : D ⊆ C) : RelCWComplex C D :=
  if h : C.Nonempty then enlarge_of_nonempty hC h hDC else sorry

open Set.Notation in
open Classical in
@[simps]
def PartialEquiv.restrictImage {X Y : Type*} (e : PartialEquiv X Y) (A : Set Y)
    (heA : e.target ⊆ A) (hA : A.Nonempty) : PartialEquiv X A :=
  letI : Nonempty A := Nonempty.to_subtype hA
  letI : Inhabited A := inhabited_of_nonempty this
  { toFun x := if h : e x ∈ A then ⟨e x, h⟩ else default
    invFun := e.symm ∘ Subtype.val
    source := e.source
    target := A ↓∩ e.target
    map_source' x hx := by simp_all [heA (e.map_source' hx)]
    map_target' y hy := by simp_all [e.map_target' hy]
    left_inv' x hx := by simp_all [heA (e.map_source' hx)]
    right_inv' y hy := by simp_all}

-- this proof can probably be done nicer
lemma PartialEquiv.restrictImage_image_eq {X Y : Type*} (e : PartialEquiv X Y) (B : Set X)
    (A : Set Y) (hB : e '' B ⊆ A) (heA : e.target ⊆ A) (hA : A.Nonempty) :
    (e.restrictImage A heA hA) '' B = e '' B := by
  ext x
  simp only [restrictImage_apply, mem_image, exists_exists_and_eq_and]
  constructor
  · intro ⟨b, hb, hbx⟩
    use b
    simp_all [hB (mem_image_of_mem _ hb)]
  · intro ⟨b, hb, hbx⟩
    use b
    have := hB (mem_image_of_mem _ hb)
    simp_all

open Set.Notation in
def RelCWComplex.restrict [RelCWComplex C D] (Y : Set X) (hCY : C ⊆ Y) (hC : C.Nonempty) :
    RelCWComplex (X := Y) (Y ↓∩ C) (Y ↓∩ D) where
  cell := cell C
  map n i := (map n i).restrictImage Y (by
    refine subset_trans ?_ hCY
    rw [← PartialEquiv.image_source_eq_target, source_eq]
    exact openCell_subset_complex (C := C) n i)
    (hC.mono hCY)
  source_eq n i := by simp [source_eq]
  continuousOn n i := by
    simp only [PartialEquiv.restrictImage, continuousOn_iff_continuous_restrict]
    have : ∀ x (_ : x ∈ closedBall 0 1), map n i x ∈ Y := by
      intro x hx
      apply hCY
      exact closedCell_subset_complex _ _ (mem_image_of_mem _ hx)
    apply Continuous.congr
      (f := fun (x : closedBall 0 1) ↦ (⟨map n i x, this x.1 x.2⟩ : Y))
    · apply Continuous.subtype_mk
      apply Continuous.congr (f := (closedBall 0 1).restrict (map n i))
      · rw [← continuousOn_iff_continuous_restrict]
        exact continuousOn n i
      · intro
        simp
    · intro ⟨x, hx⟩
      simp [this x hx]
  continuousOn_symm n i := by
    simp only [PartialEquiv.restrictImage, PartialEquiv.coe_symm_mk]
    apply ContinuousOn.image_comp_continuous
    · have : (map n i).target ⊆ Y := by
        refine subset_trans ?_ hCY
        rw [← PartialEquiv.image_source_eq_target, source_eq]
        exact openCell_subset_complex (C := C) n i
      simp only [Subtype.image_preimage_coe, inter_eq_right.2 this]
      exact continuousOn_symm n i
    · exact continuous_subtype_val
  pairwiseDisjoint' := by
    have h := pairwiseDisjoint' (C := C)
    simp only [PairwiseDisjoint, Set.Pairwise, mem_univ, ne_eq, Function.onFun, forall_const] at h ⊢
    intro x y hxy
    apply Disjoint.of_image (f := Subtype.val)
    have hx : map x.1 x.2 '' ball 0 1 ⊆ Y := (openCell_subset_complex x.1 x.2).trans hCY
    have hy : map y.1 y.2 '' ball 0 1 ⊆ Y := (openCell_subset_complex y.1 y.2).trans hCY
    rw [(map x.1 x.2).restrictImage_image_eq _ _ hx, (map y.1 y.2).restrictImage_image_eq _ _ hy]
    exact h hxy
  disjointBase' n i := by
    apply Disjoint.of_image (f := Subtype.val)
    have h1 : D ⊆ Y := subset_trans base_subset_complex hCY
    have h2 : (map n i) '' ball 0 1 ⊆ Y := (openCell_subset_complex n i).trans hCY
    simp only [Subtype.image_preimage_coe, inter_eq_right.2 h1,
      (map n i).restrictImage_image_eq _ _ h2]
    exact disjointBase' n i
  mapsto n i := by
    obtain ⟨I, hI⟩ := mapsto n i
    use I
    rw [mapsTo'] at hI ⊢
    rw [← image_subset_image_iff Subtype.val_injective]
    simp_rw [image_union, image_iUnion]
    have h1 : map n i '' sphere 0 1 ⊆ Y := (cellFrontier_subset_complex n i).trans hCY
    have h2 : ∀ m (j : cell C m), map m j '' closedBall 0 1 ⊆ Y :=
      fun m j ↦ (closedCell_subset_complex m j).trans hCY
    simp_rw [PartialEquiv.restrictImage_image_eq _ _ _ h1,
      fun m j ↦ PartialEquiv.restrictImage_image_eq _ _ _ (h2 m j),
      Subtype.image_preimage_coe, inter_eq_right.2 (base_subset_complex.trans hCY)]
    exact hI
  closed' A hA := by
    intro ⟨hA1, hA2⟩
    suffices IsClosed (Subtype.val '' A) by
      rw [← preimage_image_eq A Subtype.val_injective]
      exact this.preimage_val
    have hAC: Subtype.val '' A ⊆ C := by
      rw [← inter_eq_left.2 hCY]
      nth_rw 3 [← Subtype.range_val (s := Y)]
      rw [← image_preimage_eq_inter_range]
      exact image_mono hA
    rw [closed (C := C) _ hAC]
    -- how do I get back to the preimage now?
    constructor
    · sorry
    · rw [← inter_eq_left.2 (base_subset_complex.trans hCY)]
      nth_rw 3 [← Subtype.range_val (s := Y)]
      rw [← image_preimage_eq_inter_range, ← image_inter Subtype.val_injective]
      sorry
  isClosedBase := (isClosedBase C).preimage continuous_subtype_val
  union' := by
    rw [← image_eq_image Subtype.val_injective]
    simp_rw [image_union, image_iUnion]
    have h : ∀ m (j : cell C m), map m j '' closedBall 0 1 ⊆ Y :=
      fun m j ↦ (closedCell_subset_complex m j).trans hCY
    simp_rw [fun m j ↦ PartialEquiv.restrictImage_image_eq _ _ _ (h m j),
      Subtype.image_preimage_coe, inter_eq_right.2 (base_subset_complex.trans hCY),
      inter_eq_right.2 hCY]
    exact union'

open Set.Notation in
def RelCWComplex.univSelf [RelCWComplex C D] (hC : C.Nonempty) :
    RelCWComplex (univ : Set C) (C ↓∩ D) :=
  letI := RelCWComplex.restrict C Subset.rfl hC
  ofEq (C ↓∩ C) (C ↓∩ D) (E := (Set.univ : Set C)) (by simp) rfl

namespace ClasCWComplex

export RelCWComplex (ofEq finiteDimensional_ofEq finiteType_ofEq finite_ofEq)

end ClasCWComplex
