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

namespace Topology

variable {X : Type*} [t : TopologicalSpace X] {C D : Set X}

section

/-- Every finite set is a CW complex. -/
def CWComplex.ofFiniteSet {C : Set X} (h : C.Finite) : CWComplex C := mkFinite C
  (cell := fun n ↦ match n with
    | 0 => C
    | (_ + 1) => PEmpty)
  (map := fun n i ↦ match n with
    | 0 => PartialEquiv.single ![] i
    | (_ + 1) => i.elim)
  (eventually_isEmpty_cell := by
    rw [Filter.eventually_atTop]
    use 1
    intro b beq1
    simp only
    split
    · contradiction
    · infer_instance)
  (finite_cell := fun n ↦ match n with
    | 0 => h
    | (_ + 1) => inferInstance)
  (source_eq := fun n i ↦ match n with
    | 0 => by
      simp [PartialEquiv.single, ball, Matrix.empty_eq, eq_univ_iff_forall]
    | (_ + 1) => i.elim)
  (continuousOn := fun n i ↦ match n with
    | 0 => continuousOn_const
    | (m + 1) => i.elim)
  (continuousOn_symm := fun n i ↦ match n with
    | 0 => continuousOn_const
    | (_ + 1) => i.elim)
  (pairwiseDisjoint' := by
    simp_rw [PairwiseDisjoint, Set.Pairwise, Function.onFun]
    exact fun ⟨n, j⟩ _ ⟨m, i⟩ _ ne ↦  match n with
      | 0 => match m with
        | 0 => by simp_all [Subtype.coe_ne_coe]
        | (_ + 1) => i.elim
      | (_ + 1) => j.elim)
  (mapsto := fun n i ↦ match n with
    | 0 => by simp [Matrix.zero_empty, sphere_eq_empty_of_subsingleton]
    | (_ + 1) => i.elim)
  (union' := by
    ext x
    simp only [mem_iUnion]
    constructor
    · intro ⟨n, i, hi⟩
      exact match n with
        | 0 => by simp_all
        | (_ + 1) => i.elim
    · intro hx
      use 0, ⟨x, hx⟩
      simp)

--split this lemma into two
lemma CWComplex.ofFiniteSet_cell {C : Set X} (h : C.Finite) {n : ℕ} :
    letI := ofFiniteSet h
    cell C n =  match n with | 0 => C | (_ + 1) => PEmpty :=
  rfl

--only first case
lemma CWComplex.ofFiniteSet_map {C : Set X} (h : C.Finite) {n : ℕ}
    {i : match n with | 0 => C | (_ + 1) => PEmpty} :
    letI := ofFiniteSet h
    map (C := C) n i =
      match n, i with | 0, i => PartialEquiv.single ![] i | (_ + 1), i => PEmpty.elim i :=
  rfl

lemma CWComplex.ofFiniteSet_map' {C : Set X} (h : C.Finite)
    {i : C} :
    letI := ofFiniteSet h
    map (C := C) 0 i =
      PartialEquiv.single (β := X) ![] i  := by
  rfl

/-- The CW-complex on a finite set is finite. -/
lemma CWComplex.finite_ofFiniteSet (C : Set X) (h : C.Finite) :
    letI := ofFiniteSet h
    Finite C :=
  finite_mkFinite ..

-- delete the next three

instance CWComplex.instFiniteSet (C : Set X) [_root_.Finite C] : CWComplex C :=
  ofFiniteSet (by assumption)

@[simp]
lemma CWComplex.instFiniteSet_eq_ofFiniteSet (C : Set X) [_root_.Finite C] :
    instFiniteSet C = ofFiniteSet (by assumption) :=
  rfl

/-- The CW-complex on a finite set is finite. -/
instance CWComplex.finite_instFiniteSet (C : Set X) [_root_.Finite C] :
    Finite C :=
  finite_ofFiniteSet C (by assumption)

@[simps -isSimp]
def RelCWComplex.ofEq {X : Type*} [TopologicalSpace X] (C D : Set X)
    {E F : Set X} [RelCWComplex C D] (hCE : C = E) (hDF : D = F) : RelCWComplex E F where
  cell := cell C
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  disjointBase' := hDF ▸ disjointBase'
  mapsTo := hDF ▸ mapsTo
  closed' := hCE ▸ hDF ▸ closed'
  isClosedBase := hDF ▸ isClosedBase C
  union' := hCE ▸ hDF ▸ union'

@[simps! -isSimp]
def CWComplex.ofEq {X : Type*} [TopologicalSpace X] (C : Set X)
    {E : Set X} [CWComplex C] (hCE : C = E) : CWComplex E :=
  (RelCWComplex.ofEq C ∅ hCE rfl).toCWComplex

lemma RelCWComplex.finiteDimensional_ofEq {X : Type*} [TopologicalSpace X] (C D : Set X)
    {E F : Set X} [RelCWComplex C D] [FiniteDimensional C] (hCE : C = E) (hDF : D = F) :
    letI _ := ofEq C D hCE hDF
    FiniteDimensional E :=
  let _ := ofEq C D hCE hDF
  {eventually_isEmpty_cell := FiniteDimensional.eventually_isEmpty_cell (C := C)}

lemma CWComplex.finiteDimensional_ofEq {X : Type*} [TopologicalSpace X] (C : Set X)
    {E : Set X} [CWComplex C] [FiniteDimensional C] (hCE : C = E) :
    letI _ := ofEq C hCE
    FiniteDimensional E :=
  let _ := ofEq C hCE
  {eventually_isEmpty_cell := FiniteDimensional.eventually_isEmpty_cell (C := C)}

lemma RelCWComplex.finiteType_ofEq {X : Type*} [TopologicalSpace X] (C D : Set X)
    {E F : Set X} [RelCWComplex C D] [FiniteType C] (hCE : C = E) (hDF : D = F) :
    letI _ := ofEq C D hCE hDF
    FiniteType E :=
  let _ := ofEq C D hCE hDF
  {finite_cell := FiniteType.finite_cell (C := C)}

lemma CWComplex.finiteType_ofEq {X : Type*} [TopologicalSpace X] (C : Set X)
    {E : Set X} [CWComplex C] [FiniteType C] (hCE : C = E) :
    letI _ := ofEq C hCE
    FiniteType E :=
  let _ := ofEq C hCE
  {finite_cell := FiniteType.finite_cell (C := C)}

lemma RelCWComplex.finite_ofEq {X : Type*} [TopologicalSpace X] (C D : Set X)
    {E F : Set X} [RelCWComplex C D] [Finite C] (hCE : C = E) (hDF : D = F) :
    letI _ := ofEq C D hCE hDF
    Finite E :=
  let _ := ofEq C D hCE hDF
  let _ := finiteDimensional_ofEq C D hCE hDF
  let _ := finiteType_ofEq C D hCE hDF
  inferInstance

lemma CWComplex.finite_ofEq {X : Type*} [TopologicalSpace X] (C : Set X)
    {E : Set X} [CWComplex C] [Finite C] (hCE : C = E) :
    letI _ := ofEq C hCE
    Finite E :=
  let _ := ofEq C hCE
  let _ := finiteDimensional_ofEq C hCE
  let _ := finiteType_ofEq C hCE
  inferInstance

variable [T2Space X]

/-- The union of two disjoint CW-complexes is again a CW-complex. -/
@[simps -isSimp]
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
      · exact (disjoint_openCell_of_ne (by aesop)).inter_eq
      · exact subset_eq_empty (inter_subset_inter (openCell_subset_complex n cn)
          (openCell_subset_complex m cm)) (disjoint_iff_inter_eq_empty.1 disjoint)
    rcases cm with cm | cm
    · exact subset_eq_empty (inter_subset_inter (openCell_subset_complex n cn)
        (openCell_subset_complex m cm)) (disjoint_iff_inter_eq_empty.1 (disjoint_comm.1 disjoint))
    · exact (disjoint_openCell_of_ne (by aesop)).inter_eq
  disjointBase' := by
    intro n cn
    rcases cn with cn | cn
    · exact (disjointBase (C := C) (D := D) _ _).union_right
       (disjoint.mono (openCell_subset_complex _ _) base_subset_complex)
    · exact (disjoint.symm.mono (openCell_subset_complex n cn) base_subset_complex).union_right
        (disjointBase (C := E) (D := F) _ _)
  mapsTo n i := by
    classical
    rcases i with ic | id
    · obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell n ic
      use fun m ↦ (I m).image Sum.inl
      rw [Set.mapsTo', union_assoc]
      apply hI.trans
      apply union_subset_union_right
      apply subset_union_of_subset_right
      simp only [Finset.mem_image, iUnion_exists, biUnion_and', iUnion_iUnion_eq_right]
      rfl
    · obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell n id
      use fun m ↦ (I m).image Sum.inr
      rw [Set.mapsTo', union_comm D, union_assoc]
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
        exact SeparatedNhds.isClosed_left_of_isClosed_union this h2
    · rw [closed E (A ∩ E) inter_subset_right]
      constructor
      · intro n j
        rw [inter_right_comm]
        exact (h1 n (Sum.inr j)).inter (isClosed (D := F))
      · rw [inter_assoc, (inter_eq_right (s := E)).2 base_subset_complex]
        exact SeparatedNhds.isClosed_right_of_isClosed_union this h2
  isClosedBase := (isClosedBase C).union (isClosedBase E)
  union' := by
    simp_rw [← union (C := C) (D := D), ← union (C := E) (D := F), ← union_assoc,
      union_right_comm D _ F, union_assoc (D ∪ F), ← iUnion_union_distrib, iUnion_sum]
    rfl

@[simps! -isSimp]
def CWComplex.disjointUnion {E : Set X} [CWComplex C] [CWComplex E]
    (hCE : Disjoint C E) : CWComplex (C ∪ E) :=
  letI := RelCWComplex.disjointUnion hCE (SeparatedNhds.empty_left ∅)
  letI := RelCWComplex.ofEq (C ∪ E) (∅ ∪ ∅) rfl (empty_union ∅)
  RelCWComplex.toCWComplex (C ∪ E)

lemma RelCWComplex.finiteDimensional_disjointUnion [RelCWComplex C D] {E F : Set X}
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

lemma CWComplex.finiteDimensional_disjointUnion [CWComplex C] {E : Set X}
    [CWComplex E] [FiniteDimensional C] [FiniteDimensional E]
    (disjoint : Disjoint C E) :
    letI _complex := disjointUnion disjoint
    FiniteDimensional (C ∪ E) :=
  let _complex := disjointUnion disjoint
  {eventually_isEmpty_cell := by
    have h1 := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅)
    have h2 := FiniteDimensional.eventually_isEmpty_cell (C := E) (D := ∅)
    simp only [Filter.eventually_atTop, ge_iff_le, RelCWComplex.ofEq_cell,
      RelCWComplex.disjointUnion_cell, isEmpty_sum] at h1 h2 ⊢
    obtain ⟨N1, hN1⟩ := h1
    obtain ⟨N2, hN2⟩ := h2
    use N1 ⊔ N2
    intro b hN1N2b
    exact ⟨hN1 b (le_of_max_le_left hN1N2b), hN2 b (le_of_max_le_right hN1N2b)⟩}

lemma RelCWComplex.finiteType_disjointUnion [RelCWComplex C D] {E F : Set X}
    [RelCWComplex E F] [FiniteType C] [FiniteType E] (disjoint : Disjoint C E)
    (hDF : SeparatedNhds D F) :
    letI _complex := RelCWComplex.disjointUnion disjoint hDF
    FiniteType (C ∪ E) :=
  let _complex := RelCWComplex.disjointUnion disjoint hDF
  {finite_cell := fun n ↦ by
    simp only [RelCWComplex.disjointUnion_cell]
    infer_instance}

lemma CWComplex.finiteType_disjointUnion [CWComplex C] {E : Set X} [CWComplex E]
    [FiniteType C]
    [FiniteType E] (disjoint : Disjoint C E) :
    letI _complex := disjointUnion disjoint
    FiniteType (C ∪ E) :=
  let _complex := disjointUnion disjoint
  {finite_cell := fun n ↦ by
    simp only [RelCWComplex.ofEq_cell, RelCWComplex.disjointUnion_cell]
    infer_instance}

lemma RelCWComplex.finite_disjointUnion [RelCWComplex C D] {E F : Set X}
    [RelCWComplex E F] [Finite C] [Finite E]
    (disjoint : Disjoint C E) (hDF : SeparatedNhds D F) :
    letI _complex := RelCWComplex.disjointUnion disjoint hDF
    Finite (C ∪ E) :=
  let _complex := RelCWComplex.disjointUnion disjoint hDF
  let _finiteDimensional := finiteDimensional_disjointUnion disjoint hDF
  let _finiteType := finiteType_disjointUnion disjoint hDF
  inferInstance

lemma CWComplex.finite_disjointUnion [CWComplex C] {E : Set X}
    [CWComplex E] [Finite C] [Finite E] (disjoint : Disjoint C E) :
    letI _complex := disjointUnion disjoint
    Finite (C ∪ E) :=
  let _complex := disjointUnion disjoint
  let _finiteDimensional := finiteDimensional_disjointUnion disjoint
  let _finiteType := finiteType_disjointUnion disjoint
  inferInstance

end

@[simps -isSimp]
def RelCWComplex.attachCell.{u} {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X)
    {D : Set X} [RelCWComplex C D]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
    (continuousOn' : ContinuousOn map' (closedBall 0 1))
    (continuousOn_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (disjointBase' : Disjoint (map' '' ball 0 1) D)
    (mapsTo : ∃ I : Π m, Finset (cell C m),
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
  mapsTo m i := match i with
    | .inl j => by
      classical
      obtain ⟨I, hI⟩ := RelCWComplex.mapsTo m j
      use fun m ↦ (I m).image .inl
      simp [hI]
    | .inr hj => by
      classical
      subst hj
      obtain ⟨I, hI⟩ := mapsTo
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

lemma RelCWComplex.finiteDimensional_attachCell {X : Type*} [TopologicalSpace X] [T2Space X]
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
  relax the condition `mapsTo`. -/
@[simps! -isSimp]
def RelCWComplex.attachCellFiniteType.{u} {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) {D : Set X} [RelCWComplex C D] [FiniteType C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
    (continuousOn' : ContinuousOn map' (closedBall 0 1))
    (continuousOn_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (disjointBase' : Disjoint (map' '' ball 0 1) D)
    (mapsTo : MapsTo map' (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell C m), closedCell m j)) :
    RelCWComplex (map' '' closedBall 0 1 ∪ C) D := RelCWComplex.attachCell C map'
  (source_eq' := source_eq')
  (continuousOn' := continuousOn')
  (continuousOn_symm' := continuousOn_symm')
  (disjoint' := disjoint')
  (disjointBase' := disjointBase')
  (mapsTo := by
    use fun m ↦ finite_univ.toFinset
    simpa)

lemma RelCWComplex.finiteDimensional_attachCellFiniteType {X : Type*} [TopologicalSpace X]
    [T2Space X] (C : Set X) {D : Set X} [RelCWComplex C D] [Finite C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
    (cont' : ContinuousOn map' (closedBall 0 1))
    (cont_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (disjointBase' : Disjoint (map' '' ball 0 1) D)
    (mapsTo : MapsTo map' (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell C m), closedCell m j)) :
    letI _complex := attachCellFiniteType C map' source_eq' cont' cont_symm'
      disjoint' disjointBase' mapsTo
    FiniteDimensional (map' '' closedBall 0 1 ∪ C) :=
  let _complex := attachCellFiniteType C map' source_eq' cont' cont_symm'
      disjoint' disjointBase' mapsTo
  {eventually_isEmpty_cell := by
    have h := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)
    simp only [Filter.eventually_atTop, ge_iff_le, RelCWComplex.attachCell_cell, isEmpty_psum,
      isEmpty_Prop] at h ⊢
    obtain ⟨N, hN⟩ := h
    use N ⊔ n.succ
    intro b hb
    exact ⟨hN b (le_of_max_le_left hb) , Nat.ne_of_lt' (le_of_max_le_right hb)⟩}

lemma RelCWComplex.finiteType_attachCellFiniteType {X : Type*} [TopologicalSpace X]
    [T2Space X] (C : Set X) {D : Set X} [RelCWComplex C D] [FiniteType C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
    (continuousOn' : ContinuousOn map' (closedBall 0 1))
    (continuousOn_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (disjointBase' : Disjoint (map' '' ball 0 1) D)
    (mapsTo : MapsTo map' (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell C m), closedCell m j)) :
    letI _complex := attachCellFiniteType C map' source_eq' continuousOn' continuousOn_symm'
      disjoint' disjointBase' mapsTo
    FiniteType (map' '' closedBall 0 1 ∪ C) :=
  let _complex := attachCellFiniteType C map' source_eq' continuousOn' continuousOn_symm'
      disjoint' disjointBase' mapsTo
  {finite_cell := by
    intro m
    simp only [attachCell_cell]
    infer_instance}

lemma RelCWComplex.finite_attachCellFiniteType {X : Type*} [TopologicalSpace X]
    [T2Space X] (C : Set X) {D : Set X} [RelCWComplex C D] [Finite C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
    (cont' : ContinuousOn map' (closedBall 0 1))
    (cont_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (disjointBase' : Disjoint (map' '' ball 0 1) D)
    (mapsTo : MapsTo map' (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell C m), closedCell m j)) :
    letI _complex := attachCellFiniteType C map' source_eq' cont' cont_symm'
      disjoint' disjointBase' mapsTo
    Finite (map' '' closedBall 0 1 ∪ C) :=
  let _complex := attachCellFiniteType C map' source_eq' cont' cont_symm'
      disjoint' disjointBase' mapsTo
  let _finiteDimensional := finiteDimensional_attachCellFiniteType C map'
      source_eq' cont' cont_symm' disjoint' disjointBase' mapsTo
  let _finiteType := finiteType_attachCellFiniteType C map'
      source_eq' cont' cont_symm' disjoint' disjointBase' mapsTo
  inferInstance

@[simps! -isSimp]
def CWComplex.attachCell.{u} {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X)
    [CWComplex C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
    (continuousOn' : ContinuousOn map' (closedBall 0 1))
    (continuousOn_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (mapsTo : ∃ I : Π m, Finset (cell C m),
      MapsTo map' (sphere 0 1) (⋃ (m < n) (j ∈ I m), closedCell m j)) :
    CWComplex (map' '' closedBall 0 1 ∪ C) :=
  (RelCWComplex.attachCell C map'
    (source_eq' := source_eq')
    (continuousOn' := continuousOn')
    (continuousOn_symm' := continuousOn_symm')
    (disjoint' := disjoint')
    (disjointBase' := disjoint_empty _)
    (mapsTo := by
      simp_rw [empty_union]
      exact mapsTo)).toCWComplex

lemma CWComplex.finiteDimensional_attachCell {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] [FiniteDimensional C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
    (cont' : ContinuousOn map' (closedBall 0 1))
    (cont_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (mapsTo : ∃ I : Π m, Finset (cell C m),
      MapsTo map' (sphere 0 1) (⋃ (m < n) (j ∈ I m), closedCell m j)) :
    letI _complex := attachCell C map' source_eq' cont' cont_symm' disjoint' mapsTo
    FiniteDimensional (map' '' closedBall 0 1 ∪ C) :=
  let _complex := attachCell C map' source_eq' cont' cont_symm' disjoint' mapsTo
  {eventually_isEmpty_cell := by
    have h := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅)
    simp only [Filter.eventually_atTop, ge_iff_le, RelCWComplex.ofEq_cell,
      RelCWComplex.attachCell_cell, isEmpty_psum, isEmpty_Prop] at h ⊢
    obtain ⟨N, hN⟩ := h
    use N ⊔ n.succ
    intro b hb
    exact ⟨hN b (le_of_max_le_left hb) , Nat.ne_of_lt' (le_of_max_le_right hb)⟩}

@[simps! -isSimp]
def CWComplex.attachCellFiniteType.{u} {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X)
    [CWComplex C] [FiniteType C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
    (continuousOn' : ContinuousOn map' (closedBall 0 1))
    (continuousOn_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (mapsTo : MapsTo map' (sphere 0 1) (⋃ (m < n) (j : cell C m), closedCell m j)) :
    CWComplex (map' '' closedBall 0 1 ∪ C) := attachCell C map'
  (source_eq' := source_eq')
  (continuousOn' := continuousOn')
  (continuousOn_symm' := continuousOn_symm')
  (disjoint' := disjoint')
  (mapsTo := by
    use fun m ↦ finite_univ.toFinset
    simpa)

lemma CWComplex.finiteType_attachCellFiniteType {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] [FiniteType C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
    (continuousOn' : ContinuousOn map' (closedBall 0 1))
    (continuousOn_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (mapsTo : MapsTo map' (sphere 0 1) (⋃ (m < n) (j : cell C m), closedCell m j)) :
  letI _complex := attachCellFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
    mapsTo
  FiniteType (map' '' closedBall 0 1 ∪ C) :=
  let _complex := attachCellFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
    mapsTo
  {finite_cell := by
    intro m
    simp only [RelCWComplex.ofEq_cell, RelCWComplex.attachCell_cell]
    infer_instance}

lemma CWComplex.finiteDimensional_attachCellFiniteType {X : Type*} [TopologicalSpace X]
    [T2Space X] (C : Set X) [CWComplex C] [Finite C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
    (continuousOn' : ContinuousOn map' (closedBall 0 1))
    (continuousOn_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (mapsTo : MapsTo map' (sphere 0 1) (⋃ (m < n) (j : cell C m), closedCell m j)) :
  letI _complex := attachCellFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
    mapsTo
  FiniteDimensional (map' '' closedBall 0 1 ∪ C) :=
  let _complex := attachCellFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
    mapsTo
  {eventually_isEmpty_cell := by
    have h := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅)
    simp only [Filter.eventually_atTop, ge_iff_le, RelCWComplex.ofEq_cell,
      RelCWComplex.attachCell_cell, isEmpty_psum, isEmpty_Prop] at h ⊢
    obtain ⟨N, hN⟩ := h
    use N ⊔ n.succ
    intro b hb
    exact ⟨hN b (le_of_max_le_left hb) , Nat.ne_of_lt' (le_of_max_le_right hb)⟩}

lemma CWComplex.finite_attachCellFiniteType {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] [Finite C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
    (continuousOn' : ContinuousOn map' (closedBall 0 1))
    (continuousOn_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (mapsTo : MapsTo map' (sphere 0 1) (⋃ (m < n) (j : cell C m), closedCell m j)) :
  letI _complex := attachCellFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
    mapsTo
  Finite (map' '' closedBall 0 1 ∪ C) :=
  let _complex := attachCellFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
    mapsTo
  let _finiteDimensional := finiteDimensional_attachCellFiniteType C map' source_eq'
    continuousOn' continuousOn_symm' disjoint' mapsTo
  let _finiteType := finiteType_attachCellFiniteType C map' source_eq' continuousOn'
    continuousOn_symm' disjoint' mapsTo
  inferInstance

@[simps -isSimp]
def RelCWComplex.attachCells.{u} {X : Type u} [TopologicalSpace X] [T2Space X] (C D : Set X)
    [RelCWComplex C D] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (disjointBase' : ∀ i, Disjoint (map' i '' ball 0 1) D)
    (mapsTo : ∀ i, ∃ I : Π m, Finset (cell C m),
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
  mapsTo m j := match m, j with
    | m, .inl j => by
      classical
      obtain ⟨I, hI⟩ := RelCWComplex.mapsTo m j
      use fun l ↦ (I l).image .inl
      simp [hI]
    | _, .inr ⟨j, rfl⟩ => by
      classical
      obtain ⟨I, hI⟩ := mapsTo j
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

lemma RelCWComplex.finiteDimensional_attachCells.{u} {X : Type u} [TopologicalSpace X]
    [T2Space X] (C D : Set X) [RelCWComplex C D] [FiniteDimensional C]
    {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (disjointBase' : ∀ i, Disjoint (map' i '' ball 0 1) D)
    (mapsTo : ∀ i, ∃ I : Π m, Finset (cell C m),
      MapsTo (map' i) (sphere 0 1) (D ∪ ⋃ (m < n) (j ∈ I m), closedCell m j)) :
    letI := attachCells C D map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' disjointBase' mapsTo
    FiniteDimensional ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  let _ := attachCells C D map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' disjointBase' mapsTo
  {eventually_isEmpty_cell := by
    have h := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)
    simp only [Filter.eventually_atTop, ge_iff_le, attachCells_cell, isEmpty_sum, isEmpty_pprod,
      isEmpty_Prop] at h ⊢
    obtain ⟨N, hN⟩ := h
    use N ⊔ n.succ
    intro b hb
    exact ⟨hN b (le_of_max_le_left hb), .inr (Nat.ne_of_lt' (le_of_max_le_right hb))⟩}

/-- A version of `RelCWComplex.attachCells`. Assuming that the CW complex is of finite type lets us
  relax the condition `mapsTo`. -/
@[simps! -isSimp]
def RelCWComplex.attachCellsFiniteType.{u} {X : Type u} [TopologicalSpace X] [T2Space X]
    (C D : Set X) [RelCWComplex C D] [FiniteType C] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (disjointBase' : ∀ i, Disjoint (map' i '' ball 0 1) D)
    (mapsTo : ∀ i, MapsTo (map' i) (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell C m) , closedCell m j)) :
    RelCWComplex ((⋃ i, map' i '' closedBall 0 1) ∪ C) D :=
  attachCells C D map' source_eq' continuousOn' continuousOn_symm' disjoint' disjoint''
    disjointBase'
    (mapsTo := by
      intro i
      use fun m ↦ finite_univ.toFinset
      simp [mapsTo i])

lemma RelCWComplex.finiteDimensional_attachCellsFiniteType.{u} {X : Type u} [TopologicalSpace X]
    [T2Space X] (C D : Set X) [RelCWComplex C D] [Finite C] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (disjointBase' : ∀ i, Disjoint (map' i '' ball 0 1) D)
    (mapsTo : ∀ i, MapsTo (map' i) (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell C m) , closedCell m j)) :
    letI := attachCellsFiniteType C D map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' disjointBase' mapsTo
    FiniteDimensional ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  let _ := attachCellsFiniteType C D map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' disjointBase' mapsTo
  {eventually_isEmpty_cell := by
    have h := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)
    simp only [Filter.eventually_atTop, ge_iff_le, attachCells_cell, isEmpty_sum, isEmpty_pprod,
      isEmpty_Prop] at h ⊢
    obtain ⟨N, hN⟩ := h
    use N ⊔ n.succ
    intro b hb
    exact ⟨hN b (le_of_max_le_left hb), .inr (Nat.ne_of_lt' (le_of_max_le_right hb))⟩}

lemma RelCWComplex.finiteType_attachCellsFiniteType.{u} {X : Type u} [TopologicalSpace X]
    [T2Space X] (C D : Set X) [RelCWComplex C D] [FiniteType C] {n : ℕ} {ι : Type u}
    [_root_.Finite ι] (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (disjointBase' : ∀ i, Disjoint (map' i '' ball 0 1) D)
    (mapsTo : ∀ i, MapsTo (map' i) (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell C m) , closedCell m j)) :
    letI := attachCellsFiniteType C D map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' disjointBase' mapsTo
    FiniteType ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  let _ := attachCellsFiniteType C D map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' disjointBase' mapsTo
  {finite_cell := by
    intro m
    simp only [attachCells_cell]
    infer_instance}

lemma RelCWComplex.finite_attachCellsFiniteType.{u} {X : Type u} [TopologicalSpace X]
    [T2Space X] (C D : Set X) [RelCWComplex C D] [Finite C] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (disjointBase' : ∀ i, Disjoint (map' i '' ball 0 1) D)
    (mapsTo : ∀ i, MapsTo (map' i) (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell C m) , closedCell m j)) :
    letI := attachCellsFiniteType C D map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' disjointBase' mapsTo
    Finite ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  let _ := attachCellsFiniteType C D map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' disjointBase' mapsTo
  let _ := finiteDimensional_attachCellsFiniteType C D map' source_eq' continuousOn'
    continuousOn_symm' disjoint' disjoint'' disjointBase' mapsTo
  let _ := finiteType_attachCellsFiniteType C D map' source_eq' continuousOn' continuousOn_symm'
      disjoint' disjoint'' disjointBase' mapsTo
  inferInstance

@[simps! -isSimp]
def CWComplex.attachCells.{u} {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X)
    [CWComplex C] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (mapsTo : ∀ i, ∃ I : Π m, Finset (cell C m),
      MapsTo (map' i) (sphere 0 1) (⋃ (m < n) (j ∈ I m), closedCell m j)) :
    CWComplex ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  (RelCWComplex.attachCells C ∅ map' source_eq' continuousOn' continuousOn_symm' disjoint'
    disjoint'' (disjointBase' := by simp) (mapsTo := by simpa)).toCWComplex

lemma CWComplex.finiteDimensional_attachCells.{u} {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] [FiniteDimensional C] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (mapsTo : ∀ i, ∃ I : Π m, Finset (cell C m),
      MapsTo (map' i) (sphere 0 1) (⋃ (m < n) (j ∈ I m), closedCell m j)) :
    letI := attachCells C map' source_eq' continuousOn' continuousOn_symm' disjoint' disjoint''
      mapsTo
    FiniteDimensional ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  let _ := attachCells C map' source_eq' continuousOn' continuousOn_symm' disjoint' disjoint''
      mapsTo
  {eventually_isEmpty_cell := by
    have h := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅)
    simp only [Filter.eventually_atTop, ge_iff_le, RelCWComplex.ofEq_cell,
      RelCWComplex.attachCells_cell, isEmpty_sum, isEmpty_pprod, isEmpty_Prop] at h ⊢
    obtain ⟨N, hN⟩ := h
    use N ⊔ n.succ
    intro b hb
    exact ⟨hN b (le_of_max_le_left hb), .inr (Nat.ne_of_lt' (le_of_max_le_right hb))⟩}

/-- A version of `RelCWComplex.attachCells`. Assuming that the CW complex is of finite type lets us
  relax the condition `mapsTo`. -/
@[simps! -isSimp]
def CWComplex.attachCellsFiniteType.{u} {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] [FiniteType C] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (mapsTo : ∀ i, MapsTo (map' i) (sphere 0 1) (⋃ (m < n) (j : cell C m) , closedCell m j)) :
    CWComplex ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  attachCells C map' source_eq' continuousOn' continuousOn_symm' disjoint' disjoint''
    (mapsTo := by
      intro i
      use fun m ↦ finite_univ.toFinset
      simp only [instRelCWComplex_cell, Finite.mem_toFinset, mem_univ, iUnion_true]
      exact mapsTo i)

lemma CWComplex.finiteDimensional_attachCellsFiniteType.{u} {X : Type u} [TopologicalSpace X]
    [T2Space X] (C : Set X) [CWComplex C] [Finite C] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (mapsTo : ∀ i, MapsTo (map' i) (sphere 0 1) (⋃ (m < n) (j : cell C m) , closedCell m j)) :
    letI := attachCellsFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' mapsTo
    FiniteDimensional ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  let _ := attachCellsFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
    disjoint'' mapsTo
  {eventually_isEmpty_cell := by
    have h := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅)
    simp only [Filter.eventually_atTop, ge_iff_le, RelCWComplex.ofEq_cell,
      RelCWComplex.attachCells_cell, isEmpty_sum, isEmpty_pprod, isEmpty_Prop] at h ⊢
    obtain ⟨N, hN⟩ := h
    use N ⊔ n.succ
    intro b hb
    exact ⟨hN b (le_of_max_le_left hb), .inr (Nat.ne_of_lt' (le_of_max_le_right hb))⟩}

lemma CWComplex.finiteType_attachCellsFiniteType.{u} {X : Type u} [TopologicalSpace X]
    [T2Space X] (C : Set X) [CWComplex C] [FiniteType C] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (mapsTo : ∀ i, MapsTo (map' i) (sphere 0 1) (⋃ (m < n) (j : cell C m) , closedCell m j)) :
    letI := attachCellsFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' mapsTo
    FiniteType ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  let _ := attachCellsFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
    disjoint'' mapsTo
  {finite_cell := by
    intro m
    simp only [RelCWComplex.ofEq_cell, RelCWComplex.attachCells_cell]
    infer_instance}

lemma CWComplex.finite_attachCellsFiniteType.{u} {X : Type u} [TopologicalSpace X]
    [T2Space X] (C : Set X) [CWComplex C] [Finite C] {n : ℕ} {ι : Type u} [_root_.Finite ι]
    (map' : ι → PartialEquiv (Fin n → ℝ) X)
    (source_eq' : ∀ i, (map' i).source = ball 0 1)
    (continuousOn' : ∀ i, ContinuousOn (map' i) (closedBall 0 1))
    (continuousOn_symm' : ∀ i, ContinuousOn (map' i).symm (map' i).target)
    (disjoint' : ∀ i m (j : cell C m), Disjoint (map' i '' ball 0 1) (openCell m j))
    (disjoint'' : ∀ i j, i ≠ j → Disjoint (map' i '' ball 0 1) (map' j '' ball 0 1))
    (mapsTo : ∀ i, MapsTo (map' i) (sphere 0 1) (⋃ (m < n) (j : cell C m) , closedCell m j)) :
    letI := attachCellsFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
      disjoint'' mapsTo
    Finite ((⋃ i, map' i '' closedBall 0 1) ∪ C) :=
  let _ := attachCellsFiniteType C map' source_eq' continuousOn' continuousOn_symm' disjoint'
    disjoint'' mapsTo
  let _ := finiteDimensional_attachCellsFiniteType C map' source_eq' continuousOn'
    continuousOn_symm' disjoint' disjoint'' mapsTo
  let _ := finiteType_attachCellsFiniteType C map' source_eq' continuousOn'
    continuousOn_symm' disjoint' disjoint'' mapsTo
  inferInstance

/-- A partial bijection with closed source and target that is continuous on both source and target
preserves CW-structures. -/
@[simps -isSimp]
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
  mapsTo n i := by
    obtain ⟨I, hI⟩ := mapsTo n i
    use I
    rw [Set.mapsTo'] at hI ⊢
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
lemma RelCWComplex.finiteDimensional_ofPartialEquiv.{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y}
    [RelCWComplex C D] [FiniteDimensional C] (hC : IsClosed C) (hE : IsClosed E)
    (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E) (hDF : f '' D = F)
    (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E) :
    letI := ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
    FiniteDimensional E :=
  let _ := ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
  {eventually_isEmpty_cell := FiniteDimensional.eventually_isEmpty_cell (C := C)}

/-- `RelCWComplex.ofPartialEquiv` preserves finite type. -/
lemma RelCWComplex.finiteType_ofPartialEquiv.{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y}
    [RelCWComplex C D] [FiniteType C] (hC : IsClosed C) (hE : IsClosed E)
    (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E) (hDF : f '' D = F)
    (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E) :
    letI := ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
    FiniteType E :=
  let _ := ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
  {finite_cell := FiniteType.finite_cell (C := C)}

/-- `RelCWComplex.ofPartialEquiv` preserves finiteness. -/
lemma RelCWComplex.finite_ofPartialEquiv.{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y}
    [RelCWComplex C D] [Finite C] (hC : IsClosed C) (hE : IsClosed E)
    (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E) (hDF : f '' D = F)
    (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E) :
    letI := ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
    Finite E :=
  let _ := ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
  let _ := finiteDimensional_ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
  let _ := finiteType_ofPartialEquiv C E hC hE f hfC1 hfE1 hDF hfC2 hfE2
  inferInstance

/-- A version of `RelCWComplex.ofPartialEquiv` for absolute CW-complexes. -/
@[simps! -isSimp]
def CWComplex.ofPartialEquiv.{u} {X Y : Type u} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] (C : Set X) (E : Set Y) [CWComplex C] (hC : IsClosed C)
    (hE : IsClosed E) (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E)
    (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E)  :
    CWComplex E :=
  (RelCWComplex.ofPartialEquiv C E hC hE f hfC1 hfE1 (image_empty f)  hfC2 hfE2).toCWComplex

/-- `CWComplex.ofPartialEquiv` preserves finite dimensionality. -/
lemma CWComplex.finiteDimensional_ofPartialEquiv .{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) (E : Set Y) [CWComplex C] [FiniteDimensional C]
    (hC : IsClosed C) (hE : IsClosed E) (f : PartialEquiv X Y) (hfC1 : f.source = C)
    (hfE1 : f.target = E) (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E)  :
    letI := ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
    FiniteDimensional E :=
  let _ := ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
  { eventually_isEmpty_cell := FiniteDimensional.eventually_isEmpty_cell (C := C) }

/-- `CWComplex.ofPartialEquiv` preserves finite type. -/
lemma CWComplex.finiteType_ofPartialEquiv .{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) (E : Set Y) [CWComplex C] [FiniteType C]
    (hC : IsClosed C) (hE : IsClosed E) (f : PartialEquiv X Y) (hfC1 : f.source = C)
    (hfE1 : f.target = E) (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E)  :
    letI := ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
    FiniteType E :=
  let _ := ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
  { finite_cell := FiniteType.finite_cell (C := C) }

/-- `CWComplex.ofPartialEquiv` preserves finiteness. -/
lemma CWComplex.finite_ofPartialEquiv .{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) (E : Set Y) [CWComplex C] [Finite C]
    (hC : IsClosed C) (hE : IsClosed E) (f : PartialEquiv X Y) (hfC1 : f.source = C)
    (hfE1 : f.target = E) (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E)  :
    letI := ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
    Finite E :=
  let _ := ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
  let _ := finiteDimensional_ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
  let _ := finiteType_ofPartialEquiv C E hC hE f hfC1 hfE1 hfC2 hfE2
  inferInstance

/-- The image of a CW-complex under a homeomorphisms is again a CW-complex. -/
@[simps! -isSimp]
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

lemma RelCWComplex.finiteDimensional_ofHomeomorph.{u} {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y}
    [RelCWComplex C D] (f : X ≃ₜ Y) (hCE : f '' C = E) (hDF : f '' D = F)
    [FiniteDimensional C] :
    letI := ofHomeomorph C E f hCE hDF
    FiniteDimensional E :=
  let _ := ofHomeomorph C E f hCE hDF
  {eventually_isEmpty_cell := FiniteDimensional.eventually_isEmpty_cell (C := C)}

lemma RelCWComplex.finiteType_ofHomeomorph.{u} {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y}
    [RelCWComplex C D] (f : X ≃ₜ Y) (hCE : f '' C = E) (hDF : f '' D = F)
    [FiniteType C] :
    letI := ofHomeomorph C E f hCE hDF
    FiniteType E :=
  let _ := ofHomeomorph C E f hCE hDF
  {finite_cell := FiniteType.finite_cell (C := C)}

lemma RelCWComplex.finite_ofHomeomorph.{u} {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y}
    [RelCWComplex C D] (f : X ≃ₜ Y) (hCE : f '' C = E) (hDF : f '' D = F)
    [Finite C] :
    letI := ofHomeomorph C E f hCE hDF
    Finite E :=
  let _ := ofHomeomorph C E f hCE hDF
  let _ := finiteDimensional_ofHomeomorph C E f hCE hDF
  let _ := finiteType_ofHomeomorph C E f hCE hDF
  inferInstance

/-- The image of a CW-complex under a homeomorphisms is again a CW-complex. -/
@[simps! -isSimp]
def CWComplex.ofHomeomorph.{u} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] (C : Set X) (E : Set Y) [CWComplex C] (f : X ≃ₜ Y)
    (hCE : f '' C = E) : CWComplex E :=
  (RelCWComplex.ofHomeomorph C E f hCE (image_empty ⇑f)).toCWComplex

lemma CWComplex.finiteDimensional_ofHomeomorph.{u} {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] (C : Set X) (E : Set Y) [CWComplex C] (f : X ≃ₜ Y)
    (hCE : f '' C = E) [FiniteDimensional C] :
    letI := ofHomeomorph C E f hCE
    FiniteDimensional E :=
  let _ := ofHomeomorph C E f hCE
  {eventually_isEmpty_cell := FiniteDimensional.eventually_isEmpty_cell (C := C)}

lemma CWComplex.finiteType_ofHomeomorph.{u} {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] (C : Set X) (E : Set Y) [CWComplex C] (f : X ≃ₜ Y)
    (hCE : f '' C = E) [FiniteType C] :
    letI := ofHomeomorph C E f hCE
    FiniteType E :=
  let _ := ofHomeomorph C E f hCE
  {finite_cell := FiniteType.finite_cell (C := C)}

variable [T2Space X]

lemma CWComplex.finite_ofHomeomorph.{u} {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] (C : Set X) (E : Set Y) [CWComplex C] (f : X ≃ₜ Y)
    (hCE : f '' C = E) [Finite C] :
    letI := ofHomeomorph C E f hCE
    Finite E :=
  let _ := ofHomeomorph C E f hCE
  let _ := finiteDimensional_ofHomeomorph C E f hCE
  let _ := finiteType_ofHomeomorph C E f hCE
  inferInstance

open Set.Notation in
@[simps! -isSimp]
def RelCWComplex.enlargeNonempty [RelCWComplex (X := C) univ (C ↓∩ D)] (hC : IsClosed C)
    (hC2 : C.Nonempty) (hDC : D ⊆ C) :
    RelCWComplex C D :=
  letI : Nonempty C := Nonempty.to_subtype hC2
  letI : Inhabited C := Classical.inhabited_of_nonempty this
  ofPartialEquiv univ (D := (C ↓∩ D)) C (F := D) isClosed_univ hC
    (Subtype.val_injective.injOn.toPartialEquiv _ (univ : Set C))
    (by simp)
    (by simp)
    (by simp [hDC])
    continuous_subtype_val.continuousOn
    (by
      simp [continuousOn_iff_continuous_restrict]
      apply continuous_id.congr
      exact fun x ↦ (Subtype.val_injective.injOn.leftInvOn_invFunOn (mem_univ x)).symm)

open Set.Notation in
lemma RelCWComplex.finiteDimensional_enlargeNonempty [RelCWComplex (X := C) univ (C ↓∩ D)]
    [FiniteDimensional (X := C) univ]
    (hC : IsClosed C) (hC2 : C.Nonempty) (hDC : D ⊆ C) :
    letI := enlargeNonempty hC hC2 hDC
    FiniteDimensional C :=
  let _ := enlargeNonempty hC hC2 hDC
  finiteDimensional_ofPartialEquiv ..

open Set.Notation in
lemma RelCWComplex.finiteType_enlargeNonempty [RelCWComplex (X := C) univ (C ↓∩ D)]
    [FiniteType (X := C) univ]
    (hC : IsClosed C) (hC2 : C.Nonempty) (hDC : D ⊆ C) :
    letI := enlargeNonempty hC hC2 hDC
    FiniteType C :=
  let _ := enlargeNonempty hC hC2 hDC
  finiteType_ofPartialEquiv ..

open Set.Notation in
lemma RelCWComplex.finite_enlargeNonempty [RelCWComplex (X := C) univ (C ↓∩ D)]
    [Finite (X := C) univ]
    (hC : IsClosed C) (hC2 : C.Nonempty) (hDC : D ⊆ C) :
    letI := enlargeNonempty hC hC2 hDC
    Finite C :=
  let _ := enlargeNonempty hC hC2 hDC
  finite_ofPartialEquiv ..

@[simps! -isSimp]
def CWComplex.enlargeNonempty [CWComplex (X := C) univ] (hC : IsClosed C)
    (hC2 : C.Nonempty) : CWComplex C :=
  (RelCWComplex.enlargeNonempty hC hC2 (empty_subset C)).toCWComplex

lemma CWComplex.finiteDimensional_enlargeNonempty [CWComplex (X := C) univ]
    [FiniteDimensional (X := C) univ]
    (hC : IsClosed C) (hC2 : C.Nonempty) :
    letI := enlargeNonempty hC hC2
    FiniteDimensional C :=
  let _ := enlargeNonempty hC hC2
  finiteDimensional_ofPartialEquiv ..

lemma CWComplex.finiteType_enlargeNonempty [CWComplex (X := C) univ]
    [FiniteType (X := C) univ]
    (hC : IsClosed C) (hC2 : C.Nonempty) :
    letI := enlargeNonempty hC hC2
    FiniteType C :=
  let _ := enlargeNonempty hC hC2
  finiteType_ofPartialEquiv ..

open Set.Notation in
lemma CWComplex.finite_enlargeNonempty [CWComplex (X := C) univ]
    [Finite (X := C) univ]
    (hC : IsClosed C) (hC2 : C.Nonempty) :
    letI := enlargeNonempty hC hC2
    Finite C :=
  let _ := enlargeNonempty hC hC2
  finite_ofPartialEquiv ..

open Set.Notation Classical in
def RelCWComplex.enlarge [RelCWComplex (X := C) univ (C ↓∩ D)] (hC : IsClosed C)
    (hDC : D ⊆ C) : RelCWComplex C D :=
  if h : C.Nonempty then enlargeNonempty hC h hDC else
    ofEq ∅ ∅ (not_nonempty_iff_eq_empty.1 h).symm
    (subset_eq_empty hDC (not_nonempty_iff_eq_empty.1 h)).symm

@[simps! -isSimp]
def CWComplex.enlarge [CWComplex (X := C) univ] (hC : IsClosed C) : CWComplex C :=
  (RelCWComplex.enlarge hC (empty_subset C)).toCWComplex

open Set.Notation in
lemma RelCWComplex.enlarge_eq_enlargeNonempty [RelCWComplex (X := C) univ (C ↓∩ D)]
    (hC : IsClosed C) (hC2 : C.Nonempty) (hDC : D ⊆ C) :
    enlarge hC hDC = enlargeNonempty hC hC2 hDC := by
  simp [enlarge, hC2]

lemma CWComplex.enlarge_eq_enlargeNonempty [CWComplex (X := C) univ]
    (hC : IsClosed C) (hC2 : C.Nonempty) :
    enlarge hC = enlargeNonempty hC hC2 :=
  congrArg _ (RelCWComplex.enlarge_eq_enlargeNonempty hC hC2 (empty_subset C))

open Set.Notation in
lemma RelCWComplex.enlarge_eq_empty [RelCWComplex (X := C) univ (C ↓∩ D)]
    (hC : IsClosed C)
    (hC2 : ¬ C.Nonempty) (hDC : D ⊆ C) :
    enlarge hC hDC = ofEq ∅ ∅ (not_nonempty_iff_eq_empty.1 hC2).symm
    (subset_eq_empty hDC (not_nonempty_iff_eq_empty.1 hC2)).symm := by
  simp [enlarge, hC2]

lemma CWComplex.enlarge_eq_empty [h : CWComplex (X := C) univ]
    (hC : IsClosed C) (hC2 : ¬ C.Nonempty) :
    letI := RelCWComplex.ofEq ∅ ∅ (not_nonempty_iff_eq_empty.1 hC2).symm rfl
    enlarge hC = RelCWComplex.toCWComplex C :=
  congrArg _ (RelCWComplex.enlarge_eq_empty hC hC2 (empty_subset C))

open Set.Notation Classical in
lemma RelCWComplex.finiteDimensional_enlarge [RelCWComplex (X := C) univ (C ↓∩ D)]
    [FiniteDimensional (X := C) univ] (hC : IsClosed C) (hDC : D ⊆ C) :
    letI := enlarge hC hDC
    FiniteDimensional C :=
  let _ := enlarge hC hDC
  if hC2 : C.Nonempty then
    (enlarge_eq_enlargeNonempty hC hC2 hDC ▸ finiteDimensional_enlargeNonempty hC hC2 hDC)
    else (enlarge_eq_empty hC hC2 hDC ▸ finiteDimensional_ofEq ..)

open Set.Notation Classical in
lemma RelCWComplex.finiteType_enlarge [RelCWComplex (X := C) univ (C ↓∩ D)]
    [FiniteType (X := C) univ] (hC : IsClosed C) (hDC : D ⊆ C) :
    letI := enlarge hC hDC
    FiniteType C :=
  let _ := enlarge hC
  if hC2 : C.Nonempty then
    (enlarge_eq_enlargeNonempty hC hC2 hDC ▸ finiteType_enlargeNonempty hC hC2 hDC)
    else (enlarge_eq_empty hC hC2 hDC ▸ finiteType_ofEq ..)

open Set.Notation in
lemma RelCWComplex.finite_enlarge [RelCWComplex (X := C) univ (C ↓∩ D)]
    [Finite (X := C) univ] (hC : IsClosed C) (hDC : D ⊆ C) :
    letI := enlarge hC hDC
    Finite C :=
  let _ := enlarge hC hDC
  let _ := finiteDimensional_enlarge hC hDC
  let _ := finiteType_enlarge hC hDC
  inferInstance

lemma CWComplex.finiteDimensional_enlarge [CWComplex (X := C) univ]
    [h : FiniteDimensional (X := C) univ] (hC : IsClosed C) :
    letI := enlarge hC
    FiniteDimensional C :=
  @RelCWComplex.finiteDimensional_enlarge _ _ _ _ _ _ h hC (empty_subset C)

lemma CWComplex.finiteType_enlarge [CWComplex (X := C) univ]
    [h : FiniteType (X := C) univ] (hC : IsClosed C) :
    letI := enlarge hC
    FiniteType C :=
  @RelCWComplex.finiteType_enlarge _ _ _ _ _ _ h hC (empty_subset C)

lemma CWComplex.finite_enlarge [CWComplex (X := C) univ]
    [h : Finite (X := C) univ] (hC : IsClosed C) :
    letI := enlarge hC
    Finite C :=
  @RelCWComplex.finite_enlarge _ _ _ _ _ _ h hC (empty_subset C)

open Notation in
@[simps! -isSimp]
def RelCWComplex.restrictNonempty [RelCWComplex C D] (Y : Set X) (hCY : C ⊆ Y)
    (hC : C.Nonempty) : RelCWComplex (X := Y) (Y ↓∩ C) (Y ↓∩ D) :=
  letI : Nonempty Y := Nonempty.to_subtype (hC.mono hCY)
  ofPartialEquiv C (Y ↓∩ C) isClosed (isClosed.preimage continuous_subtype_val)
    (Subtype.val_injective.injOn.toPartialEquiv _ (Y ↓∩ C)).symm
    (by simp [hCY])
    (by simp)
    (by
      ext x
      simp only [InjOn.toPartialEquiv, Subtype.image_preimage_coe, BijOn.toPartialEquiv_symm_apply,
        mem_image, mem_preimage]
      constructor
      · intro ⟨y, hyD, hyx⟩
        rw [← hyx, Subtype.val.invFunOn_eq ⟨(⟨y, hCY (base_subset_complex hyD)⟩ : Y),
          by simp only [mem_preimage, base_subset_complex hyD], rfl⟩]
        exact hyD
      · intro hx
        exact ⟨x, hx, Subtype.val_injective.injOn.leftInvOn_invFunOn
          (by simp only [mem_preimage, base_subset_complex hx])⟩)
    (by
      simp only [InjOn.toPartialEquiv, Subtype.image_preimage_coe, BijOn.toPartialEquiv_symm_apply,
        continuousOn_iff_continuous_restrict]
      apply (continuous_inclusion hCY).congr
      intro x
      simp only [inclusion, restrict_apply, mem_preimage, Subtype.coe_prop,
        (Subtype.val_injective.injOn.leftInvOn_invFunOn (x := (⟨x, hCY x.2⟩ : Y)))])
    continuous_subtype_val.continuousOn

open Notation in
lemma RelCWComplex.finiteDimensional_restrictNonempty [RelCWComplex C D] [FiniteDimensional C]
    (Y : Set X) (hCY : C ⊆ Y) (hC : C.Nonempty) :
    letI := restrictNonempty Y hCY hC
    FiniteDimensional (Y ↓∩ C) :=
  letI := restrictNonempty Y hCY hC
  finiteDimensional_ofPartialEquiv ..

open Notation in
lemma RelCWComplex.finiteType_restrictNonempty [RelCWComplex C D] [FiniteType C]
    (Y : Set X) (hCY : C ⊆ Y) (hC : C.Nonempty) :
    letI := restrictNonempty Y hCY hC
    FiniteType (Y ↓∩ C) :=
  letI := restrictNonempty Y hCY hC
  finiteType_ofPartialEquiv ..

open Notation in
lemma RelCWComplex.finite_restrictNonempty [RelCWComplex C D] [Finite C]
    (Y : Set X) (hCY : C ⊆ Y) (hC : C.Nonempty) :
    letI := restrictNonempty Y hCY hC
    Finite (Y ↓∩ C) :=
  letI := restrictNonempty Y hCY hC
  finite_ofPartialEquiv ..

open Notation Classical in
def RelCWComplex.restrict [RelCWComplex C D] (Y : Set X) (hCY : C ⊆ Y) :
    RelCWComplex (X := Y) (Y ↓∩ C) (Y ↓∩ D) :=
  if h : C.Nonempty then restrictNonempty Y hCY h else
    ofEq ∅ ∅ (by rw [not_nonempty_iff_eq_empty.1 h, preimage_empty])
    (by rw [subset_eq_empty base_subset_complex (not_nonempty_iff_eq_empty.1 h), preimage_empty])

lemma RelCWComplex.restrict_eq_restrictNonempty [RelCWComplex C D] (Y : Set X) (hCY : C ⊆ Y)
    (hC : C.Nonempty) :
    restrict Y hCY = restrictNonempty Y hCY hC := by
  simp [restrict, hC]

open Notation in
lemma RelCWComplex.restrict_eq_empty [RelCWComplex C D] (Y : Set X) (hCY : C ⊆ Y)
    (hC : ¬ C.Nonempty) :
    restrict Y hCY = ofEq (E := (Y ↓∩ C)) ∅ ∅
      (by rw [not_nonempty_iff_eq_empty.1 hC, preimage_empty])
      (by rw [subset_eq_empty base_subset_complex (not_nonempty_iff_eq_empty.1 hC),
        preimage_empty]) := by
  simp [restrict, hC]

open Notation Classical in
lemma RelCWComplex.finiteDimensional_restrict [RelCWComplex C D] [FiniteDimensional C]
    (Y : Set X) (hCY : C ⊆ Y) :
    letI := restrict Y hCY
    FiniteDimensional (Y ↓∩ C) :=
  let _ := restrict Y hCY
  if hC : C.Nonempty then
    (restrict_eq_restrictNonempty Y hCY hC ▸ finiteDimensional_restrictNonempty Y hCY hC)
    else (restrict_eq_empty Y hCY hC ▸ finiteDimensional_ofEq ..)

open Notation Classical in
lemma RelCWComplex.finiteType_restrict [RelCWComplex C D] [FiniteType C]
    (Y : Set X) (hCY : C ⊆ Y) :
    letI := restrict Y hCY
    FiniteType (Y ↓∩ C) :=
  let _ := restrict Y hCY
  if hC : C.Nonempty then
    (restrict_eq_restrictNonempty Y hCY hC ▸ finiteType_restrictNonempty Y hCY hC)
    else (restrict_eq_empty Y hCY hC ▸ finiteType_ofEq ..)

open Notation in
lemma RelCWComplex.finite_restrict [RelCWComplex C D] [Finite C]
    (Y : Set X) (hCY : C ⊆ Y) :
    letI := restrict Y hCY
    FiniteType (Y ↓∩ C) :=
  let _ := restrict Y hCY
  let _ := finiteDimensional_restrict Y hCY
  let _ := finiteType_restrict Y hCY
  inferInstance

namespace CWComplex

export RelCWComplex (restrictNonempty finiteDimensional_restrictNonempty finiteType_restrictNonempty
  finite_restrictNonempty restrictNonempty_cell restrictNonempty_map_apply
  restrictNonempty_map_symm_apply restrictNonempty_map_source restrictNonempty_map_target restrict
  restrict_eq_restrictNonempty restrict_eq_empty finiteDimensional_restrict finiteType_restrict
  finite_restrict)

end CWComplex

end Topology

set_option linter.style.longFile 1700
