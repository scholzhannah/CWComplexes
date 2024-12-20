import CWcomplexes.Relative.RelLemmas
import Mathlib.Analysis.NormedSpace.Real

/-!
# Subcomplexes

In this file we discuss subcomplexes of CW-complexes.

## Main definitions:
* `Subcomplex`: A subcomplex is a closed subspace of a CW-complex that is the union of open cells of
  the CW-complex.
* `Subcomplex'`: An alternative definition of a subcomplex that does not require that the subspace
  is closed. Instead it requires that for every open cell that forms the subcomplex the
  corresponding closed cell is a subset of the subspace.
* `Subcomplex''` : An alternative definition of a subcomplex that does not require the subspace to
  be closed but instead requires that it is a CW-complex itself.
* `attach_cell`: The subcomplex that results from attaching a cell to a subcomplex when the edge of
  the cell is contained in the original subcomplex.

## Main results:
* `CWComplex_subcomplex`: A subcomplex of a CW-complex is again a CW-complex.
* `subcomplex_iUnion_subcomplex`: A union of subcomplexes is again a subcomplex.
* `cell_mem_finite_subcomplex`: Every cell is part of a finite subcomplex.
* `compact_subset_finite_subcomplex`: Every compact set in a CW-complex is contained in a finite
  subcomplex.

## Notation
* `E ⇂ C`: `E` is a subcomplex of the CW-complex `C`.

## References
* [K. Jänich, *Topology*]
-/

noncomputable section

open Metric Set

namespace CWComplex

variable {X : Type*} [t : TopologicalSpace X] {C D : Set X}

section

-- rename Subcomplex as it does the same thing.

/-- A subcomplex is a closed subspace of a CW-complex that is the union of open cells of the
  CW-complex.-/
class RelSubcomplex (C : Set X) {D : Set X} [RelCWComplex C D] (E : Set X) where
  /-- The indexing set of cells of the subcomplex.-/
  I : Π n, Set (cell C n)
  /-- A subcomplex is closed.-/
  closed : IsClosed E
  /-- The union of all open cells of the subcomplex equals the subcomplex.-/
  union : D ∪ ⋃ (n : ℕ) (j : I n), openCell (C := C) (D := D) n j = E

abbrev Subcomplex (C E : Set X) [CWComplex C] := RelSubcomplex C E

lemma Subcomplex.union {C E : Set X} [CWComplex C] [Subcomplex C E] :
    ⋃ (n : ℕ) (j : RelSubcomplex.I (C := C) (D := ∅) E n), openCell (C := C) (D := ∅) n j = E := by
  have := RelSubcomplex.union (C := C) (D := ∅) (E := E)
  rw [empty_union] at this
  exact this

-- lower case, relsubcomplex.mk'

/-- An alternative version of `Subcomplex`: Instead of requiring that `E` is closed it requires
  that for every cell of the subcomplex the corresponding closed cell is a subset of `E`.-/
@[simps -isSimp]
def RelSubcomplex' [T2Space X] (C : Set X) {D : Set X} [RelCWComplex C D] (E : Set X)
    (I : Π n, Set (cell C n))
    (closedCell_subset : ∀ (n : ℕ) (i : I n), closedCell (C := C) n i ⊆ E)
    (union : D ∪ ⋃ (n : ℕ) (j : I n), openCell (C := C) n j = E) : RelSubcomplex C E where
  I := I
  closed := by
    have EsubC : E ⊆ C := by
      simp_rw [← union, ← iUnion_openCell (C := C) (D := D)]
      exact union_subset_union_right D
        (iUnion_mono fun n ↦ iUnion_subset fun i ↦ by apply subset_iUnion_of_subset ↑i; rfl)
    apply isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell (D := D) EsubC
    · have : D ⊆ E := by
        rw [← union]
        exact subset_union_left
      rw [inter_eq_right.2 this]
      exact isClosedBase C
    intro n _ j
    by_cases h : j ∈ I n
    · right
      suffices closedCell n j ⊆ E by
        rw [inter_eq_right.2 this]
        exact isClosed_closedCell
      exact closedCell_subset n ⟨j, h⟩
    · left
      rw [← union, union_inter_distrib_right]
      apply IsClosed.union
      · rw [inter_comm, (disjointBase n j).inter_eq]
        exact isClosed_empty
      · simp_rw [iUnion_inter]
        suffices ⋃ m, ⋃ (i : ↑(I m)), openCell m (i : cell C m) ∩ openCell (C := C) n j = ∅ by
          rw [this]
          exact isClosed_empty
        apply iUnion_eq_empty.2 fun m ↦ iUnion_eq_empty.2 fun i ↦ ?_
        apply disjoint_openCell_of_ne
        aesop
  union := union

/-- An alternative version of `Subcomplex`: Instead of requiring that `E` is closed it requires
  that for every cell of the subcomplex the corresponding closed cell is a subset of `E`.-/
@[simps!]
def Subcomplex' [T2Space X] (C : Set X) [CWComplex C] (E : Set X) (I : Π n, Set (cell C n))
    (closedCell_subset : ∀ (n : ℕ) (i : I n), closedCell (C := C) (D := ∅) n i ⊆ E)
    (union : ⋃ (n : ℕ) (j : I n), openCell (C := C) (D := ∅) n j = E) : Subcomplex C E :=
  RelSubcomplex' C E I closedCell_subset (by rw [empty_union]; exact union)

/-- An alternative version of `Subcomplex`: Instead of requiring that `E` is closed it requires that
  `E` is a CW-complex. -/
@[simps]
def RelSubcomplex'' [T2Space X] (C : Set X) {D : Set X} [RelCWComplex C D] (E : Set X)
    (I : Π n, Set (cell C n)) [RelCWComplex E D]
    (union : D ∪ ⋃ (n : ℕ) (j : I n), openCell (C := C) (D := D) n j = E) : RelSubcomplex C E where
  I := I
  closed := CWComplex.isClosed (D := D)
  union := union

/-- An alternative version of `Subcomplex`: Instead of requiring that `E` is closed it requires that
  `E` is a CW-complex. -/
@[simps]
def Subcomplex'' [T2Space X] (C : Set X) [CWComplex C] (E : Set X) (I : Π n, Set (cell C n))
    [CWComplex E] (union : ⋃ (n : ℕ) (j : I n), openCell (C := C) (D := ∅) n j = E) :
    Subcomplex C E where
  I := I
  closed := CWComplex.isClosed (D := ∅)
  union := by
    rw [empty_union]
    exact union

namespace Subcomplex

lemma subset_complex [RelCWComplex C D] (E : Set X) [subcomplex : RelSubcomplex C E] : E ⊆ C := by
  simp_rw [← subcomplex.union, ← iUnion_openCell (C := C) (D := D)]
  apply union_subset_union_right D
  exact iUnion_mono fun n ↦ iUnion_subset fun i ↦ by apply subset_iUnion_of_subset ↑i; rfl

/-- A subcomplex is the union of its closed cells.-/
lemma union_closedCell [T2Space X] [RelCWComplex C D] (E : Set X)
    [subcomplex : RelSubcomplex C E] :
    D ∪ ⋃ (n : ℕ) (j : subcomplex.I n), closedCell (C := C) (D := D) n j = E := by
  apply subset_antisymm
  · apply union_subset
    · rw [← RelSubcomplex.union (C := C) (D := D) (E := E)]
      exact subset_union_left
    · apply iUnion_subset fun n ↦ iUnion_subset fun i ↦ ?_
      simp_rw [← closure_openCell_eq_closedCell, subcomplex.closed.closure_subset_iff,
        ← subcomplex.union]
      apply subset_union_of_subset_right
      exact subset_iUnion_of_subset n
        (subset_iUnion (fun (i : ↑(RelSubcomplex.I E n)) ↦ openCell (C := C) (D := D) n ↑i) i)
  · simp_rw [← subcomplex.union]
    apply union_subset_union_right
    apply iUnion_mono fun n ↦ iUnion_mono fun (i : ↑(RelSubcomplex.I E n)) ↦ ?_
    exact openCell_subset_closedCell (C := C) (D := D) n i

/-- A subcomplex is the union of its closed cells.-/
lemma union_closedCellAB [T2Space X] [CWComplex C] (E : Set X) [subcomplex : Subcomplex C E] :
    ⋃ (n : ℕ) (j : subcomplex.I n), closedCell (C := C) (D := ∅) n j = E := by
  apply subset_antisymm
  · apply iUnion_subset fun n ↦ iUnion_subset fun i ↦ ?_
    simp_rw [← closure_openCell_eq_closedCell, subcomplex.closed.closure_subset_iff,
      ← subcomplex.union]
    exact subset_iUnion_of_subset n
      (subset_iUnion (fun (i : ↑(RelSubcomplex.I E n)) ↦ openCell (C := C) (D := ∅) n ↑i) i)
  · simp_rw [← subcomplex.union]
    apply iUnion_mono fun n ↦ iUnion_mono fun (i : ↑(subcomplex.I n)) ↦ ?_
    exact openCell_subset_closedCell (C := C) (D := ∅) n i


abbrev RelSub (E C : Set X) : Set X := E

/-- `E ⇂ C` should be used to say that `E` is a subcomplex of `C`. -/
scoped infixr:35 " ⇂ "  => RelSub

/-- A subcomplex is again a CW-complex. -/
@[simps]
instance RelCWComplex_RelSubcomplex [T2Space X] [RelCWComplex C D] (E : Set X)
    [subcomplex : RelSubcomplex C E] : RelCWComplex (E ⇂ C) D where
  cell n := subcomplex.I n
  map n i := map (C := C) (D := D) n i
  source_eq n i := source_eq (C := C) (D := D) n i
  cont n i := cont (C := C) (D := D) n i
  cont_symm n i := cont_symm (C := C) (D := D) n i
  pairwiseDisjoint' := by
    simp only [PairwiseDisjoint, Set.Pairwise, mem_univ, ne_eq, Function.onFun,
      disjoint_iff_inter_eq_empty, true_implies, Sigma.forall, Subtype.forall,
      not_and]
    intro n j _ m i _ eq
    apply disjoint_openCell_of_ne
    simp_all only [Sigma.mk.inj_iff, not_and, ne_eq]
    intro a
    subst a
    simp_all only [heq_eq_eq, Subtype.mk.injEq, forall_const, not_false_eq_true]
  disjointBase' := fun n i ↦ RelCWComplex.disjointBase' (C := C) (D := D) n i
  mapsto := by
    intro n i
    rcases cellFrontier_subset_finite_openCell (C := C) (D := D) n i with ⟨J, hJ⟩
    use fun m ↦ Finset.preimage (J m) (fun (x : subcomplex.I m) ↦ ↑x) (by simp [InjOn])
    rw [mapsTo']
    intro x xmem
    simp_rw [iUnion_coe_set, mem_union, mem_iUnion, exists_prop, exists_and_right]
    replace hJ := hJ xmem
    by_cases h : x ∈ D
    · left
      exact h
    simp only [mem_union, h, mem_iUnion, exists_prop, false_or] at hJ
    right
    obtain ⟨m, mltn, j, jmem, xmemopen⟩ := hJ
    use m, mltn, j
    refine ⟨?_, openCell_subset_closedCell _ _ xmemopen⟩
    suffices j ∈ subcomplex.I m by
      use this
      simp only [Finset.mem_preimage, jmem]
    have : x ∈ E := by
      rw [← Subcomplex.union_closedCell (C := C) (D := D) (E := E)]
      right
      refine mem_of_subset_of_mem ?_ xmem
      refine subset_iUnion_of_subset n (subset_iUnion_of_subset ↑i ?_)
      exact cellFrontier_subset_closedCell (C := C)  (D := D) n ↑i
    simp only [← subcomplex.union, iUnion_coe_set, mem_union, h, mem_iUnion, exists_prop,
      false_or] at this
    obtain ⟨l, o, xmemopen'⟩ := this
    suffices (⟨m, j⟩ : Σ n, cell C n) = ⟨l, ↑o⟩ by aesop
    apply eq_cell_of_not_disjoint
    rw [not_disjoint_iff]
    use x
    exact ⟨xmemopen, xmemopen'.2⟩
  closed' A Asub closed := by
    apply isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell (D := D)
      (subset_trans Asub (Subcomplex.subset_complex (C := C) (D := D) E)) closed.2
    intro n _ j
    by_cases h : j ∈ subcomplex.I n
    · exact Or.intro_right _ (closed.1 n ⟨j, h⟩)
    left
    suffices A ∩ openCell n j = ∅ by
      rw [this]
      exact isClosed_empty
    rw [← subset_empty_iff]
    apply subset_trans (inter_subset_inter_left _ Asub)
    simp_rw [RelSub, ← subcomplex.union, subset_empty_iff, union_inter_distrib_right, iUnion_inter,
      union_empty_iff]
    constructor
    · rw [inter_comm]
      exact (RelCWComplex.disjointBase' n j).inter_eq
    · exact iUnion_eq_empty.2 fun m ↦ iUnion_eq_empty.2 fun i ↦ disjoint_openCell_of_ne (by aesop)
  isClosedBase := RelCWComplex.isClosedBase (C := C) (D := D)
  union' := Subcomplex.union_closedCell E (D := D)

/-- A subcomplex is again a CW-complex. -/
instance CWComplex_Subcomplex [T2Space X] [CWComplex C] (E : Set X)
    [subcomplex : Subcomplex C E] : CWComplex (E ⇂ C) := RelCWComplex_RelSubcomplex (C := C) E

instance finiteType_subcomplex_of_finiteType [T2Space X] [RelCWComplex C D] [FiniteType C]
    (E : Set X) [RelSubcomplex C E] : FiniteType E where
  finite_cell n :=
    let _ := FiniteType.finite_cell (C := C) (D := D) n
    toFinite (RelSubcomplex.I E n)

instance finiteDimensional_subcomplex_of_finiteDimensional [T2Space X] [RelCWComplex C D]
    [FiniteDimensional C] (E : Set X) [RelSubcomplex C E] : FiniteDimensional E where
  eventually_isEmpty_cell := by
    have := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)
    simp only [Filter.eventually_atTop, ge_iff_le] at this ⊢
    obtain ⟨n, hn⟩ := this
    use n
    intro b nleb
    simp only [RelCWComplex_RelSubcomplex, isEmpty_subtype, hn b nleb, IsEmpty.forall_iff]

/-- A subcomplex of a finite CW-complex is again finite.-/
instance finite_subcomplex_of_finite [T2Space X] [RelCWComplex C D] [Finite C] (E : Set X)
  [RelSubcomplex C E] : Finite E := inferInstance

/-- A union of subcomplexes is again a subcomplex.-/
@[simps!]
instance relSubcomplex_iUnion_RelSubcomplex [T2Space X] [RelCWComplex C D] (J : Type*) [Nonempty J]
    (sub : J → Set X) [cw : ∀ (j : J), RelSubcomplex C (sub j)] :
    RelSubcomplex C (⋃ (j : J), sub j) := RelSubcomplex' C _
  (fun (n : ℕ) ↦ ⋃ (j : J), (cw j).I n)
  (by
    intro n ⟨i, imem⟩
    rw [mem_iUnion] at imem
    obtain ⟨j, imemj⟩ := imem
    apply subset_iUnion_of_subset j
    rw [← Subcomplex.union_closedCell (C := C) (E := sub j)]
    apply subset_union_of_subset_right
    exact subset_iUnion_of_subset n (subset_iUnion
      (fun (j : ↑(RelSubcomplex.I (sub j) n)) ↦ closedCell (C := C) n ↑j) ⟨i, imemj⟩))
  (by
    simp_rw [← (cw _).union]
    rw [← union_iUnion, iUnion_comm]
    congrm D ∪ ?_
    apply iUnion_congr fun n ↦ ?_
    simp_rw [iUnion_subtype, mem_iUnion, iUnion_exists,
      iUnion_comm (fun x ↦ fun i ↦ ⋃ (_ : x ∈ RelSubcomplex.I (sub i) n), openCell n x)])

/-- A union of subcomplexes is again a subcomplex.-/
@[simps!]
instance subcomplex_iUnion_subcomplex [T2Space X] [CWComplex C] (J : Type*)
    (sub : J → Set X) [cw : ∀ (j : J), Subcomplex C (sub j)] :
    Subcomplex C (⋃ (j : J), sub j) := Subcomplex' C _
  (fun (n : ℕ) ↦ ⋃ (j : J), (cw j).I n)
  (by
    intro n ⟨i, imem⟩
    rw [mem_iUnion] at imem
    obtain ⟨j, imemj⟩ := imem
    apply subset_iUnion_of_subset j
    rw [← Subcomplex.union_closedCellAB (C := C) (E := sub j)]
    exact subset_iUnion_of_subset n (subset_iUnion
      (fun (j : ↑(RelSubcomplex.I (sub j) n)) ↦ closedCell (C := C) (D := ∅) n ↑j) ⟨i, imemj⟩))
  (by
    simp_rw [← (cw _).union]
    rw [iUnion_comm]
    apply iUnion_congr fun n ↦ ?_
    simp_rw [iUnion_subtype, mem_iUnion, iUnion_exists,
      iUnion_comm (fun x ↦ fun i ↦ ⋃ (_ : x ∈ RelSubcomplex.I (sub i) n), openCell n x)])

/-- A finite union of finite-dimensional subcomplexes is again a finite-dimensional subcomplex.-/
instance finiteDimensional_RelSubcomplex_finite_iUnion_finiteDimensional_RelSubcomplex
    [T2Space X] [RelCWComplex C D] {J : Type*} [Nonempty J] [_root_.Finite J] {sub : J → Set X}
    [cw : ∀ (j : J), RelSubcomplex C (sub j)]
    [finite : ∀ (j : J), FiniteDimensional (sub j ⇂ C)] : FiniteDimensional (⋃ j, sub j) where
  eventually_isEmpty_cell := by
    have h j := (finite j).eventually_isEmpty_cell
    simp only [RelCWComplex_RelSubcomplex, isEmpty_coe_sort, Filter.eventually_iff,
      relSubcomplex_iUnion_RelSubcomplex, RelSubcomplex', iUnion_eq_empty, setOf_forall,
      Filter.iInter_mem] at h ⊢
    exact h

/-- A finite union of finite-dimensionl subcomplexes is again a finite-dimensional subcomplex.-/
instance finiteDimensional_subcomplex_finite_iUnion_finiteDimensional_subcomplex
    [T2Space X] [CWComplex C] {J : Type*}
    [_root_.Finite J] {sub : J → Set X} [cw : ∀ (j : J), Subcomplex C (sub j)]
    [finite : ∀ (j : J), FiniteDimensional (sub j ⇂ C)] : FiniteDimensional (⋃ j, sub j) where
  eventually_isEmpty_cell := by
    have h j := (finite j).eventually_isEmpty_cell
    simp only [CWComplex_Subcomplex, RelCWComplex_RelSubcomplex, isEmpty_coe_sort,
      Filter.eventually_iff, subcomplex_iUnion_subcomplex, Subcomplex', RelSubcomplex',
      iUnion_eq_empty, setOf_forall, Filter.iInter_mem] at h ⊢
    exact h

/-- A finite union of subcomplexes of finite type is again a subcomplex of finite type.-/
instance finiteType_RelSubcomplex_finite_iUnion_finiteType_RelSubcomplex [T2Space X]
    [RelCWComplex C D] {J : Type*} [Nonempty J] [_root_.Finite J] {sub : J → Set X}
    [cw : ∀ (j : J), RelSubcomplex C (sub j)]
    [finite : ∀ (j : J), FiniteType (sub j ⇂ C)] : FiniteType (⋃ j, sub j) where
 finite_cell := by
    have h j := (finite j).finite_cell
    intro n
    simp only [relSubcomplex_iUnion_RelSubcomplex, Subcomplex'', RelCWComplex_RelSubcomplex] at h ⊢
    apply Finite.Set.finite_iUnion

/-- A finite union of subcomplexes of finite type is again a subcomplex of finite type.-/
instance finiteType_subcomplex_finite_iUnion_finiteType_subcomplex [T2Space X] [CWComplex C]
    {J : Type*} [_root_.Finite J] {sub : J → Set X} [cw : ∀ (j : J), Subcomplex C (sub j)]
    [finite : ∀ (j : J), FiniteType (sub j ⇂ C)] : FiniteType (⋃ j, sub j) where
  finite_cell := by
    have h j := (finite j).finite_cell
    intro n
    simp only [subcomplex_iUnion_subcomplex, Subcomplex'', RelCWComplex_RelSubcomplex] at h ⊢
    apply Finite.Set.finite_iUnion

/-- A finite union of finite subcomplexes is again a finite subcomplex.-/
instance finite_RelSubcomplex_finite_iUnion_finite_RelSubcomplex [T2Space X] [RelCWComplex C D]
    {J : Type*} [Nonempty J] [_root_.Finite J] {sub : J → Set X}
    [cw : ∀ (j : J), RelSubcomplex C (sub j)]
    [finite : ∀ (j : J), Finite (sub j ⇂ C)] : Finite (⋃ j, sub j) := inferInstance

/-- A finite union of finite subcomplexes is again a finite subcomplex.-/
instance finite_subcomplex_finite_iUnion_finite_subcomplex [T2Space X] [CWComplex C] {J : Type*}
    [_root_.Finite J] {sub : J → Set X} [cw : ∀ (j : J), Subcomplex C (sub j)]
    [finite : ∀ (j : J), Finite (sub j ⇂ C)] : Finite (⋃ j, sub j) := inferInstance

@[simps]
instance RelSubcomplex_base [RelCWComplex C D] : RelSubcomplex C D where
  I n := ∅
  closed := isClosedBase C
  union := by simp

instance finite_base [T2Space X] [RelCWComplex C D] : Finite D where
  eventually_isEmpty_cell := by
    simp only [Filter.eventually_iff, Filter.mem_atTop_sets, ge_iff_le, mem_setOf_eq]
    use 0
    intro b _
    simp [RelCWComplex_RelSubcomplex, RelSubcomplex_base]
  finite_cell := by
    intro n
    simp [RelCWComplex_RelSubcomplex, RelSubcomplex_base]
    exact Finite.of_subsingleton

@[simps]
def attach_base [T2Space X] [RelCWComplex C D] (n : ℕ) (i : cell C n) (hD: cellFrontier n i ⊆ D) :
    RelSubcomplex C (D ∪ closedCell n i) where
  I m := {x | HEq (⟨m, x⟩ : Σ m, cell C m) (⟨n, i⟩ : Σ n, cell C n)}
  closed := (isClosedBase C).union isClosed_closedCell
  union := by
    rw [← cellFrontier_union_openCell_eq_closedCell, ← union_assoc, union_eq_left.2 hD]
    congrm D ∪ ?_
    ext x
    simp only [coe_setOf, mem_setOf_eq, iUnion_subtype, heq_eq_eq, Sigma.mk.inj_iff, mem_iUnion,
      exists_prop]
    constructor
    · intro ⟨m, j, ⟨eq1, eq2⟩, h⟩
      subst eq1
      simp_all
    · intro h
      use n, i

lemma finite_attach_base [T2Space X] [RelCWComplex C D] (n : ℕ) (i : cell C n)
    (hD: cellFrontier n i ⊆ D) :
    letI _subcomplex := attach_base n i hD
    Finite (D ∪ closedCell n i) :=
  let _subcomplex := attach_base n i hD
  { eventually_isEmpty_cell := by
      simp only [Filter.eventually_atTop, ge_iff_le]
      use n.succ
      intro b le
      simp only [RelCWComplex_RelSubcomplex, attach_base, coe_setOf, mem_setOf_eq, heq_eq_eq,
        Sigma.mk.inj_iff, isEmpty_subtype, not_and]
      intro j h
      subst h
      exfalso
      exact Nat.not_succ_le_self b le
    finite_cell := by
      intro m
      by_cases h : m = n
      · subst m
        simp only [RelCWComplex_RelSubcomplex, attach_base, coe_setOf, mem_setOf_eq, heq_eq_eq,
          Sigma.mk.inj_iff, true_and]
        exact Finite.of_subsingleton
      · suffices IsEmpty (cell (D ∪ closedCell n i) m) by
          exact Finite.of_subsingleton
        simp only [RelCWComplex_RelSubcomplex, attach_base, coe_setOf, mem_setOf_eq, heq_eq_eq,
          Sigma.mk.inj_iff, isEmpty_subtype, not_and, _subcomplex]
        intro c eq
        contradiction}

@[simps!]
instance cellzero [T2Space X] [RelCWComplex C D] (i : cell C 0) :
  RelSubcomplex C (D ∪ closedCell 0 i) := attach_base 0 i (by simp [cellFrontier_zero_eq_empty])

@[simps]
instance cellzeroAB [T2Space X] [CWComplex C] (i : cell C 0) : Subcomplex C (closedCell 0 i) where
  I n := {x | HEq (⟨n, x⟩ : Σ n, cell C n) (⟨0, i⟩ : Σ n, cell C n)}
  closed := by
    rw [closedCell_zero_eq_singleton]
    exact isClosed_singleton
  union := by
    rw [empty_union]
    apply subset_antisymm
    · refine iUnion_subset fun n ↦ iUnion_subset fun ⟨j, eq⟩ ↦ ?_
      simp only [heq_eq_eq, Sigma.mk.inj_iff, mem_setOf_eq] at eq
      rcases eq with ⟨eq1, eq2⟩
      subst eq1
      rw [heq_eq_eq] at eq2
      subst eq2
      exact openCell_subset_closedCell 0 _
    · apply subset_iUnion_of_subset 0
      apply subset_iUnion_of_subset ⟨i, by simp only [heq_eq_eq, Sigma.mk.inj_iff, true_and,
        setOf_eq_eq_singleton, mem_singleton_iff]⟩
      simp only [closedCell_zero_eq_singleton, openCell_zero_eq_singleton, subset_singleton_iff,
        mem_singleton_iff, imp_self, implies_true]

instance finite_cellzero [T2Space X] [RelCWComplex C D] (i : cell C 0) :
    Finite (D ∪ closedCell 0 i) :=
  finite_attach_base 0 i (by simp [cellFrontier_zero_eq_empty])

instance finite_cellzeroAB [T2Space X] [CWComplex C] (i : cell C 0) :
    Finite (closedCell 0 i) where
  eventually_isEmpty_cell := by
    simp only [Filter.eventually_atTop, ge_iff_le]
    use 1
    intro b leb
    simp only [cellzeroAB, CWComplex_Subcomplex, RelCWComplex_RelSubcomplex, coe_setOf,
      mem_setOf_eq, heq_eq_eq, Sigma.mk.inj_iff, isEmpty_subtype, not_and]
    intro j eq
    subst eq
    contradiction
  finite_cell := by
    intro n
    simp_rw [cellzeroAB, CWComplex_Subcomplex, RelCWComplex_RelSubcomplex]
    by_cases h : n = 0
    · subst n
      simp only [heq_eq_eq, Sigma.mk.inj_iff, true_and, setOf_eq_eq_singleton]
      exact Finite.of_fintype _
    · rw [finite_coe_iff]
      suffices {x | HEq (⟨n, x⟩ : Σ n, cell C n) (⟨0, i⟩ : Σ n, cell C n)} = ∅ by
        rw [this]
        exact finite_empty
      apply eq_empty_of_forall_not_mem
      intro x xmem
      apply h
      simp only [heq_eq_eq, Sigma.mk.inj_iff, mem_setOf_eq] at xmem
      exact xmem.1

/-- The subcomplex that results from attaching a cell to a subcomplex when the edge of the cell is
  contained in the original subcomplex.-/
@[simps]
def attach_cell [T2Space X] [RelCWComplex C D] (n : ℕ) (i : cell C n) (E : Set X)
    [sub : RelSubcomplex C E]
    (subset : ∃ (I : Π m, Set (cell C m)), (∀ m < n, I m ⊆ sub.I m) ∧  cellFrontier n i ⊆
    (D ∪ ⋃ (m < n) (j ∈ I m), closedCell (C := C) m j)) :
    RelSubcomplex C (E ∪ openCell n i) where
  I l := {j : cell C l | j ∈ sub.I l ∨ (⟨l, j⟩ : Σ n, cell C n) = ⟨n, i⟩}
  closed := by
    suffices cellFrontier n i ⊆ E by
      rw [← union_eq_left.2 this, union_assoc, cellFrontier_union_openCell_eq_closedCell]
      exact sub.closed.union isClosed_closedCell
    obtain ⟨I, hI1, hI2⟩ := subset
    apply hI2.trans
    apply union_subset
    · exact base_subset_complex (C := E ⇂ C)
    rw [← Subcomplex.union_closedCell (C := C) (D := D) (E := E)]
    apply subset_union_of_subset_right
    exact iUnion_mono fun m ↦ iUnion_subset fun mltn ↦ iUnion_subset fun j ↦
      iUnion_subset fun jmem ↦ subset_iUnion_of_subset ⟨j, hI1 m mltn jmem⟩ (by rfl)
  union := by
    simp_rw [← sub.union, union_assoc]
    congrm D ∪ ?_
    ext x
    simp only [mem_iUnion, mem_union]
    constructor
    · intro ⟨m, ⟨j, jmem⟩, xmem⟩
      simp only [Sigma.mk.inj_iff, mem_setOf_eq] at jmem
      rcases jmem with jmem | ⟨eq1, eq2⟩
      · left
        use m, ⟨j, jmem⟩
      · right
        subst m
        rw [heq_eq_eq] at eq2
        subst j
        exact xmem
    · intro h
      rcases h with ⟨m, j, xmem⟩ | xmem
      · use m, ⟨j.1, Or.intro_left _ j.2⟩
      · use n, ⟨i, Or.intro_right _ rfl⟩

/-- The subcomplex that results from attaching a cell to a subcomplex when the edge of the cell is
  contained in the original subcomplex.-/
@[simps]
def attach_cellAB [T2Space X] [CWComplex C] (n : ℕ) (i : cell C n) (E : Set X)
    [sub : Subcomplex C E]
    (subset : ∃ (I : Π m, Set (cell C m)), (∀ m < n, I m ⊆ sub.I m) ∧  cellFrontier n i ⊆
    (⋃ (m < n) (j ∈ I m), closedCell (C := C) m j)) :
    Subcomplex C (E ∪ openCell n i) where
  I l := {j : cell C l | j ∈ sub.I l ∨ (⟨l, j⟩ : Σ n, cell C n) = ⟨n, i⟩}
  closed := by
    suffices cellFrontier n i ⊆ E by
      rw [← union_eq_left.2 this, union_assoc, cellFrontier_union_openCell_eq_closedCell]
      exact sub.closed.union isClosed_closedCell
    obtain ⟨I, hI1, hI2⟩ := subset
    apply hI2.trans
    rw [← Subcomplex.union_closedCell (C := C) (D := ∅) (E := E), empty_union]
    exact iUnion_mono fun m ↦ iUnion_subset fun mltn ↦ iUnion_subset fun j ↦
      iUnion_subset fun jmem ↦ subset_iUnion_of_subset ⟨j, hI1 m mltn jmem⟩ (by rfl)
  union := by
    rw [empty_union]
    ext x
    simp only [mem_iUnion, ← sub.union, mem_union]
    constructor
    · intro ⟨m, ⟨j, jmem⟩, xmem⟩
      simp only [Sigma.mk.inj_iff, mem_setOf_eq] at jmem
      rcases jmem with jmem | ⟨eq1, eq2⟩
      · left
        use m, ⟨j, jmem⟩
      · right
        subst m
        rw [heq_eq_eq] at eq2
        subst j
        exact xmem
    · intro h
      rcases h with ⟨m, j, xmem⟩ | xmem
      · use m, ⟨j.1, Or.intro_left _ j.2⟩
      · use n, ⟨i, Or.intro_right _ rfl⟩

lemma finiteDimensional_attach_cell [T2Space X] [RelCWComplex C D] (n : ℕ) (i : cell C n)
    (E : Set X) [sub : RelSubcomplex C E]
    [FiniteDimensional (E ⇂ C)] (subset : ∃ (I : Π m, Set (cell C m)),
    (∀ m < n, I m ⊆ sub.I m) ∧  cellFrontier n i ⊆
    (D ∪ ⋃ (m < n) (j ∈ I m), closedCell (C := C) m j)) :
    letI _subcomplex := attach_cell n i E subset
    FiniteDimensional ((E ∪ openCell n i) ⇂ C) :=
  let _subcomplex := attach_cell n i E subset
  {
  eventually_isEmpty_cell := by
    have := FiniteDimensional.eventually_isEmpty_cell (C := E ⇂ C) (D := D)
    simp only [Filter.eventually_atTop, ge_iff_le] at this ⊢
    obtain ⟨a, ha⟩ := this
    use a.max (n + 1)
    intro b le
    simp only [cell, attach_cell, Sigma.mk.inj_iff, coe_setOf, isEmpty_subtype, not_or,
      not_and] at ha ⊢
    intro x
    refine ⟨ha b (le_of_max_le_left le) x, ?_⟩
    aesop}

lemma finiteType_attach_cell [T2Space X] [RelCWComplex C D] (n : ℕ) (i : cell C n) (E : Set X)
    [sub : RelSubcomplex C E]
    [finite : FiniteType (E ⇂ C)] (subset : ∃ (I : Π m, Set (cell C m)),
    (∀ m < n, I m ⊆ sub.I m) ∧  cellFrontier n i ⊆
    (D ∪ ⋃ (m < n) (j ∈ I m), closedCell (C := C) m j)) :
    letI _subcomplex := attach_cell n i E subset
    FiniteType ((E ∪ openCell n i) ⇂ C) :=
  let _subcomplex := attach_cell n i E subset
  {
  finite_cell := by
    intro m
    by_cases h : m = n
    · subst m
      simp only [cell, attach_cell, Sigma.mk.inj_iff, setOf_or, heq_eq_eq, true_and, finite_coe_iff,
        finite_union, setOf_mem_eq, setOf_eq_eq_singleton]
      exact ⟨finite.finite_cell n, finite_singleton i⟩
    simp only [cell, attach_cell, Sigma.mk.inj_iff, setOf_or, setOf_mem_eq, setOf_and, h,
      setOf_false, empty_inter, finite_coe_iff, finite_union, finite_empty, and_true]
    exact finite.finite_cell m}

lemma finite_attach_cell [T2Space X] [RelCWComplex C D] (n : ℕ) (i : cell C n) (E : Set X)
    [sub : RelSubcomplex C E] [Finite (E ⇂ C)] (subset : ∃ (I : Π m, Set (cell C m)),
    (∀ m < n, I m ⊆ sub.I m) ∧  cellFrontier n i ⊆
    (D ∪ ⋃ (m < n) (j ∈ I m), closedCell (C := C) m j)) :
    letI _subcomplex := attach_cell n i E subset
    Finite ((E ∪ openCell n i) ⇂ C) :=
  let _subcomplex := attach_cell n i E subset
  let _finiteDimensional := finiteDimensional_attach_cell n i E subset
  let _finiteType := finiteType_attach_cell n i E subset
  inferInstance

lemma finiteDimensional_attach_cellAB [T2Space X] [CWComplex C] (n : ℕ) (i : cell C n) (E : Set X)
    [sub : Subcomplex C E] [FiniteDimensional (E ⇂ C)] (subset : ∃ (I : Π m, Set (cell C m)),
    (∀ m < n, I m ⊆ sub.I m) ∧ cellFrontier n i ⊆ (⋃ (m < n) (j ∈ I m), closedCell (C := C) m j)):
    let _subcomplex := attach_cellAB n i E subset
    FiniteDimensional (E ∪ openCell n i) := finiteDimensional_attach_cell n i E
  (by simp_rw [empty_union]; exact subset)

lemma finiteType_attach_cellAB [T2Space X] [CWComplex C] (n : ℕ) (i : cell C n) (E : Set X)
    [sub : Subcomplex C E] [FiniteType (E ⇂ C)] (subset : ∃ (I : Π m, Set (cell C m)),
    (∀ m < n, I m ⊆ sub.I m) ∧ cellFrontier n i ⊆ (⋃ (m < n) (j ∈ I m), closedCell (C := C) m j)):
    let _subcomplex := attach_cellAB n i E subset
    FiniteType (E ∪ openCell n i) := finiteType_attach_cell n i E
  (by simp_rw [empty_union]; exact subset)

lemma finite_attach_cellAB [T2Space X] [CWComplex C] (n : ℕ) (i : cell C n) (E : Set X)
    [sub : Subcomplex C E] [Finite (E ⇂ C)] (subset : ∃ (I : Π m, Set (cell C m)),
    (∀ m < n, I m ⊆ sub.I m) ∧ cellFrontier n i ⊆ (⋃ (m < n) (j ∈ I m), closedCell (C := C) m j)):
    let _subcomplex := attach_cellAB n i E subset
    Finite (E ∪ openCell n i) := finite_attach_cell n i E
  (by simp_rw [empty_union]; exact subset)

/-- Every cell is part of a finite subcomplex.-/
lemma cell_mem_finite_RelSubcomplex [T2Space X] [RelCWComplex C D] (n : ℕ) (i : cell C n) :
    ∃ (E : Set X) (subE : RelSubcomplex C E), Finite E ∧ i ∈ subE.I n := by
  induction' n using Nat.case_strong_induction_on with n hn
  · use (D ∪ closedCell 0 i), (Subcomplex.cellzero i)
    exact ⟨finite_cellzero i, by rfl⟩
  by_cases h : cellFrontier (n + 1) i ⊆ D
  · let _ := attach_base (n + 1) i h
    use D ∪ closedCell (n + 1) i, inferInstance
    refine ⟨finite_attach_base (n + 1) i h, ?_⟩
    simp
  obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell n.succ i
  choose sub cw hsub using hn
  let sub' := ⋃ (x : Σ (m : {m : ℕ // m ≤ n}), I m), sub x.1.1 x.1.2 ↑x.2.1
  have : Nonempty ((m : { m // m ≤ n }) × { x // x ∈ I ↑m }) := by
    simp only [nonempty_sigma, nonempty_subtype, Subtype.exists, exists_prop]
    have : ∃ x, x ∈ cellFrontier n.succ i ∩ ⋃ m, ⋃ (_ : m < n.succ), ⋃ j ∈ I m, closedCell m j := by
      by_contra h'
      push_neg at h'
      apply h
      intro x xmem
      rcases hI xmem with xmem' | xmem'
      · exact xmem'
      exfalso
      apply h' x
      exact mem_inter xmem xmem'
    obtain ⟨x, _, xmem⟩ := this
    simp only [Nat.succ_eq_add_one, mem_iUnion, exists_prop] at xmem
    obtain ⟨m, mlt, j, jmem, _⟩ := xmem
    use m, Nat.le_of_lt_succ mlt, j
  let cw' : RelSubcomplex C sub' := relSubcomplex_iUnion_RelSubcomplex _ _
  have : ∃ (I : Π m, Set (cell C m)),
      (∀ m < n.succ , I m ⊆ cw'.I m) ∧  cellFrontier n.succ i ⊆
      (D ∪ ⋃ (m < n.succ) (j ∈ I m), closedCell (C := C) (D := D) m j) := by
    use fun m ↦ I m
    refine ⟨?_, hI⟩
    intro m mltn x xmem
    simp only [relSubcomplex_iUnion_RelSubcomplex, RelSubcomplex', mem_iUnion, Sigma.exists,
      Subtype.exists, exists_prop, sub', cw']
    use m, Nat.lt_succ_iff.1 mltn, x, xmem
    exact (hsub m (Nat.lt_succ_iff.1 mltn) x).2
  use sub' ∪ openCell n.succ i, attach_cell n.succ i sub' this
  constructor
  · have : Finite (sub' ⇂ C) := finite_RelSubcomplex_finite_iUnion_finite_RelSubcomplex
     (finite := fun ⟨m, j⟩ ↦ (hsub m.1 m.2 j.1).1)
    exact finite_attach_cell n.succ i _ _
  · simp only [attach_cell, subcomplex_iUnion_subcomplex, Subcomplex', mem_iUnion, Sigma.exists,
    Subtype.exists, exists_prop, setOf_or, sub', cw']
    right
    rfl

lemma closedCell_subset_finite_RelSubcomplex [T2Space X] [RelCWComplex C D] (n : ℕ) (i : cell C n) :
    ∃ (E : Set X) (_subE : RelSubcomplex C E), Finite E ∧ closedCell n i ⊆ E := by
  obtain ⟨E, subE, hE1, hE2⟩ := cell_mem_finite_RelSubcomplex n i
  use E, subE
  refine ⟨hE1, ?_⟩
  rw [← Subcomplex.union_closedCell (C := C) (E := E)]
  apply subset_union_of_subset_right
  exact subset_iUnion_of_subset n (subset_iUnion_of_subset ⟨i, hE2⟩ (by rfl))

/-- Every finite set of cells is contained in some finite subcomplex.-/
lemma finite_iUnion_subset_RelSubcomplex [T2Space X] [RelCWComplex C D]
    (I : (n : ℕ) → Set (cell C n)) [finite : _root_.Finite (Σ n, I n)] :
    ∃ (E : Set X) (_sub : RelSubcomplex C E), CWComplex.Finite E ∧
    (⋃ (n : ℕ) (i : I n), map (C := C) (D := D) n i '' closedBall 0 1) ⊆ E := by
  by_cases nonempty : Nonempty (Σ n, I n)
  · choose sub cw finite subset using closedCell_subset_finite_RelSubcomplex (C := C) (D := D)
    use ⋃ (x : Σ n, I n), sub x.1 x.2, inferInstance
    constructor
    · exact finite_RelSubcomplex_finite_iUnion_finite_RelSubcomplex
        (finite := fun (x : Σ n, I n) ↦ finite x.1 x.2)
    · rw [iUnion_sigma]
      exact iUnion_mono fun n ↦ iUnion_mono fun i ↦ subset n i
  · use D, inferInstance
    refine ⟨finite_base, ?_⟩
    simp_all

/-- Every compact set in a CW-complex is contained in a finite subcomplex.-/
lemma compact_subset_finite_RelSubcomplex [T2Space X] [RelCWComplex C D] {B : Set X}
    (compact : IsCompact B) :
    ∃ (E : Set X) (_sub : RelSubcomplex C E), Finite E ∧ B ∩ C ⊆ E := by
  have : _root_.Finite (Σ n, { j | ¬Disjoint B (openCell (C:= C) n j)}) :=
    compact_inter_finite (C := C) (D := D) B compact
  obtain ⟨E, sub, finite, subset⟩ := finite_iUnion_subset_RelSubcomplex (C := C) (D := D)
    (fun n ↦ { j | ¬Disjoint B (openCell (C := C) n j)})
  use E,sub
  refine ⟨finite, ?_⟩
  apply subset_trans (subset_not_disjoint (C := C) (D := D) B)
  apply union_subset
  · exact base_subset_complex
  rw [iUnion_sigma]
  exact subset

/-- The levels of a CW-complex constitute subcomplexes. -/
@[simps!]
instance RelSubcomplex_levelaux [T2Space X] [RelCWComplex C D] (n : ℕ∞) :
    RelSubcomplex C (levelaux C n) :=
  RelSubcomplex'' _ (levelaux C n)
  (fun l ↦ {x : cell C l | l < n})
  (by
    rw [← iUnion_openCell_eq_levelaux]
    congrm D ∪ ?_
    apply iUnion_congr fun m ↦ ?_
    simp_rw [iUnion_subtype, mem_setOf_eq]
    rw [iUnion_comm])

/-- The levels of a CW-complex constitute subcomplexes. -/
@[simps!]
instance RelSubcomplex_level [T2Space X] [RelCWComplex C D] (n : ℕ∞) :
  RelSubcomplex C (level C n) := RelSubcomplex_levelaux _

end Subcomplex

end

end CWComplex
