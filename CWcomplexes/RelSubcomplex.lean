import CWcomplexes.RelFinite
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

## Notation
* `E ⇂ C`: `E` is a subcomplex of the CW-complex `C`.

## References
* [K. Jänich, *Topology*]
-/

noncomputable section

open Metric Set

namespace Topology

variable {X : Type*} [t : TopologicalSpace X] {C D : Set X}

lemma RelCWComplex.Subcomplex.subset_complex [RelCWComplex C D] (E : Subcomplex C) :
    (E : Set X) ⊆ C := by
  simp_rw [← E.union, ← union_iUnion_openCell_eq_complex (C := C) (D := D)]
  apply union_subset_union_right D
  exact iUnion_mono fun n ↦ iUnion_subset fun i ↦ by apply subset_iUnion_of_subset ↑i; rfl

/-- A subcomplex is the union of its closed cells.-/
lemma RelCWComplex.Subcomplex.union_closedCell [T2Space X] [RelCWComplex C D] (E : Subcomplex C):
    D ∪ ⋃ (n : ℕ) (j : E.I n), closedCell (C := C) n j = E := by
  apply subset_antisymm
  · apply union_subset
    · rw [← Subcomplex.union (C := C) (D := D) (E := E)]
      exact subset_union_left
    · apply iUnion_subset fun n ↦ iUnion_subset fun i ↦ ?_
      rw [← closure_openCell_eq_closedCell, E.closed.closure_subset_iff, ← E.union]
      apply subset_union_of_subset_right
      exact subset_iUnion_of_subset n
        (subset_iUnion (fun (i : ↑(E.I n)) ↦ openCell (C := C) (D := D) n ↑i) i)
  · simp_rw [← E.union]
    apply union_subset_union_right
    apply iUnion_mono fun n ↦ iUnion_mono fun (i : ↑(E.I n)) ↦ ?_
    exact openCell_subset_closedCell (C := C) (D := D) n i

/-- A subcomplex is the union of its closed cells.-/
lemma CWComplex.Subcomplex.union_closedCell [T2Space X] [CWComplex C] (E : Subcomplex C) :
    ⋃ (n : ℕ) (j : E.I n), closedCell (C := C) n j = E := by
  apply subset_antisymm
  · apply iUnion_subset fun n ↦ iUnion_subset fun i ↦ ?_
    simp_rw [← closure_openCell_eq_closedCell, (Subcomplex.closed E).closure_subset_iff,
      ← E.union (C := C), empty_union]
    exact subset_iUnion_of_subset n
      (subset_iUnion (fun (i : ↑(E.I n)) ↦ openCell (C := C) (D := ∅) n ↑i) i)
  · simp_rw [← Topology.CWComplex.Subcomplex.union (C := C)]
    apply iUnion_mono fun n ↦ iUnion_mono fun (i : ↑(E.I n)) ↦ ?_
    exact openCell_subset_closedCell (C := C) (D := ∅) n i

open RelCWComplex.Subcomplex in
/-- A subcomplex is again a CW-complex. -/
@[simps]
instance RelCWComplex.Subcomplex.instSubcomplex [T2Space X] [RelCWComplex C D] (E : Subcomplex C) :
    RelCWComplex E D where
  cell n := E.I n
  map n i := map (C := C) n i
  source_eq n i := source_eq (C := C) n i
  continuousOn n i := continuousOn (C := C) n i
  continuousOn_symm n i := continuousOn_symm (C := C) n i
  pairwiseDisjoint' := by
    simp only [PairwiseDisjoint, Set.Pairwise, mem_univ, ne_eq, Function.onFun,
      disjoint_iff_inter_eq_empty, true_implies, Sigma.forall, Subtype.forall,
      not_and]
    intro n j _ m i _ eq
    refine (disjoint_openCell_of_ne ?_).inter_eq
    simp_all only [Sigma.mk.inj_iff, not_and, ne_eq]
    intro a
    subst a
    simp_all only [heq_eq_eq, Subtype.mk.injEq, forall_const, not_false_eq_true]
  disjointBase' := fun n i ↦ RelCWComplex.disjointBase' (C := C) (D := D) n i
  mapsTo := by
    intro n i
    rcases cellFrontier_subset_finite_openCell (C := C) (D := D) n i with ⟨J, hJ⟩
    use fun m ↦ Finset.preimage (J m) (fun (x : E.I m) ↦ ↑x) (by simp [InjOn])
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
    suffices j ∈ E.I m by
      use this
      simp only [Finset.mem_preimage, jmem]
    have : x ∈ (E : Set X) := by
      rw [← Subcomplex.union_closedCell (C := C) (D := D) (E := E)]
      right
      refine mem_of_subset_of_mem ?_ xmem
      refine subset_iUnion_of_subset n (subset_iUnion_of_subset ↑i ?_)
      exact cellFrontier_subset_closedCell (C := C)  (D := D) n ↑i
    simp only [← E.union, iUnion_coe_set, mem_union, h, mem_iUnion, exists_prop,
      false_or] at this
    obtain ⟨l, o, xmemopen'⟩ := this
    suffices (⟨m, j⟩ : Σ n, cell C n) = ⟨l, ↑o⟩ by aesop
    apply eq_of_not_disjoint_openCell
    rw [not_disjoint_iff]
    use x
    exact ⟨xmemopen, xmemopen'.2⟩
  closed' A Asub closed := by
    apply isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell (D := D)
      (subset_trans Asub (Subcomplex.subset_complex (C := C) (D := D) E)) closed.2
    intro n _ j
    by_cases h : j ∈ E.I n
    · exact Or.intro_right _ (closed.1 n ⟨j, h⟩)
    left
    suffices A ∩ openCell n j = ∅ by
      rw [this]
      exact isClosed_empty
    rw [← subset_empty_iff]
    apply subset_trans (inter_subset_inter_left _ Asub)
    simp_rw [← E.union, subset_empty_iff, union_inter_distrib_right, iUnion_inter,
      union_empty_iff]
    constructor
    · rw [inter_comm]
      exact (RelCWComplex.disjointBase' n j).inter_eq
    · exact iUnion_eq_empty.2 fun m ↦ iUnion_eq_empty.2 fun i ↦
        (disjoint_openCell_of_ne (by aesop)).inter_eq
  isClosedBase := RelCWComplex.isClosedBase (C := C) (D := D)
  union' := Subcomplex.union_closedCell E (D := D)

/-- A subcomplex is again a CW-complex. -/
instance CWComplex.Subcomplex.instSubcomplex [T2Space X] [CWComplex C] (E : Subcomplex C) :
    CWComplex (E : Set X) :=
  RelCWComplex.Subcomplex.instSubcomplex (C := C) E

@[simp]
lemma CWComplex.Subcomplex.instSubcomplex_cell [T2Space X] [CWComplex C] (E : Subcomplex C)
    (n : ℕ) : cell (E : Set X) n = E.I (C := C) n :=
  rfl

@[simp]
lemma CWComplex.Subcomplex.instSubcomplex_map [T2Space X] [CWComplex C] (E : Subcomplex C) (n : ℕ)
    (i : E.I n) : map (C := E) n i = map (C := C) n i :=
  rfl

instance RelCWComplex.Subcomplex.finiteType_subcomplex_of_finiteType [T2Space X]
    [RelCWComplex C D] [FiniteType C] (E : Subcomplex C) : FiniteType (E : Set X) where
  finite_cell n :=
    let _ := FiniteType.finite_cell (C := C) (D := D) n
    toFinite (E.I n)

instance RelCWComplex.Subcomplex.finiteDimensional_subcomplex_of_finiteDimensional
    [T2Space X] [RelCWComplex C D] [FiniteDimensional C] (E : Subcomplex C) :
    FiniteDimensional (E : Set X) where
  eventually_isEmpty_cell := by
    have := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)
    simp only [Filter.eventually_atTop, ge_iff_le] at this ⊢
    obtain ⟨n, hn⟩ := this
    use n
    intro b nleb
    simp only [instSubcomplex, isEmpty_subtype, hn b nleb, IsEmpty.forall_iff]

/-- A subcomplex of a finite CW-complex is again finite.-/
instance RelCWComplex.Subcomplex.finite_subcomplex_of_finite [T2Space X] [RelCWComplex C D]
    [Finite C] (E : Subcomplex C) : Finite (E : Set X) :=
  inferInstance

section TopBot

@[simps]
instance RelCWComplex.Subcomplex.instTop [T2Space X] [RelCWComplex C D] :
    Top (Subcomplex C) := ⟨{
    carrier := C
    I n := univ
    closed' := isClosed
    union' := by simp [← union_iUnion_openCell_eq_complex]
  }⟩

@[simps]
instance RelCWComplex.Subcomplex.instBot [RelCWComplex C D] :
    Bot (Subcomplex C) := ⟨{
      carrier := D
      I n := ∅
      closed' := isClosedBase C
      union' := by simp
    }⟩

instance RelCWComplex.Subcomplex.finite_instBot [T2Space X] [RelCWComplex C D] :
    Finite ((⊥ : Subcomplex C) : Set X) where
  eventually_isEmpty_cell := by
    simp only [instBot_bot_carrier, Filter.eventually_atTop, ge_iff_le]
    use 0
    intro b _
    simp [instSubcomplex]
  finite_cell := by
    intro n
    simp only [instSubcomplex_cell, mk''_I]
    exact Finite.of_subsingleton

end TopBot

section SupSet

instance RelCWComplex.Subcomplex.instSupSet [T2Space X] [RelCWComplex C D] :
    SupSet (Subcomplex C) where
  sSup := fun S ↦ mk' C (D ∪ ⋃ (E ∈ S), E) (fun n ↦ ⋃ (E ∈ S), E.I n)
    (by
      intro n ⟨i, hi⟩
      apply subset_union_of_subset_right
      simp_rw [mem_iUnion] at hi
      obtain ⟨E, hE, hEj⟩ := hi
      apply subset_iUnion_of_subset E
      apply subset_iUnion_of_subset hE
      rw [← E.union_closedCell (C := C)]
      apply subset_union_of_subset_right
      exact subset_iUnion_of_subset n (subset_iUnion
        (fun (j : ↑(E.I n)) ↦ closedCell (C := C) n ↑j) ⟨i, hEj⟩))
    (by
      simp_rw [← Subcomplex.union]
      rw [← iUnion_subtype (p := fun E ↦ E ∈ S)
        (s := fun E ↦ D ∪ ⋃ n, ⋃ (j : E.1.I n), openCell n j.1)]
      by_cases h : Nonempty S
      · rw [← union_iUnion, ← union_assoc, union_self, iUnion_comm]
        congrm D ∪ ?_
        apply iUnion_congr fun n ↦ ?_
        simp_rw [iUnion_subtype, mem_iUnion, iUnion_exists]
        rw [iUnion_comm]
        apply iUnion_congr fun E ↦ ?_
        rw [iUnion_comm]
      · simp_all only [nonempty_subtype, not_exists, iUnion_of_empty, iUnion_empty,
        isEmpty_coe_sort, union_empty, mk''_I, iUnion_coe_set, eq_mp_eq_cast, id_eq,
        not_isEmpty_of_nonempty])

-- its annoying to have to write it like this. Notation?
lemma RelCWComplex.Subcomplex.instSupSet_carrier [T2Space X] [RelCWComplex C D]
    {J : Type*} (sub : J → Subcomplex C) :
    (((⨆ (j : J), sub j) : Subcomplex C) : Set X) = D ∪ ⋃ j, sub j := by
  unfold instSupSet mk' iSup
  simp [coe_eq_carrier]

@[simp] lemma RelCWComplex.Subcomplex.instSupSet_coe_eq_of_nonempty [T2Space X] [RelCWComplex C D]
    {J : Type*} [Nonempty J] (sub : J → Subcomplex C) :
    (((⨆ (j : J), sub j) : Subcomplex C) : Set X) = ⋃ j, sub j := by
  simp only [instSupSet_carrier, union_eq_right]
  apply subset_iUnion_of_subset (Classical.choice (α := J) inferInstance)
  exact base_subset_complex

@[simp] lemma RelCWComplex.Subcomplex.instSupSet_coe_eq_of_empty [T2Space X] [RelCWComplex C D]
    {J : Type*} [IsEmpty J] (sub : J → Subcomplex C) :
    ⨆ (j : J), sub j = ⊥ := by
  ext x
  simp only [mem, instSupSet_carrier, instBot_bot_carrier, iUnion_of_empty, union_empty]

@[simp]
lemma CWComplex.Subcomplex.instSupSet_carrier [T2Space X] [CWComplex C]
    {J : Type*} (sub : J → Subcomplex C) :
    (((⨆ (j : J), sub j) : Subcomplex C) : Set X) = ⋃ j, sub j := by
  unfold RelCWComplex.Subcomplex.instSupSet RelCWComplex.Subcomplex.mk' iSup
  simp [coe_eq_carrier]

@[simp]
lemma RelCWComplex.Subcomplex.instSupSet_I [T2Space X] [RelCWComplex C D]
    {J : Type*} (sub : J → Subcomplex C) (n : ℕ) :
    (⨆ (j : J), sub j).I n = ⋃ (j : J), (sub j).I n := by
  simp

/-- A finite union of finite-dimensional subcomplexes is again a finite-dimensional subcomplex.-/
instance RelCWComplex.Subcomplex.finiteDimensional_finite_iSupSubcomplex_of_finiteDimensional
    [T2Space X] [RelCWComplex C D] {J : Type*} [_root_.Finite J]
    {sub : J → Subcomplex C}
    [finite : ∀ (j : J), FiniteDimensional (sub j : Set X)] :
    FiniteDimensional (((⨆ j : J, sub j) : Subcomplex C) : Set X) where
  eventually_isEmpty_cell := by
    have h j := (finite j).eventually_isEmpty_cell
    simp only [instSubcomplex_cell, isEmpty_coe_sort, Filter.eventually_iff, Filter.mem_atTop_sets,
      ge_iff_le, mem_setOf_eq, mk''_I, mem_range, iUnion_exists, iUnion_iUnion_eq', iUnion_eq_empty,
      setOf_forall, Filter.iInter_mem] at h ⊢
    exact h

/-- A finite union of subcomplexes of finite type is again a subcomplex of finite type.-/
instance RelCWComplex.Subcomplex.finiteType_finite_iSupSubComplex_of_finiteType [T2Space X]
    [RelCWComplex C D] {J : Type*} [_root_.Finite J] {sub : J → Subcomplex C}
    [finite : ∀ (j : J), FiniteType (sub j : Set X)] :
    FiniteType ((⨆ j, sub j : Subcomplex C) : Set X) where
 finite_cell := by
    have h j := (finite j).finite_cell
    intro n
    simp only [instSubcomplex_cell, mk''_I, mem_range, iUnion_exists, iUnion_iUnion_eq'] at h ⊢
    apply Finite.Set.finite_iUnion

end SupSet

section InfSet

-- ## TODO

end InfSet

/-- A cell whose boundary is in th base forms a subcomplex together with the base.-/
def RelCWComplex.Subcomplex.attachBase [T2Space X] [RelCWComplex C D] (n : ℕ) (i : cell C n)
    (hD: cellFrontier n i ⊆ D) :
    Subcomplex C  where
  carrier := D ∪ closedCell n i
  I m := {x | HEq (⟨m, x⟩ : Σ m, cell C m) (⟨n, i⟩ : Σ n, cell C n)}
  closed' := (isClosedBase C).union isClosed_closedCell
  union' := by
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

lemma RelCWComplex.Subcomplex.attachBase_I [T2Space X] [RelCWComplex C D] (n : ℕ)
    (i : cell C n) (hD : cellFrontier n i ⊆ D) (m : ℕ) :
    (attachBase n i hD).I m = {x | HEq (⟨m, x⟩ : Σ m, cell C m) (⟨n, i⟩ : Σ n, cell C n)} :=
  rfl

lemma RelCWComplex.Subcomplex.finite_attachBase [T2Space X] [RelCWComplex C D] (n : ℕ)
    (i : cell C n) (hD: cellFrontier n i ⊆ D) :
    Finite (attachBase n i hD : Set X) where
  eventually_isEmpty_cell := by
      simp only [Filter.eventually_atTop, ge_iff_le]
      use n.succ
      intro b le
      simp only [instSubcomplex_cell, mk''_I, heq_eq_eq, Sigma.mk.inj_iff, coe_setOf,
        isEmpty_subtype, not_and]
      intro j h
      subst h
      exfalso
      exact Nat.not_succ_le_self b le
  finite_cell := by
      intro m
      by_cases h : m = n
      · subst m
        simp only [instSubcomplex_cell, mk''_I, heq_eq_eq, Sigma.mk.inj_iff, true_and,
          setOf_eq_eq_singleton]
        exact Finite.of_subsingleton
      · suffices IsEmpty (cell (attachBase n i hD : Set X) m) by
          exact Finite.of_subsingleton
        simp only [instSubcomplex_cell, mk''_I, heq_eq_eq, Sigma.mk.inj_iff, coe_setOf,
          isEmpty_subtype, not_and]
        intro c eq
        contradiction

@[simps!]
def RelCWComplex.Subcomplex.cellZero [T2Space X] [RelCWComplex C D] (i : cell C 0) :
  Subcomplex C := attachBase 0 i (by simp [cellFrontier_zero_eq_empty])

@[simps]
instance CWComplex.Subcomplex.cellZero [T2Space X] [CWComplex C] (i : cell C 0) :
    Subcomplex C where
  carrier := closedCell 0 i
  I n := {x | HEq (⟨n, x⟩ : Σ n, cell C n) (⟨0, i⟩ : Σ n, cell C n)}
  closed' := by
    rw [closedCell_zero_eq_singleton]
    exact isClosed_singleton
  union' := by
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

instance RelCWComplex.Subcomplex.finite_cellZero [T2Space X] [RelCWComplex C D] (i : cell C 0) :
    Finite (cellZero i : Set X) :=
  finite_attachBase 0 i (by simp [cellFrontier_zero_eq_empty])

instance CWComplex.Subcomplex.finite_cellZero [T2Space X] [CWComplex C] (i : cell C 0) :
    Finite (cellZero i : Set X) where
  eventually_isEmpty_cell := by
    simp only [Filter.eventually_atTop, ge_iff_le]
    use 1
    intro b leb
    simp only [RelCWComplex.Subcomplex.instSubcomplex_cell, RelCWComplex.Subcomplex.mk''_I,
      heq_eq_eq, Sigma.mk.inj_iff, coe_setOf, isEmpty_subtype, not_and]
    intro j eq
    subst eq
    contradiction
  finite_cell := by
    intro n
    simp only [RelCWComplex.Subcomplex.instSubcomplex_cell, RelCWComplex.Subcomplex.mk''_I]
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

open RelCWComplex.Subcomplex in
/-- The subcomplex that results from attaching a cell to a subcomplex when the edge of the cell is
  contained in the original subcomplex.-/
def RelCWComplex.Subcomplex.attachCell [T2Space X] [RelCWComplex C D] (n : ℕ) (i : cell C n)
    (E : Subcomplex C)
    (subset : ∃ (I : Π m, Set (cell C m)), (∀ m < n, I m ⊆ E.I m) ∧  cellFrontier n i ⊆
      (D ∪ ⋃ (m < n) (j ∈ I m), closedCell (C := C) m j)) :
    Subcomplex C where
  carrier := E ∪ openCell n i
  I l := {j : cell C l | j ∈ E.I l ∨ (⟨l, j⟩ : Σ n, cell C n) = ⟨n, i⟩}
  closed' := by
    suffices cellFrontier n i ⊆ E by
      rw [← union_eq_left.2 this, union_assoc, cellFrontier_union_openCell_eq_closedCell]
      exact E.closed.union isClosed_closedCell
    obtain ⟨I, hI1, hI2⟩ := subset
    apply hI2.trans
    apply union_subset
    · exact base_subset_complex (C := (E : Set X))
    rw [← Subcomplex.union_closedCell (C := C) (D := D) (E := E)]
    apply subset_union_of_subset_right
    exact iUnion_mono fun m ↦ iUnion_subset fun mltn ↦ iUnion_subset fun j ↦
      iUnion_subset fun jmem ↦ subset_iUnion_of_subset ⟨j, hI1 m mltn jmem⟩ (by rfl)
  union' := by
    simp_rw [← E.union, union_assoc]
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

lemma RelCWComplex.Subcomplex.attachCell_I [T2Space X] [RelCWComplex C D] (n : ℕ)
    (i : cell C n) (E : Subcomplex C)
    (subset : ∃ (I : Π m, Set (cell C m)), (∀ m < n, I m ⊆ E.I m) ∧
      cellFrontier n i ⊆ D ∪ ⋃ m, ⋃ (_ : m < n), ⋃ j ∈ I m, closedCell m j) (l : ℕ) :
    (attachCell n i E subset).I l =
    {j | j ∈ E.I l ∨ (⟨l, j⟩ : Σ n, cell C n) = ⟨n, i⟩} := by
  rfl

/-- The subcomplex that results from attaching a cell to a subcomplex when the edge of the cell is
contained in the original subcomplex.-/
def CWComplex.Subcomplex.attachCell [T2Space X] [CWComplex C] (n : ℕ) (i : cell C n)
    (E : Subcomplex C)
    (subset : ∃ (I : Π m, Set (cell C m)), (∀ m < n, I m ⊆ E.I m) ∧  cellFrontier n i ⊆
      (⋃ (m < n) (j ∈ I m), closedCell (C := C) m j)) :
    Subcomplex C where
  carrier := E ∪ openCell n i
  I l := {j : cell C l | j ∈ E.I l ∨ (⟨l, j⟩ : Σ n, cell C n) = ⟨n, i⟩}
  closed' := by
    suffices cellFrontier n i ⊆ E by
      rw [← union_eq_left.2 this, union_assoc, cellFrontier_union_openCell_eq_closedCell]
      exact E.closed.union isClosed_closedCell
    obtain ⟨I, hI1, hI2⟩ := subset
    apply hI2.trans
    rw [← union_closedCell (C := C) (E := E)]
    exact iUnion_mono fun m ↦ iUnion_subset fun mltn ↦ iUnion_subset fun j ↦
      iUnion_subset fun jmem ↦ subset_iUnion_of_subset ⟨j, hI1 m mltn jmem⟩ (by rfl)
  union' := by
    rw [empty_union]
    ext x
    simp only [mem_iUnion, ← Topology.CWComplex.Subcomplex.union (C := C) (E := E), mem_union]
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

lemma CWComplex.Subcomplex.attachCell_I [T2Space X] [CWComplex C] (n : ℕ)
    (i : cell C n) (E : Subcomplex C)
    (subset : ∃ (I : Π m, Set (cell C m)), (∀ m < n, I m ⊆ E.I m) ∧
      cellFrontier n i ⊆ ⋃ m, ⋃ (_ : m < n), ⋃ j ∈ I m, closedCell m j)
    (l : ℕ) :
    (attachCell n i E subset).I l =
    {j | j ∈ E.I l ∨ (⟨l, j⟩ : Σ n, cell C n) = ⟨n, i⟩} :=
  rfl

lemma RelCWComplex.Subcomplex.finiteDimensional_attachCell [T2Space X] [RelCWComplex C D] (n : ℕ)
    (i : cell C n) (E : Subcomplex C)
    [FiniteDimensional (E : Set X)] (subset : ∃ (I : Π m, Set (cell C m)),
      (∀ m < n, I m ⊆ E.I m) ∧  cellFrontier n i ⊆
      (D ∪ ⋃ (m < n) (j ∈ I m), closedCell (C := C) m j)) :
    FiniteDimensional (attachCell n i E subset : Set X) where
  eventually_isEmpty_cell := by
    have := FiniteDimensional.eventually_isEmpty_cell (C := E) (D := D)
    simp only [Filter.eventually_atTop, ge_iff_le] at this ⊢
    obtain ⟨a, ha⟩ := this
    use a.max (n + 1)
    intro b le
    simp only [instSubcomplex_cell, isEmpty_subtype, mk''_I, Sigma.mk.inj_iff, coe_setOf, not_or,
      not_and] at ha ⊢
    intro x
    refine ⟨ha b (le_of_max_le_left le) x, ?_⟩
    aesop

lemma RelCWComplex.Subcomplex.finiteType_attachCell [T2Space X] [RelCWComplex C D] (n : ℕ)
    (i : cell C n) (E : Subcomplex C)
    [finite : FiniteType (E : Set X)] (subset : ∃ (I : Π m, Set (cell C m)),
    (∀ m < n, I m ⊆ E.I m) ∧  cellFrontier n i ⊆
    (D ∪ ⋃ (m < n) (j ∈ I m), closedCell (C := C) m j)) :
    letI _subcomplex := attachCell n i E subset
    FiniteType (attachCell n i E subset : Set X) where
  finite_cell := by
    intro m
    by_cases h : m = n
    · subst m
      simp only [instSubcomplex_cell, attachCell_I, Sigma.mk.inj_iff, heq_eq_eq, true_and, setOf_or,
        setOf_mem_eq, setOf_eq_eq_singleton, finite_coe_iff, finite_union]
      exact ⟨finite.finite_cell n, finite_singleton i⟩
    simp only [instSubcomplex_cell, mk''_I, Sigma.mk.inj_iff, h, false_and, or_false, setOf_mem_eq,
      finite_coe_iff]
    exact finite.finite_cell m

lemma RelCWComplex.Subcomplex.finite_attachCell [T2Space X] [RelCWComplex C D] (n : ℕ)
    (i : cell C n) (E : Subcomplex C) [Finite (E : Set X)] (subset : ∃ (I : Π m, Set (cell C m)),
      (∀ m < n, I m ⊆ E.I m) ∧  cellFrontier n i ⊆
      (D ∪ ⋃ (m < n) (j ∈ I m), closedCell (C := C) m j)) :
    Finite (attachCell n i E subset : Set X) :=
  let _ := finiteDimensional_attachCell n i E subset
  let _ := finiteType_attachCell n i E subset
  inferInstance

lemma CWComplex.Subcomplex.finiteDimensional_attachCell [T2Space X] [CWComplex C] (n : ℕ)
    (i : cell C n) (E : Subcomplex C) [FiniteDimensional (E : Set X)]
    (subset : ∃ (I : Π m, Set (cell C m)),
      (∀ m < n, I m ⊆ E.I m) ∧ cellFrontier n i ⊆ (⋃ (m < n) (j ∈ I m), closedCell (C := C) m j)):
    FiniteDimensional (attachCell n i E subset : Set X) :=
      RelCWComplex.Subcomplex.finiteDimensional_attachCell n i E
  (by simp_rw [empty_union]; exact subset)

lemma CWComplex.Subcomplex.finiteType_attachCell [T2Space X] [CWComplex C] (n : ℕ)
    (i : cell C n) (E : Subcomplex C) [FiniteType (E : Set X)]
    (subset : ∃ (I : Π m, Set (cell C m)),
      (∀ m < n, I m ⊆ E.I m) ∧ cellFrontier n i ⊆ (⋃ (m < n) (j ∈ I m), closedCell (C := C) m j)):
    FiniteType (attachCell n i E subset: Set X) :=
  RelCWComplex.Subcomplex.finiteType_attachCell n i E
    (by simp_rw [empty_union]; exact subset)

lemma CWComplex.Subcomplex.finite_attachCell [T2Space X] [CWComplex C] (n : ℕ)
    (i : cell C n) (E : Subcomplex C) [Finite (E : Set X)] (subset : ∃ (I : Π m, Set (cell C m)),
      (∀ m < n, I m ⊆ E.I m) ∧ cellFrontier n i ⊆ (⋃ (m < n) (j ∈ I m), closedCell (C := C) m j)):
    Finite (attachCell n i E subset : Set X) := RelCWComplex.Subcomplex.finite_attachCell n i E
  (by simp_rw [empty_union]; exact subset)

/-- Every cell is part of a finite subcomplex.-/
lemma RelCWComplex.Subcomplex.cell_mem_finite_subcomplex [T2Space X] [RelCWComplex C D]
    (n : ℕ) (i : cell C n) :
    ∃ (E : Subcomplex C), Finite (E : Set X) ∧ i ∈ E.I n := by
  induction' n using Nat.case_strong_induction_on with n hn
  · use (Subcomplex.cellZero i)
    exact ⟨finite_cellZero i, by rfl⟩
  by_cases h : cellFrontier (n + 1) i ⊆ D
  · use (attachBase (n + 1) i h)
    refine ⟨finite_attachBase (n + 1) i h, ?_⟩
    simp
  obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell n.succ i
  choose sub cw hsub using hn
  let sub' := ⨆ (x : Σ (m : {m : ℕ // m ≤ n}), I m), sub x.1.1 x.1.2 ↑x.2.1
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
  have : ∃ (I : Π m, Set (cell C m)),
      (∀ m < n.succ , I m ⊆ sub'.I m) ∧ cellFrontier n.succ i ⊆
      (D ∪ ⋃ (m < n.succ) (j ∈ I m), closedCell (C := C) (D := D) m j) := by
    use fun m ↦ I m
    refine ⟨?_, hI⟩
    intro m mltn x xmem
    simp only [sub', instSupSet_I]
    simp only [mem_iUnion, Sigma.exists, Subtype.exists, sub']
    use m, Nat.lt_succ_iff.1 mltn, x, xmem
    exact hsub m (Nat.lt_succ_iff.1 mltn) x
  use attachCell n.succ i sub' this
  refine ⟨finite_attachCell n.succ i _ _, ?_⟩
  simp only [attachCell_I, setOf_or, sub']
  right
  rfl

lemma RelCWComplex.Subcomplex.closedCell_subset_finite_subcomplex [T2Space X] [RelCWComplex C D]
    (n : ℕ) (i : cell C n) :
    ∃ (E : Subcomplex C) , Finite (E : Set X) ∧ closedCell n i ⊆ E := by
  obtain ⟨E, hE1, hE2⟩ := cell_mem_finite_subcomplex n i
  use E
  refine ⟨hE1, ?_⟩
  rw [← Subcomplex.union_closedCell (C := C) (E := E)]
  apply subset_union_of_subset_right
  exact subset_iUnion_of_subset n (subset_iUnion_of_subset ⟨i, hE2⟩ (by rfl))

/-- Every finite set of cells is contained in some finite subcomplex.-/
lemma RelCWComplex.Subcomplex.finite_iUnion_subset_finite_subcomplex [T2Space X] [RelCWComplex C D]
    (I : (n : ℕ) → Set (cell C n)) [finite : _root_.Finite (Σ n, I n)] :
    ∃ (E : Subcomplex C), Finite (E : Set X) ∧
    (⋃ (n : ℕ) (i : I n), map (C := C) (D := D) n i '' closedBall 0 1) ⊆ E := by
  by_cases nonempty : Nonempty (Σ n, I n)
  · choose sub finite subset using closedCell_subset_finite_subcomplex (C := C) (D := D)
    use ⨆ (x : Σ n, I n), sub x.1 x.2, inferInstance
    rw [instSupSet_coe_eq_of_nonempty, iUnion_sigma]
    exact iUnion_mono fun n ↦ iUnion_mono fun i ↦ subset n i
  · use ⊥, inferInstance
    simp_all

namespace CWComplex.Subcomplex

export RelCWComplex.Subcomplex (subset_complex finiteType_subcomplex_of_finiteType
  finiteDimensional_subcomplex_of_finiteDimensional finite_subcomplex_of_finite
  instTop instTop_top_carrier instBot instBot_bot_carrier finite_instBot instSupSet instSupSet_I
  finiteDimensional_finite_iSupSubcomplex_of_finiteDimensional
  finiteType_finite_iSupSubComplex_of_finiteType
  cell_mem_finite_subcomplex closedCell_subset_finite_subcomplex
  finite_iUnion_subset_finite_subcomplex)

end CWComplex.Subcomplex

end Topology
