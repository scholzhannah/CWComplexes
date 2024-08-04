import CWcomplexes.Lemmas
import Mathlib.Analysis.NormedSpace.Real

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open Metric Set

namespace CWComplex

variable {X : Type*} [t : TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

section

class Subcomplex (C : Set X) [CWComplex C] (E : Set X) where
  I : Π n, Set (cell C n)
  closed : IsClosed E
  union : ⋃ (n : ℕ) (j : I n), openCell (C := C) n j = E

/- See "Topologie" p. 120 by Klaus Jänich from 2001 -/
def Subcomplex' (C : Set X) [CWComplex C] (E : Set X) (I : Π n, Set (cell C n))
    (closedCell_subset : ∀ (n : ℕ) (i : I n), closedCell (C := C) n i ⊆ E)
    (union : ⋃ (n : ℕ) (j : I n), openCell (C := C) n j = E) : Subcomplex C E where
  I := I
  closed := by
    have EsubC : E ⊆ C := by -- extract a lemma here?
      simp_rw [← union, ← union_openCell]
      exact iUnion_mono fun n ↦ iUnion_subset fun i ↦ by apply subset_iUnion_of_subset ↑i; rfl
    apply strong_induction_isClosed EsubC
    intro n _ j
    by_cases h : j ∈ I n
    · right
      suffices closedCell n j ⊆ E by
        rw [inter_eq_right.2 this]
        exact isClosed_closedCell
      exact closedCell_subset n ⟨j, h⟩
    · left
      simp_rw [← union, iUnion_inter]
      suffices ⋃ m, ⋃ (i : ↑(I m)), openCell m (i : cell C m) ∩ openCell (C := C) n j = ∅ by
        rw [this]
        exact isClosed_empty
      apply iUnion_eq_empty.2 fun m ↦ iUnion_eq_empty.2 fun i ↦ ?_
      apply disjoint_openCell_of_ne
      aesop
  union := union

/- See "Topologie" p. 120 by Klaus Jänich from 2001 -/
def Subcomplex'' (C : Set X) [CWComplex C] (E : Set X) (I : Π n, Set (cell C n))
    (cw : CWComplex E) (hI : (n : ℕ) → cw.cell n = ↑(I n)) -- this probably needs to be stated differently...
    (union : ⋃ (n : ℕ) (j : I n), openCell (C := C) n j = E) : Subcomplex C E := Subcomplex' C E I
  (by
    sorry
  )
  union

namespace Subcomplex

lemma subset_complex (E : Set X) [subcomplex : Subcomplex C E] : E ⊆ C := by
  simp_rw [← subcomplex.union, ← union_openCell]
  exact iUnion_mono fun n ↦ iUnion_subset fun i ↦ by apply subset_iUnion_of_subset ↑i; rfl

lemma union_closedCell (E : Set X) [subcomplex : Subcomplex C E] :
    ⋃ (n : ℕ) (j : subcomplex.I n), closedCell (C := C) n j = E := by
  apply subset_antisymm
  · apply iUnion_subset fun n ↦ iUnion_subset fun i ↦ ?_
    simp_rw [← closure_openCell_eq_closedCell, subcomplex.closed.closure_subset_iff,
      ← subcomplex.union]
    exact subset_iUnion_of_subset n (subset_iUnion (fun (i : ↑(I E n)) ↦ openCell (C := C) n ↑i) i)
  · simp_rw [← subcomplex.union]
    apply iUnion_mono fun n ↦ iUnion_mono fun (i : ↑(I E n)) ↦ ?_
    exact openCell_subset_closedCell (C := C) n i

-- I should probably revise this name and think of some smart notation
def Complex (E : Set X) (C : Set X) [CWComplex C] [Subcomplex C E] : Set X := E

-- Is this good notation? Is this used somewhere else?
scoped infixr:35 " ⇂ "  => Complex

/- See "Topologie" p. 120 by Klaus Jänich from 2001 -/
instance CWComplex_subcomplex (E : Set X) [subcomplex : Subcomplex C E] : CWComplex (E ⇂ C) where
  cell n := subcomplex.I n
  map n i := map (C := C) n i
  source_eq n i := source_eq (C := C) n i
  cont n i := cont (C := C) n i
  cont_symm n i := cont_symm (C := C) n i
  pairwiseDisjoint' := by
    simp only [PairwiseDisjoint, Set.Pairwise, mem_univ, ne_eq, Function.onFun,
      disjoint_iff_inter_eq_empty, true_implies, Sigma.forall, Subtype.forall,
      not_and]
    intro n j _ m i _ eq
    apply disjoint_openCell_of_ne
    aesop
  mapsto := by
    intro n i
    rcases cellFrontier_subset' (C := C) n i with ⟨J, hJ⟩
    let J' m := Finset.preimage (J m) (fun (x : subcomplex.I m) ↦ ↑x) (by simp [InjOn])
    use J'
    rw [mapsTo']
    intro x xmem
    simp only [iUnion_coe_set, mem_iUnion, exists_prop, exists_and_right]
    have := hJ xmem
    simp only [mem_iUnion, exists_prop] at this ⊢
    obtain ⟨m, mltn, j, jmem, xmemopen⟩ := this
    use m, mltn, j
    refine ⟨?_, openCell_subset_closedCell _ _ xmemopen⟩
    suffices j ∈ subcomplex.I m by
      use this
      simp only [Finset.mem_preimage, jmem, J']
    have : x ∈ E := by
      rw [← subcomplex.union_closedCell]
      refine mem_of_subset_of_mem ?_ xmem
      refine subset_iUnion_of_subset n (subset_iUnion_of_subset ↑i ?_)
      exact cellFrontier_subset_closedCell (C := C) n ↑i
    simp only [← subcomplex.union, mem_iUnion, exists_prop] at this
    obtain ⟨l, o, xmemopen'⟩ := this
    suffices (⟨m, j⟩ : Σ n, cell C n) = ⟨l, ↑o⟩ by aesop
    apply eq_cell_of_not_disjoint
    rw [Set.not_disjoint_iff]
    use x
  closed' A := by
    intro Asub
    refine ⟨fun closedA _ _ ↦ closedA.inter isClosed_closedCell, ?_⟩
    intro closed
    apply strong_induction_isClosed (subset_trans Asub subcomplex.subset_complex)
    intro n _ j
    by_cases h : j ∈ subcomplex.I n
    · exact Or.intro_right _ (closed n ⟨j, h⟩)
    left
    suffices A ∩ openCell n j = ∅ by
      rw [this]
      exact isClosed_empty
    rw [← subset_empty_iff]
    apply subset_trans (inter_subset_inter_left _ Asub)
    simp_rw [Complex, ← subcomplex.union, subset_empty_iff, iUnion_inter]
    apply iUnion_eq_empty.2 fun m ↦ iUnion_eq_empty.2 fun i ↦ ?_
    apply disjoint_openCell_of_ne
    aesop
  union' := subcomplex.union_closedCell

--this is quite ugly, probably because `Subcomplex` shouldn't be a lemma
instance subcomplex_iUnion_subcomplex (J : Type*) (sub : J → Set X)
    [cw : ∀ (j : J), Subcomplex C (sub j)] : Subcomplex C (⋃ (j : J), sub j) := Subcomplex' C _
  (fun (n : ℕ) ↦ ⋃ (j : J), (cw j).I n)
  (by
    intro n ⟨i, imem⟩
    rw [mem_iUnion] at imem
    obtain ⟨j, imemj⟩ := imem
    apply subset_iUnion_of_subset j
    rw [← (cw j).union_closedCell]
    exact subset_iUnion_of_subset n
      (subset_iUnion (fun (j : ↑(I (sub j) n)) ↦ closedCell (C := C) n ↑j) ⟨i, imemj⟩)
    )
  (by
    simp_rw [← (cw _).union]
    rw [iUnion_comm]
    apply iUnion_congr fun n ↦ ?_
    simp_rw [iUnion_subtype, mem_iUnion, iUnion_exists,
      iUnion_comm (fun x ↦ fun i ↦ ⋃ (_ : x ∈ I (sub i) n), openCell n x)]
    )

def finite_subcomplex_finite_iUnion_finite_subcomplex {J : Type*} [_root_.Finite J]
    {sub : J → Set X} [cw : ∀ (j : J), Subcomplex C (sub j)]
    (finite : ∀ (j : J), Finite (sub j ⇂ C)) : Finite (⋃ j, sub j ⇂ C) where
  finitelevels := by
    have h j := (finite j).finitelevels
    simp only [Filter.eventually_iff, subcomplex_iUnion_subcomplex, CWComplex_subcomplex,
      Subcomplex', iUnion_eq_empty, isEmpty_coe_sort, setOf_forall, Filter.iInter_mem] at h ⊢
    exact h
  finitecellFrontiers := by
    have h j := (finite j).finitecellFrontiers
    intro n
    simp only [subcomplex_iUnion_subcomplex, Subcomplex'', CWComplex_subcomplex] at h ⊢
    apply Finite.Set.finite_iUnion

instance cellzero (i : cell C 0) : Subcomplex C (closedCell 0 i) where
  I n := {x | HEq (⟨n, x⟩ : Σ n, cell C n) (⟨0, i⟩ : Σ n, cell C n)}
  closed := by
    simp only [closedCell_zero_eq_singleton]
    exact isClosed_singleton
  union := by
    apply subset_antisymm
    · apply iUnion_subset
      intro n
      apply iUnion_subset
      intro ⟨j, eq⟩
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

instance finite_cellzero (i : cell C 0) : Finite ((closedCell 0 i) ⇂ C) where
  finitelevels := by
    simp only [Filter.eventually_atTop, ge_iff_le]
    use 1
    intro b leb
    simp only [cellzero, CWComplex_subcomplex, coe_setOf, mem_setOf_eq, heq_eq_eq, Sigma.mk.inj_iff,
      isEmpty_subtype, not_and]
    intro j eq
    subst eq
    contradiction
  finitecellFrontiers := by
    intro n
    simp only [cellzero, CWComplex_subcomplex]
    by_cases h : n = 0
    · subst n
      simp only [heq_eq_eq, Sigma.mk.inj_iff, true_and, setOf_eq_eq_singleton]
      apply Finite.of_fintype
    · rw [finite_coe_iff]
      convert finite_empty
      apply eq_empty_of_forall_not_mem
      intro x xmem
      apply h
      simp only [heq_eq_eq, Sigma.mk.inj_iff, mem_setOf_eq] at xmem
      exact xmem.1

def attach_cell (n : ℕ) (i : cell C n) (E : Set X) [sub : Subcomplex C E]
    (subset : ∃ (I : Π m, Finset (sub.I m)), cellFrontier n i ⊆
    (⋃ (m < n) (j ∈ I m), closedCell (C := C) m j)) :
    Subcomplex C (E ∪ openCell n i) where
  I l := {j : cell C l | j ∈ sub.I l ∨ (⟨l, j⟩ : Σ n, cell C n) = ⟨n, i⟩}
  closed := by
    suffices cellFrontier n i ⊆ E by
      rw [← union_eq_left.2 this, union_assoc, cellFrontier_union_openCell_eq_closedCell]
      exact sub.closed.union isClosed_closedCell
    obtain ⟨I, hI⟩ := subset
    apply hI.trans
    simp_rw [← sub.union_closedCell]
    apply iUnion_mono fun m ↦ iUnion_subset fun _ ↦ iUnion_subset fun i ↦ iUnion_subset fun _ ↦ ?_
    exact subset_iUnion_of_subset i (by rfl)
  union := by
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

instance finite_attach_cell (n : ℕ) (i : cell C n) (E : Set X) [sub : Subcomplex C E]
    [Finite (E ⇂ C)] (subset : ∃ (I : Π m, Finset (sub.I m)), cellFrontier n i ⊆
    (⋃ (m < n) (j ∈ I m), closedCell (C := C) m j)) :
    let subcomplex := attach_cell n i E subset
    Finite (E ∪ openCell n i ⇂ C) where
  finitelevels := by sorry
  finitecellFrontiers := by sorry

-- All of this isn't really even needed for what I'm trying to do

lemma closedCell_subset_finite_subcomplex (n : ℕ) (i : cell C n) :
    ∃ (E : Set X) (_ : Subcomplex C E), Finite (E ⇂ C) ∧ closedCell n i ⊆ E := by
  induction' n using Nat.case_strong_induction_on with n hn
  · use (closedCell 0 i), (Subcomplex.cellzero _)
    exact ⟨finite_cellzero i, by rfl⟩
  obtain ⟨I, hI⟩ := cellFrontier_subset n.succ i
  choose sub cw hsub using hn
  have : _root_.Finite (Σ (m : {m : ℕ // m ≤ n}), I m) := by

    sorry
  use ⋃ (x : Σ (m : {m : ℕ // m ≤ n}), I m), sub x.1.1 x.1.2 ↑x.2.1, inferInstance
  --use ⋃ (x : {x : Σ n, cell C n // x.1 ≤ n ∧ x.2 ∈ I x.1}), sub x.1.1 x.2.1 x.1.2, inferInstance
  refine ⟨finite_subcomplex_finite_iUnion_finite_subcomplex (fun ⟨⟨m, mlen⟩, j⟩ ↦ (hsub m mlen j).1),
    ?_⟩


  sorry

lemma finite_iUnion_subset_Subcomplex_of_cell_subset_Subcomplex (I : (n : ℕ) → Set (cell C n))
    [_root_.Finite (Σ n, I n)] (cellsubset : ∀ n (i : I n), ∃ (E : Set X) (_ : Subcomplex C E),
    CWComplex.Finite (E ⇂ C) ∧ map (C := C) n i '' closedBall 0 1 ⊆ E) :
    ∃ (E : Set X) (sub : Subcomplex C E), CWComplex.Finite (E ⇂ C) ∧
    (⋃ (n : ℕ) (i : I n), map (C := C) n i '' closedBall 0 1) ⊆ E := by
  choose S hS using cellsubset
  choose SC hSC using hS
  sorry
  /-use (⋃ (ni : Σ n, I n), S ni.1 ni.2), (Subcomplex.subcomplex_iUnion_subcomplex _ _ _)
  constructor
  · apply Subcomplex.finite_subcomplex_finite_iUnion_finite_subcomplex
    intro ⟨n, i⟩
    exact (hSC n i).1
  · apply iUnion_subset
    intro n
    apply iUnion_subset
    intro i
    apply subset_iUnion_of_subset ⟨n, i⟩
    exact (hSC n i).2
  -/

lemma finite_iUnion_subset_Subcomplex (I : (n : ℕ) → Set (cell C n))
    [finite : _root_.Finite (Σ n, I n)] :
    ∃ (E : Set X) (sub : Subcomplex C E), CWComplex.Finite (E ⇂ C) ∧
    (⋃ (n : ℕ) (i : I n), map (C := C) n i '' closedBall 0 1) ⊆ E := by
  apply finite_iUnion_subset_Subcomplex_of_cell_subset_Subcomplex
  intro n i
  induction' n using Nat.case_strong_induction_on with n hn
  · use (map (C := C) 0 i '' closedBall 0 1), (Subcomplex.cellzero _)
    exact ⟨finite_cellzero (i : cell C 0), by rfl⟩

  sorry

end Subcomplex

end
