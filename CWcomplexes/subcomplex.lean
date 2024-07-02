import CWcomplexes.Lemmas
import Mathlib.Analysis.NormedSpace.Real

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open Metric Set

namespace CWComplex

variable {X : Type*} [t : TopologicalSpace X] [T2Space X] (C : Set X) [hC : CWComplex C]

section

class Subcomplex (E : Set X) where
  I : Π n, Set (hC.cell n)
  closed : IsClosed E
  union : E = ⋃ (n : ℕ) (j : I n), hC.map n j '' ball 0 1

-- should this be a def? I would like this to unfold nicer in proofs
/- See "Topologie" p. 120 by Klaus Jänich from 2001 -/
def Subcomplex' (E : Set X) (I : Π n, Set (hC.cell n))
    (cw : CWComplex E)
    (union : E = ⋃ (n : ℕ) (j : I n), hC.map n j '' ball 0 1): Subcomplex C E where
  I := I
  closed := cw.isClosed
  union := union

/- See "Topologie" p. 120 by Klaus Jänich from 2001 -/
def Subcomplex'' (E : Set X) (I : Π n, Set (hC.cell n))
    (mapsto : ∀ (n : ℕ) (i : I n), MapsTo (hC.map n i) (closedBall 0 1) E)
    (union : E = ⋃ (n : ℕ) (j : I n), hC.map n j '' ball 0 1): hC.Subcomplex E where
  I := I
  closed := by
    have EsubC : E ⊆ C := by
      simp_rw [union, ← hC.union']
      apply iUnion_mono
      intro n
      apply iUnion_subset
      intro i
      apply subset_iUnion_of_subset ↑i
      rfl
    rw [hC.closed E EsubC]
    intro n j
    have : E ∩ ↑(hC.map n j) '' closedBall 0 1 =
        (⋃ (x : {x : Σ (n : ℕ), I n // ¬ Disjoint (hC.map n j '' closedBall 0 1) (hC.map x.1 x.2 '' ball 0 1)}),
        hC.map x.1.1 x.1.2 '' ball 0 1) ∩ ↑(hC.map n j) '' closedBall 0 1 := by
      rw [union]
      apply subset_antisymm
      · simp_rw [iUnion_inter]
        apply iUnion_subset
        intro m
        apply iUnion_subset
        intro i
        by_cases h : Disjoint (hC.map n j '' closedBall 0 1) (hC.map m i '' ball 0 1)
        · rw [disjoint_iff_inter_eq_empty, inter_comm] at h
          rw [h]
          exact empty_subset _
        · apply subset_iUnion_of_subset ⟨⟨m, i⟩, h⟩
          rfl
      · apply inter_subset_inter_left
        apply iUnion_subset
        intro x
        apply subset_iUnion_of_subset x.1.1
        apply subset_iUnion_of_subset x.1.2
        rfl
    rw [this]
    have : (⋃ (x : {x : Σ (n : ℕ), I n // ¬ Disjoint (hC.map n j '' closedBall 0 1) (hC.map x.1 x.2 '' ball 0 1)}),
        hC.map x.1.1 x.1.2 '' ball 0 1) ∩ ↑(hC.map n j) '' closedBall 0 1 =
        (⋃ (x : {x : Σ (n : ℕ), I n // ¬ Disjoint (hC.map n j '' closedBall 0 1) (hC.map x.1 x.2 '' ball 0 1)}),
        hC.map x.1.1 x.1.2 '' closedBall 0 1) ∩ ↑(hC.map n j) '' closedBall 0 1 := by
      apply subset_antisymm
      · apply inter_subset_inter_left
        apply iUnion_mono
        intro _
        exact hC.map_ball_subset_map_closedball
      · rw [← this]
        apply inter_subset_inter_left
        apply iUnion_subset
        intro x
        replace mapsto:= mapsto x.1.1 x.1.2
        rw [mapsTo'] at mapsto
        exact mapsto
    rw [this]
    apply IsClosed.inter _ (hC.isClosed_map_closedBall n j)
    apply @isClosed_iUnion_of_finite _ _ _ (hC.compact_inter_finite_subset' ⟨(hC.map n j '' closedBall 0 1), by exact hC.isCompact_map_closedBall n j⟩)
    intro _
    exact hC.isClosed_map_closedBall _ _
  union := union

namespace Subcomplex

-- I should probably revise this name and think of some smart notation
def Complex (E : Set X) (C : Set X) [hC : CWComplex C] [hC.Subcomplex E] : Set X := E

-- Is this good notation? Is this used somewhere else?
infixr:35 " ⇂ "  => Complex

-- does typeclass inference even work here?
/- See "Topologie" p. 120 by Klaus Jänich from 2001 -/
instance CWComplex_subcomplex (E : Set X) [subcomplex : hC.Subcomplex E] : CWComplex (E ⇂ C) where
  cell n := subcomplex.I n
  map n i := hC.map n i
  source_eq n i := hC.source_eq n i
  cont n i := hC.cont n i
  cont_symm n i := hC.cont_symm n i
  pairwiseDisjoint := by
    have := hC.pairwiseDisjoint
    rw [PairwiseDisjoint, Set.Pairwise] at *
    intro ⟨n, ni⟩ nmem ⟨m, mi⟩ mmem nnem
    simp at mi ni
    have disjoint := @this ⟨n, ni.1⟩ (Set.mem_univ (⟨n, ni.1⟩ : (n : ℕ) × hC.cell n)) ⟨m, mi.1⟩ (Set.mem_univ (⟨m, mi.1⟩ : (n : ℕ) × hC.cell n))
    have : ({ fst := n, snd := ↑ni } : (n : ℕ) × hC.cell n) ≠ { fst := m, snd := ↑mi } := by
      simp only [ne_eq, Sigma.mk.inj_iff, not_and] at nnem ⊢
      intro men heq
      apply nnem men
      subst men
      simp at heq
      apply Subtype.coe_injective at heq
      simp [heq]
    exact disjoint this
  mapsto := by
    intro n i
    rcases hC.mapsto' n i with ⟨J, hJ⟩
    let J' m := Finset.preimage (J m) (fun (x : subcomplex.I m) ↦ ↑x) (by simp [InjOn])
    use J'
    rw [MapsTo] at *
    intro x xmem
    simp only [iUnion_coe_set, mem_iUnion, exists_prop, exists_and_right] at *
    rcases (hJ xmem) with ⟨m, mltn, j, jmem, mapxmem⟩
    use m
    simp only [mltn, true_and]
    use j
    constructor
    · have : j ∈ subcomplex.I m := by
        have : (hC.map n ↑i) x ∈ E := by
          have h1: closure (hC.map n i '' ball 0 1) ⊆ E := by
            simp_rw [IsClosed.closure_subset_iff subcomplex.closed, subcomplex.union]
            apply Set.subset_iUnion_of_subset n
            apply Set.subset_iUnion (fun (j : ↑(subcomplex.I n)) ↦ hC.map n ↑j '' ball 0 1) i
          have h2 : (hC.map n ↑i) x ∈ closure (hC.map n i '' ball 0 1) := by
            rw [hC.closure_map_ball_eq_map_closedball]
            apply Set.mem_image_of_mem
            exact Metric.sphere_subset_closedBall xmem
          exact h1 h2
        simp only [subcomplex.union, mem_iUnion, exists_prop] at this
        rcases this with ⟨l, o, mapxmem'⟩
        have : ¬ Disjoint (↑(hC.map m j) '' ball 0 1) (↑(hC.map l o) '' ball 0 1) := by
          rw [Set.not_disjoint_iff]
          use ((hC.map n i) x)
        have := hC.not_disjoint_equal this
        simp at this
        rcases this with ⟨meql, jeqo⟩
        subst meql
        simp at jeqo
        subst jeqo
        simp
      use this
      simp [J', jmem]
    · exact hC.map_ball_subset_map_closedball mapxmem
  closed A := by
    intro Asub
    constructor
    · intro closedA n j
      exact IsClosed.inter closedA (hC.isClosed_map_closedBall n j)
    · intro closed
      have : E ⊆ C := by
        simp_rw [subcomplex.union, ← hC.level_top, level, levelaux, top_add]
        intro x xmem
        simp only [mem_iUnion, exists_prop] at *
        rcases xmem with ⟨n, ⟨i, hni⟩⟩
        exact ⟨n, ⟨ENat.coe_lt_top , ⟨i, (image_mono Metric.ball_subset_closedBall) hni⟩⟩⟩
      rw [hC.closed A (subset_trans Asub this)]
      intro n j
      induction' n using Nat.case_strong_induction_on with n hn
      · simp only [Matrix.empty_eq, nonempty_closedBall, zero_le_one, Nonempty.image_const]
        exact isClosed_inter_singleton
      · by_cases h : j ∈ subcomplex.I (Nat.succ n)
        · exact closed (Nat.succ n) ⟨j, h⟩
        rw [← Metric.sphere_union_ball, image_union, inter_union_distrib_left]
        apply IsClosed.union
        · exact hC.isClosed_inter_sphere_succ_of_le_isClosed_inter_closedBall hn j
        · have h1 : (⋃ (n : ℕ) (j : subcomplex.I n), hC.map n j '' ball 0 1) ∩ ↑(hC.map (Nat.succ n) j) '' ball 0 1 = ∅ := by
            simp only [iUnion_coe_set, Nat.succ_eq_add_one, iUnion_inter, iUnion_eq_empty]
            intro m i imem
            have := hC.pairwiseDisjoint
            simp only [PairwiseDisjoint, Set.Pairwise, mem_univ, ne_eq, Function.onFun,
              forall_true_left, Sigma.forall, Sigma.mk.inj_iff, not_and] at this
            simp only [Set.disjoint_iff_inter_eq_empty] at this
            apply this
            intro meqsuccn heqij
            apply h
            subst meqsuccn
            simp only [heq_eq_eq] at heqij
            subst heqij
            exact imem
          have : A ∩ (⋃ (n : ℕ) (j : subcomplex.I n), hC.map n j '' ball 0 1) = A := by
            rw [inter_eq_left, ← subcomplex.union]
            exact Asub
          rw [← this, inter_assoc, h1, inter_empty]
          exact isClosed_empty
  union := by
    unfold Complex
    simp_rw [← Metric.sphere_union_ball, image_union, iUnion_union_distrib, subcomplex.union, union_eq_right]
    apply Set.iUnion_subset
    intro n
    apply Set.iUnion_subset
    intro i
    apply subset_trans (image_mono Metric.sphere_subset_closedBall)
    rw [← closure_ball 0 (by norm_num)]
    apply subset_trans (ContinuousOn.image_closure (by rw [closure_ball 0 (by norm_num)]; exact hC.cont n i))
    simp_rw [← subcomplex.union , IsClosed.closure_subset_iff subcomplex.closed]
    intro x xmem
    simp only [subcomplex.union, mem_iUnion]
    use n
    use i

--this is quite ugly, probably because `hC.Subcomplex` shouldn't be a lemma
instance subcomplex_iUnion_subcomplex (J : Type*) (sub : J → Set X) [cw : ∀ (j : J), hC.Subcomplex (sub j)] : hC.Subcomplex (⋃ (j : J), sub j) := hC.Subcomplex'' _
  (fun (n : ℕ) ↦ ⋃ (j : J), (cw j).I n)
  (by
    intro n i
    have imem := i.2
    rw [mem_iUnion] at imem
    rcases imem with ⟨j, imemj⟩
    have mapstoj := CWComplex.mapsto' ((sub j) ⇂ C) n
    simp only [CWComplex_subcomplex, Subcomplex] at mapstoj
    rcases mapstoj ⟨i, imemj⟩ with ⟨K, hK⟩
    rw [mapsTo'] at hK ⊢
    rw [← Metric.sphere_union_ball, image_union]
    apply union_subset
    · apply subset_iUnion_of_subset j
      apply subset_trans hK
      simp_rw [(cw j).union]
      apply iUnion_mono
      intro m
      apply iUnion_subset
      intro _
      apply iUnion_subset
      intro k
      apply iUnion_subset
      intro _
      apply subset_iUnion_of_subset k
      rfl
    · apply subset_iUnion_of_subset j
      rw [(cw j).union]
      apply subset_iUnion_of_subset n
      apply subset_iUnion_of_subset ⟨i, imemj⟩
      rfl
    )
  (by
    simp_rw [(cw _).union]
    rw [iUnion_comm]
    apply iUnion_congr
    intro n
    apply subset_antisymm
    · apply iUnion_subset
      intro j
      apply iUnion_subset
      intro i
      apply subset_iUnion_of_subset ⟨i, by rw [mem_iUnion]; use j; exact i.2⟩
      rfl
    · apply iUnion_subset
      intro ⟨i, imem⟩
      rw [mem_iUnion] at imem
      rcases imem with ⟨j, imem⟩
      apply subset_iUnion_of_subset j
      apply subset_iUnion_of_subset ⟨i, imem⟩
      rfl
    )

instance _finite_subcomplex__finite_iUnion_finite_subcomplex (J : Type*) [_root_.Finite J] (sub : J → Set X) [cw : ∀ (j : J), hC.Subcomplex (sub j)]
    (finite : ∀ (j : J), CWComplex.Finite ((sub j) ⇂ C)) : CWComplex.Finite ((⋃ j, sub j) ⇂ C) where
  finitelevels := by
    have h j := (finite j).finitelevels
    simp only [Filter.eventually_iff, subcomplex_iUnion_subcomplex, CWComplex_subcomplex, Subcomplex'',
      iUnion_eq_empty, isEmpty_coe_sort, setOf_forall, Filter.iInter_mem] at h ⊢
    exact h
  finitecells := by
    have h j := (finite j).finitecells
    intro n
    simp only [subcomplex_iUnion_subcomplex, Subcomplex'', CWComplex_subcomplex] at h ⊢
    apply Finite.Set.finite_iUnion

end Subcomplex

end
