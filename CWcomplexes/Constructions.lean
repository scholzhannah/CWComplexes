import CWcomplexes.Definition
import Mathlib.Analysis.NormedSpace.Real

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open Metric Set

namespace CWComplex

variable {X : Type*} [t : TopologicalSpace X] [T2Space X] {C : Set X} (hC : CWComplex C)

section

def CWComplex_level (n : ℕ∞) : CWComplex (hC.level n) where
  cell l := {x : hC.cell l // l < n + 1}
  map l i := hC.map l i
  source_eq l i := by rw [hC.source_eq]
  cont l i := hC.cont l i
  cont_symm l i := hC.cont_symm l i
  pairwiseDisjoint := by
    rw [PairwiseDisjoint, Set.Pairwise]
    simp only [mem_univ, ne_eq, forall_true_left, Sigma.forall, Subtype.forall]
    intro a ja alt b jb blt
    have := hC.pairwiseDisjoint
    rw [PairwiseDisjoint, Set.Pairwise] at this
    simp only [mem_univ, ne_eq, forall_true_left, Sigma.forall, Subtype.forall] at this
    have := this a ja b jb
    intro h
    simp only [Sigma.mk.inj_iff, not_and] at *
    apply this
    by_cases h' : a = b
    · simp [h']
      by_contra h''
      apply h h'
      rw [Subtype.heq_iff_coe_heq (type_eq_of_heq h'')]
      simp [h'']
      rw [h']
    · simp only [h', IsEmpty.forall_iff]
  mapsto l i := by
    rcases hC.mapsto l i with ⟨I, hI⟩
    rcases i with ⟨i, llt⟩
    let J := fun (m : ℕ) ↦ (I m).subtype (fun j ↦ m < n + 1)
    use J
    simp only [mapsTo'] at *
    apply subset_trans hI
    apply Set.iUnion_mono''
    intro i x xmem
    simp only [mem_iUnion, exists_prop] at *
    constructor
    · exact xmem.1
    rcases xmem with ⟨iltl, ⟨j, ⟨jmemIi, xmem⟩⟩⟩
    have : (i : ℕ∞) < (l : ℕ∞) := by norm_cast
    use ⟨j, lt_trans this llt⟩
    exact ⟨(by simp only [Finset.mem_subtype, jmemIi, J]) , xmem⟩
  closed A := by
    intro asublevel
    have : A ⊆ C := by
      apply subset_trans
      exact asublevel
      simp_rw [← hC.level_top]
      apply hC.level_subset_level_of_le le_top
    have := hC.closed A this
    constructor
    · intro closedA l j
      simp [this.1]
    · intro h
      simp at h
      rw [this]
      intro m
      induction' m using Nat.case_strong_induction_on with m hm
      · have : 0 < n + 1 := by simp only [add_pos_iff, zero_lt_one, or_true]
        intro j
        exact h Nat.zero j this
      rw [← Nat.add_one] at *
      intro j
      let k := ENat.toNat n
      by_cases mlt : m + 1 < n + 1
      · exact h (m + 1) j mlt
      push_neg at mlt
      have nltm : n ≤ Nat.succ m := le_trans (le_add_right le_rfl) mlt
      have coekn: ↑k = n := ENat.coe_toNat (ne_top_of_le_ne_top (WithTop.natCast_ne_top (Nat.succ m)) nltm)
      rw [← coekn] at asublevel  mlt
      norm_cast at *
      have : A ∩ ↑(hC.map (m + 1) j) '' closedBall 0 1 = A ∩ ↑(hC.map (m + 1) j) '' sphere 0 1 := by
        calc
          A ∩ ↑(hC.map (m + 1) j) '' closedBall 0 1 = A ∩ (hC.level k ∩ ↑(hC.map (m + 1) j) '' closedBall 0 1) := by rw [← inter_assoc, Set.inter_eq_left.2 asublevel]
          _ = A ∩ (hC.level k ∩ ↑(hC.map (m + 1) j) '' sphere 0 1) := by
            have : (m + 1 : ℕ∞) > (k : ℕ∞) := by norm_cast
            have : hC.level k ∩ ↑(hC.map (m + 1) j) '' closedBall 0 1 = hC.level k ∩ ↑(hC.map (m + 1) j) '' sphere 0 1 := by
              apply hC.level_inter_image_closedBall_eq_level_inter_image_sphere this
            rw [this]
          _ = A ∩ ↑(hC.map (m + 1) j) '' sphere 0 1 := by rw [← inter_assoc, Set.inter_eq_left.2 asublevel]
      rw [this]
      exact hC.isClosed_inter_sphere_succ_of_le_isClosed_inter_closedBall hm j
  union := by
    rw [CWComplex.level]
    apply Set.iUnion_congr
    intro m
    ext x
    constructor
    · intro h
      rw [mem_iUnion] at *
      rcases h with ⟨⟨i, mlt⟩, hi⟩
      use mlt
      rw [mem_iUnion]
      use i
    · intro h
      rw [mem_iUnion, exists_prop] at *
      rw [mem_iUnion] at h
      rcases h with ⟨mlt, ⟨i, hi⟩⟩
      use ⟨i, mlt⟩


variable {D : Set X} (hD : CWComplex D)

def CWComplex_disjointUnion (disjoint : Disjoint C D) : CWComplex (C ∪ D) where
  cell n := Sum (hC.cell n) (hD.cell n)
  map n i :=
    match i with
    | Sum.inl x => hC.map n x
    | Sum.inr x => hD.map n x
  source_eq n i := by
    rcases i with i | i
    · exact hC.source_eq n i
    · exact hD.source_eq n i
  cont n i := by
    rcases i with i | i
    · exact hC.cont n i
    · exact hD.cont n i
  cont_symm n i := by
    rcases i with i | i
    · exact hC.cont_symm n i
    · exact hD.cont_symm n i
  pairwiseDisjoint := by
    rw [PairwiseDisjoint, Set.Pairwise]
    simp only [mem_univ, ne_eq, forall_true_left]
    intro ⟨n, cn⟩ ⟨m, cm⟩ ne
    rcases cn with cn | cn
    rcases cm with cm | cm
    · have := hC.pairwiseDisjoint
      simp only [PairwiseDisjoint, Set.Pairwise, mem_univ, ne_eq, forall_true_left] at this
      have ne' : ¬({ fst := n, snd := cn } : (n : ℕ) × hC.cell n) = { fst := m, snd := cm } := by
        by_contra eq
        apply ne
        simp only [Sigma.mk.inj_iff] at *
        rcases eq with ⟨neqm, cnheqcm⟩
        constructor
        · exact neqm
        · subst neqm
          have := eq_of_heq cnheqcm
          subst this
          rfl
      exact @this ⟨n, cn⟩ ⟨m, cm⟩ ne'
    · simp [Function.onFun]
      exact Disjoint.mono (hC.map_ball_subset_complex n cn) (hD.map_ball_subset_complex m cm) disjoint
    rcases cm with cm | cm
    · simp [Function.onFun]
      rw [disjoint_comm] at disjoint
      exact Disjoint.mono (hD.map_ball_subset_complex n cn) (hC.map_ball_subset_complex m cm) disjoint
    · have := hD.pairwiseDisjoint
      simp only [PairwiseDisjoint, Set.Pairwise, mem_univ, ne_eq, forall_true_left] at this
      have ne' : ¬({ fst := n, snd := cn } : (n : ℕ) × hD.cell n) = { fst := m, snd := cm } := by
        by_contra eq
        apply ne
        simp only [Sigma.mk.inj_iff] at *
        rcases eq with ⟨neqm, cnheqcm⟩
        constructor
        · exact neqm
        · subst neqm
          have := eq_of_heq cnheqcm
          subst this
          rfl
      exact @this ⟨n, cn⟩ ⟨m, cm⟩ ne'
  mapsto n i := by
    rcases i with ic | id
    · rcases hC.mapsto n ic with ⟨I, hI⟩
      classical
      let J : (m : ℕ) → Finset (hC.cell m ⊕ hD.cell m) := fun (m : ℕ) ↦ Finset.image (fun j ↦ .inl j) (I m)
      use J
      rw [mapsTo'] at *
      simp only [J]
      intro x xmem
      apply hI at xmem
      simp only [mem_iUnion, exists_prop] at *
      rcases xmem with ⟨i, ⟨iltn, ⟨j, ⟨jmem, xmem⟩⟩⟩⟩
      use i
      simp only [iltn, exists_exists_and_eq_and, true_and]
      use .inl j
      simp only [Finset.mem_image, Sum.inl.injEq, exists_eq_right, jmem, true_and, xmem]
    · rcases hD.mapsto n id with ⟨I, hI⟩
      classical
      let J : (m : ℕ) → Finset (hC.cell m ⊕ hD.cell m) := fun (m : ℕ) ↦ Finset.image (fun j ↦ .inr j) (I m)
      use J
      rw [mapsTo'] at *
      simp only [J]
      intro x xmem
      apply hI at xmem
      simp only [mem_iUnion, exists_prop] at *
      rcases xmem with ⟨i, ⟨iltn, ⟨j, ⟨jmem, xmem⟩⟩⟩⟩
      use i
      simp only [iltn, exists_exists_and_eq_and, true_and]
      use .inr j
      simp only [Finset.mem_image, Sum.inr.injEq, exists_eq_right, jmem, true_and, xmem]
  closed A := by
    intro asubcd
    constructor
    · intro closedA n j
      apply IsClosed.inter closedA
      rcases j with j | j
      · exact hC.isClosed_map_closedBall n j
      · exact hD.isClosed_map_closedBall n j
    · intro h
      have : A = (A ∩ C) ∪ (A ∩ D) := by
        calc
        A = A ∩ (C ∪ A) := (inter_eq_left.2 subset_union_right).symm
        _ = (A ∪ A ∩ D) ∩ (C ∪ A ∩ D) := by
          have h1 : A ∪ A ∩ D = A := union_eq_left.2 Set.inter_subset_left
          have h2 : C ∪ A ∩ D = C ∪ A := by
            rw [union_inter_distrib_left, inter_eq_left]
            apply Set.union_subset subset_union_left asubcd
          rw [h1, h2]
        _ = (A ∩ C) ∪ (A ∩ D) := by rw [inter_union_distrib_right]
      rw [this]
      apply IsClosed.union
      · rw [hC.closed (A ∩ C) inter_subset_right]
        intro n j
        have := h n (Sum.inl j)
        simp at this
        rw [inter_right_comm]
        apply IsClosed.inter this hC.isClosed
      · rw [hD.closed (A ∩ D) inter_subset_right]
        intro n j
        have := h n (Sum.inr j)
        simp at this
        rw [inter_right_comm]
        apply IsClosed.inter this hD.isClosed
  union := by
    simp_rw [← hC.union, ← hD.union, ← Set.iUnion_union_distrib]
    apply Set.iUnion_congr
    intro n
    ext x
    constructor
    · intro h
      rw [mem_iUnion] at h
      rcases h with ⟨i, hi⟩
      rcases i with i | i
      · simp only at hi
        left
        rw [mem_iUnion]
        use i
      · simp only at hi
        right
        rw [mem_iUnion]
        use i
    · intro h
      rcases h with h | h
      · rw [mem_iUnion] at *
        rcases h with ⟨i, hi⟩
        use Sum.inl i
      · rw [mem_iUnion] at *
        rcases h with ⟨i, hi⟩
        use Sum.inr i

-- does typeclass inference even work here?
/- See "Topologie" p. 120 by Klaus Jänich from 2001 -/
def CWComplex_subcomplex (E : Set X) (subcomplex: hC.Subcomplex E) : CWComplex E where
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
    simp_rw [← Metric.sphere_union_ball, image_union, iUnion_union_distrib, subcomplex.union, Set.union_eq_right]
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

end
