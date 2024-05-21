import CWcomplexes.Constructions

open Metric Set

variable {X : Type*} [t : TopologicalSpace X] [T2Space X] {C : Set X} (hC : CWComplex C)


namespace CWComplex


lemma isClosed_level (n : ℕ∞) : IsClosed (hC.level n) := (hC.CWComplex_level n).isClosed

/- The following is one way of stating that `level 0` is discrete. -/
lemma isDiscrete_level_zero {A : Set X} : IsClosed (A ∩ hC.level 0) := by
  rw [hC.closed (A ∩ hC.level 0) (subset_trans (Set.inter_subset_right A (hC.level 0)) (by simp_rw [← hC.level_top]; apply hC.level_subset_level_of_le le_top))]
  intro n
  induction' n using Nat.case_strong_induction_on with n hn
  · intro j
    have := Set.inter_eq_right.2 (hC.map_closedBall_subset_level 0 j)
    norm_cast at this
    rw [inter_assoc, this]
    have : ↑(hC.map 0 j) '' closedBall 0 1 = {(hC.map 0 j) ![]} := by
      ext x
      constructor
      · intro h
        rw [mem_image] at h
        rcases h with ⟨y, _, mapy⟩
        have : y = ![] := by simp [Matrix.empty_eq]
        rw [this] at mapy
        simp only [mapy, mem_singleton_iff]
      · intro h
        rw [h]
        apply Set.mem_image_of_mem
        simp only [Matrix.zero_empty, mem_closedBall, dist_self, zero_le_one]
    rw [this]
    by_cases h : {(hC.map 0 j) ![]} ⊆ A
    · rw [inter_eq_right.2 h]
      exact isClosed_singleton
    · simp at h
      have : A ∩ {(hC.map 0 j) ![]} = ∅ := by
        simp only [inter_singleton_eq_empty, h, not_false_eq_true]
      rw [this]
      exact isClosed_empty
  · rw [← Nat.add_one]
    intro j
    rw [inter_assoc, hC.level_inter_image_closedBall_eq_level_inter_image_sphere (by norm_cast; exact Nat.zero_lt_succ n), ← inter_assoc]
    exact hC.isClosed_inter_sphere_succ_of_le_isClosed_inter_closedBall hn j

/- I also need the indexed sum of types here. Use subcomplex.-/
lemma iUnion_subcomplex (J : Type u) (I : J → Π n, Set (hC.cell n)) (cw : ∀ (l : J), CWComplex (⋃ (n : ℕ) (j : I l n), hC.map n j '' ball 0 1)) : CWComplex (⋃ (l : J) (n : ℕ) (j : I l n), hC.map n j '' ball 0 1) := by
  sorry


/- A finite union of finite subcomplexes is again a finite subcomplex.-/
/-
lemma finite_iUnion_finitesubcomplex (m : ℕ) (mnezero : m > 0) (I : Fin m → Π n, Set (hC.cell n)) (fincw : ∀ (l : Fin m), FiniteCWComplex (⋃ (n : ℕ) (j : I l n), hC.map n j '' ball 0 1)) : FiniteCWComplex (⋃ (l : Fin m) (n : ℕ) (j : I l n), hC.map n j '' ball 0 1) where
  cwcomplex := by
    apply hC.iUnion_subcomplex
    exact (fun l ↦ (fincw l).cwcomplex)
  finitelevels := by
    let max' l := Classical.choose (fincw l).finitelevels
    let max := Finset.max' (Finset.image (fun l ↦ max' l) (@Finset.univ _ (Fin.fintype m))) (by apply Finset.Nonempty.image (@Finset.univ_nonempty _ _ ((Fin.pos_iff_nonempty).1 mnezero)))
    use max
    ext x
    constructor
    · intro xmem
      rw [mem_iUnion] at xmem
      rcases xmem with ⟨l, xmem⟩
      simp only [level, levelaux, mem_iUnion, exists_prop]
      use max' l
      constructor
      · norm_cast
        rw [Nat.add_one]
        apply Nat.lt_succ_of_le
        simp [max]
        apply Finset.le_max'
        simp
      · have := Classical.choose_spec (fincw l).finitelevels
        sorry --maybe I need to make the construction of iUnion_subcomplex explicit to progress with this...
    · sorry
  finitecells := sorry
-/

/- See Hatcher p. 522. I don't really want to do that know so I'll just leave it here for now.-/
def open_neighbourhood_aux (ε : (n : ℕ) → (hC.cell n) → {x : ℝ // x > 0}) (A : Set X) (AsubC : A ⊆ C) (n : ℕ): Set X :=
  match n with
  | 0 => A ∩ hC.level 0
  | Nat.succ m => sorry
