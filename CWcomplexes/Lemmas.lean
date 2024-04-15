import CWcomplexes.Constructions

open Metric Set

namespace CWComplex

variable {X : Type*} [t : TopologicalSpace X] [T2Space X] {C : Set X} (hC : CWComplex C)

/- The levels are closed. The following might be helpful:
https://math.stackexchange.com/questions/4051497/subcomplex-is-closed -/
lemma isClosed_level (n : ℕ∞) : IsClosed (hC.level n) := (hC.CWComplex_level n).isClosed
-- this proof seems eerily short so I'm keeping the beginning of my earlier proof for now:
/-
  by_cases h : n = ⊤
  · rw [h]
    rw [level_top]
    exact hC.isClosed
  push_neg at h
  let m := ENat.toNat n
  have coemn: ↑m = n := ENat.coe_toNat h
  rw [← coemn]
  induction' m with m hm
  · rw [← Set.inter_self (level hC ↑Nat.zero)]
    exact hC.isDiscrete_level_zero
  · rw [← Nat.add_one, ENat.coe_add, ENat.coe_one, hC.level_succ_eq_level_union_iUnion m]
    sorry
    /- Next step of the proof: Define disjoint map (how?) show that it is a quotient map (QuotientMap). Then our set is closed since the preimage is also closed by induction -/
-/

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
