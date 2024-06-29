import CWcomplexes.Lemmas
import CWcomplexes.kification
import Mathlib.Data.Finset.NatAntidiagonal


set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open Metric Set Kification

namespace CWComplex


section

variable {X : Type*} {Y : Type*} [t1 : TopologicalSpace X] [t2 : TopologicalSpace Y] [T2Space X] [T2Space Y] {C : Set X} {D : Set Y} (hC : @CWComplex X t1 C) (hD : @CWComplex Y t2 D)

def Prodkification X Y := kification (X × Y)

infixr:35 " ×ₖ "  => Prodkification

instance instprodkification : TopologicalSpace (X ×ₖ Y) := instkification

lemma prod_map_image_ball {m l : ℕ} {j : hC.cell m} {k : hD.cell l} : (fun a => ((IsometryEquivFinMap m l).symm.transPartialEquiv ((hC.map m j).prod (hD.map l k))) a) '' ball 0 1
    = (↑(hC.map m j) '' ball 0 1) ×ˢ (↑(hD.map l k) '' ball 0 1) := by
  rw [prod_image_image_eq, ← PartialEquiv.prod_coe, ← IsometryEquivFinMapR_image_ball, image_image]
  simp only [Equiv.transPartialEquiv_apply, IsometryEquiv.coe_toEquiv, PartialEquiv.prod_coe]

lemma prod_map_image_closedball {m l : ℕ} {j : hC.cell m} {k : hD.cell l} : (fun a => ((IsometryEquivFinMap m l).symm.transPartialEquiv ((hC.map m j).prod (hD.map l k))) a) '' closedBall 0 1
    = (↑(hC.map m j) '' closedBall 0 1) ×ˢ (↑(hD.map l k) '' closedBall 0 1) := by
  rw [prod_image_image_eq, ← PartialEquiv.prod_coe, ← IsometryEquivFinMapR_image_closedball, image_image]
  simp only [Equiv.transPartialEquiv_apply, IsometryEquiv.coe_toEquiv, PartialEquiv.prod_coe]

lemma prod_map_image_sphere {m l : ℕ} {j : hC.cell m} {k : hD.cell l} : (fun a => ((IsometryEquivFinMap m l).symm.transPartialEquiv ((hC.map m j).prod (hD.map l k))) a) '' sphere 0 1
    = (hC.map m j '' (Metric.sphere 0 1 : Set (Fin m → ℝ))) ×ˢ (hD.map l k '' (Metric.closedBall 0 1 : Set (Fin l → ℝ))) ∪ (hC.map m j '' (Metric.closedBall 0 1 : Set (Fin m → ℝ))) ×ˢ (hD.map l k '' (Metric.sphere 0 1 : Set (Fin l → ℝ))) := by
  simp_rw [prod_image_image_eq, ← PartialEquiv.prod_coe, ← image_union, ← IsometryEquivFinMapR_image_sphere, image_image]
  simp only [Equiv.transPartialEquiv_apply, IsometryEquiv.coe_toEquiv, PartialEquiv.prod_coe]

-- See Hatcher p. 533
instance CWComplex_product : @CWComplex (X ×ₖ Y) instprodkification (C ×ˢ D) where
  cell n := (Σ' (m : ℕ) (l : ℕ) (hml : m + l = n), hC.cell m × hD.cell l)
  map n i := match i with
    | ⟨m, l, hmln, j, k⟩ =>
      hmln ▸ Equiv.transPartialEquiv ((IsometryEquivFinMap m l).symm).toEquiv (PartialEquiv.prod (hC.map m j) (hD.map l k))
  source_eq n i := by
    rcases i with  ⟨m, l, hmln, j, k⟩
    subst hmln
    ext x
    simp only [Equiv.transPartialEquiv_source, IsometryEquiv.coe_toEquiv, PartialEquiv.prod_source,
      hC.source_eq m j, hD.source_eq, mem_preimage, mem_closedBall, dist_zero_right, prod_closedBall_eq_closedBall 0 0, ← Prod.zero_eq_mk]
    rw [Isometry.norm_map_of_map_zero (IsometryEquiv.isometry (IsometryEquiv.symm (IsometryEquivFinMap m l)))]
    rw [IsometryEquiv.symm_apply_eq]
    exact (IsometryEquivFinMapR_zero_eq_zero _ _).symm
  cont n i := by
    rcases i with  ⟨m, l, hmln, j, k⟩
    subst hmln
    simp only [Equiv.transPartialEquiv_eq_trans, PartialEquiv.coe_trans]
    apply @ContinuousOn.comp _ _ _ _ _ instprodkification ↑((hC.map m j).prod (hD.map l k)) _ _ ((closedBall 0 1 : Set (Fin m → ℝ)) ×ˢ (closedBall 0 1 : Set (Fin l → ℝ))) _
    · apply Continuous.continuousOn
      rw [Equiv.toPartialEquiv_apply, IsometryEquiv.coe_toEquiv]
      apply IsometryEquiv.continuous
    · rw [Set.mapsTo', Equiv.toPartialEquiv_apply, IsometryEquiv.coe_toEquiv,
        IsometryEquiv.image_closedBall,IsometryEquivFinMap_symmR_zero_eq_zero, closedBall_prod_same, Prod.zero_eq_mk]
    · apply continuousOn_compact_to_kification (IsCompact.prod (isCompact_closedBall 0 1) (isCompact_closedBall 0 1))
      exact ContinuousOn.prod_map (hC.cont m j) (hD.cont l k)
  cont_symm n i:= by
    rcases i with ⟨m, l, hmln, j, k⟩
    subst hmln
    simp only [Equiv.transPartialEquiv_eq_trans, PartialEquiv.coe_trans_symm, Equiv.toPartialEquiv_symm_apply,
      PartialEquiv.trans_target, PartialEquiv.prod_target, Equiv.toPartialEquiv_target,
      preimage_univ, inter_univ]
    apply Continuous.comp_continuousOn
    · suffices Continuous ⇑(@IsometryEquivFinMap ℝ _ m l) by convert this
      apply IsometryEquiv.continuous
    · rw [PartialEquiv.prod_symm]
      exact from_kification_continuouson_of_continuouson (↑((hC.map m j).symm.prod (hD.map l k).symm)) ((hC.map m j).target ×ˢ (hD.map l k).target) (ContinuousOn.prod_map (hC.cont_symm m j) (hD.cont_symm l k))
  pairwiseDisjoint := by
    intro ⟨n1, m, l, hmln1, j, k⟩ _ ⟨n2, p, q, hpqn2, i, o⟩ _ ne
    subst hmln1 hpqn2
    unfold Function.onFun
    simp only
    rw [prod_map_image_ball, prod_map_image_ball, Set.disjoint_prod]
    have disjoint1 := hC.pairwiseDisjoint
    have disjoint2 := hD.pairwiseDisjoint
    rw [PairwiseDisjoint, Set.Pairwise] at disjoint1 disjoint2
    have : (⟨m, j⟩ : (n : ℕ) × hC.cell n) ≠ ⟨p, i⟩ ∨ (⟨l, k⟩ : (n : ℕ) × hD.cell n) ≠ ⟨q, o⟩ := by
      by_contra h
      push_neg at h
      apply ne
      rcases h with ⟨h1, h2⟩
      simp only [Sigma.mk.inj_iff] at h1 h2
      rcases h1 with ⟨h11, h12⟩
      rcases h2 with ⟨h21, h22⟩
      subst m l
      simp only [heq_eq_eq] at h12 h22
      subst j k
      rfl
    rcases this with h1 | h2
    · left
      exact disjoint1 (Set.mem_univ _) (Set.mem_univ _) h1
    · right
      exact disjoint2 (Set.mem_univ _) (Set.mem_univ _) h2
  mapsto n i := by
    classical
    rcases i with ⟨m, l, hmln, j, k⟩
    subst hmln
    rcases hC.mapsto m j with ⟨J1, hJ1⟩
    rcases hD.mapsto l k with ⟨J2, hJ2⟩
    let J n : Finset (Σ' (k m : ℕ) (h : k + m = n), hC.cell k × hD.cell m) :=
      ((Finset.antidiagonal n).attach.biUnion fun ⟨(o, p), h⟩ ↦ if h' : p = l then (J1 o ×ˢ {k}).image fun (x, y) ↦ ⟨o, l, by rw [← h']; simpa using h, x, y⟩ else ∅)
      ∪ ((Finset.antidiagonal n).attach.biUnion fun ⟨(o, p), h⟩ ↦ if h' : o = m then ({j} ×ˢ J2 p).image fun (x, y) ↦ ⟨m, p, by rw [← h']; simpa using h, x, y⟩ else ∅)
    use J
    rw [Set.mapsTo'] at hJ1 hJ2 ⊢
    intro ⟨x1, x2⟩ xmem
    rw [prod_map_image_sphere] at xmem
    rcases xmem with xmem1 | xmem2
    · rcases xmem1 with ⟨x1mem, x2mem⟩
      simp only [mem_iUnion, PSigma.exists, Prod.exists]
      replace hJ1 := hJ1 x1mem
      simp only [mem_iUnion, exists_prop] at hJ1
      rcases hJ1 with ⟨o, oltm, p, pmemo, hop⟩
      use o + l, Nat.add_lt_add_right oltm l, o, l, rfl, p, k
      have : ⟨o, ⟨l, ⟨rfl, (p, k)⟩⟩⟩ ∈ J (o + l) := by
        simp only [Finset.singleton_product, Finset.mem_union, Finset.mem_biUnion,
          Finset.mem_attach, true_and, Subtype.exists, Finset.mem_antidiagonal, Prod.exists, J]
        left
        use o, l, rfl
        simp only [↓reduceDite, Prod.mk.eta, Finset.product_singleton, Finset.mem_image,
          Finset.mem_map, Function.Embedding.coeFn_mk, PSigma.mk.injEq, heq_eq_eq, true_and,
          exists_eq_right, Prod.mk.injEq, and_true, pmemo]
      use this
      rw [prod_map_image_closedball]
      exact ⟨hop, x2mem⟩
    · rcases xmem2 with ⟨x1mem, x2mem⟩
      simp only [mem_iUnion, PSigma.exists, Prod.exists]
      replace hJ2 := hJ2 x2mem
      simp only [mem_iUnion, exists_prop] at hJ2
      rcases hJ2 with ⟨o, oltl, p, pmemo, hop⟩
      use m + o, Nat.add_lt_add_left oltl m, m, o, rfl, j, p
      have : ⟨m, ⟨o, ⟨rfl, (j, p)⟩⟩⟩ ∈ J (m + o) := by
        simp only [Finset.singleton_product, Finset.mem_union, Finset.mem_biUnion,
          Finset.mem_attach, true_and, Subtype.exists, Finset.mem_antidiagonal, Prod.exists, J]
        right
        use m, o, rfl
        simp only [↓reduceDite, Prod.mk.eta, Finset.product_singleton, Finset.mem_image,
          Finset.mem_map, Function.Embedding.coeFn_mk, PSigma.mk.injEq, heq_eq_eq, true_and,
          exists_eq_right, Prod.mk.injEq, and_true, pmemo]
      use this
      rw [prod_map_image_closedball]
      exact ⟨x1mem, hop⟩
  closed A := by
    intro Asub
    constructor
    · intro closedA n ⟨m, l, hmln, j, k⟩
      subst hmln
      apply IsClosed.inter closedA
      rw [prod_map_image_closedball]
      refine IsClosed.mono ?_ kification_le
      exact IsClosed.prod (hC.isClosed_map_closedBall _ _) (hD.isClosed_map_closedBall _ _)
    · intro hA
      rw [@kification.closed_iff _ instTopologicalSpaceProd]
      intro K
      let K' := ((Prod.fst '' K.1) ∩ C) ×ˢ ((Prod.snd '' K.1) ∩ D)
      have KsubK' : K.1 ∩ (C ×ˢ D) ⊆ K' := by
        simp only [TopologicalSpace.Compacts.carrier_eq_coe, prod_inter, inter_prod,
          subset_inter_iff, inter_subset_right, and_true, K']
        constructor
        constructor
        · apply subset_trans Set.inter_subset_left
          intro x xmem
          simp only [TopologicalSpace.Compacts.carrier_eq_coe, mem_prod, mem_image, SetLike.mem_coe,
            Prod.exists, exists_and_right, exists_eq_right]
          exact ⟨⟨x.2, xmem⟩, ⟨x.1, xmem⟩⟩
        · intro x ⟨xmem1, xmem2⟩
          simp only [mem_prod, mem_image, SetLike.mem_coe, Prod.exists, exists_eq_right] at xmem2 ⊢
          exact ⟨xmem2.1, ⟨x.1, xmem1⟩⟩
        · intro x ⟨xmem1, xmem2⟩
          simp only [mem_prod, mem_image, SetLike.mem_coe, Prod.exists, exists_and_right,
            exists_eq_right] at xmem2 ⊢
          exact ⟨⟨x.2, xmem1⟩, xmem2.2⟩
      suffices ∃ (C_1 : TopologicalSpace.Closeds (X × Y)), A ∩ K' = C_1.carrier ∩ K' by
        rcases this with ⟨B, hB⟩
        use ⟨B.1 ∩ (C ×ˢ D), IsClosed.inter B.2 (IsClosed.prod hC.isClosed hD.isClosed)⟩
        simp only
        rw [inter_assoc, inter_comm (C ×ˢ D), ← inter_eq_right.2 KsubK', ← inter_assoc, hB.symm,
          inter_assoc, inter_eq_right.2 KsubK', inter_comm K.carrier (C ×ˢ D), ← inter_assoc, inter_eq_left.2 Asub]
      let U1 := ⋃ (x : Σ (m : ℕ), {j : hC.cell m // ¬ Disjoint (Prod.fst '' K.1) (hC.map m j '' ball 0 1)}), hC.map x.1 x.2 '' closedBall 0 1
      let U2 := ⋃ (x : Σ (m : ℕ), {j : hD.cell m // ¬ Disjoint (Prod.snd '' K.1) (hD.map m j '' ball 0 1)}), hD.map x.1 x.2 '' closedBall 0 1
      have sub1 : Prod.fst '' K.1 ∩ C ⊆ U1 := by
        intro x ⟨xmem1, xmem2⟩
        simp only [U1, mem_iUnion]
        simp only [← hC.union', mem_iUnion] at xmem2
        rcases xmem2 with ⟨m, j, hmj⟩
        use ⟨m, j, not_disjoint_iff.2 ⟨x, xmem1, hmj⟩⟩
        exact hC.map_ball_subset_map_closedball hmj
      have sub2 : Prod.snd '' K.1 ∩ D ⊆ U2 := by
        intro x ⟨xmem1, xmem2⟩
        simp only [U2, mem_iUnion]
        simp only [← hD.union', mem_iUnion] at xmem2
        rcases xmem2 with ⟨m, j, hmj⟩
        use ⟨m, j, not_disjoint_iff.2 ⟨x, xmem1, hmj⟩⟩
        exact hD.map_ball_subset_map_closedball hmj
      have sub : K' ⊆ U1 ×ˢ U2 := by
        simp only [K', prod_subset_prod_iff]
        left
        exact ⟨sub1, sub2⟩
      suffices ∃ (C_1 : TopologicalSpace.Closeds (X × Y)), A ∩ (U1 ×ˢ U2) = C_1.carrier ∩ (U1 ×ˢ U2) by
        rcases this with ⟨B, hB⟩
        use B
        rw [← inter_eq_right.2 sub, ← inter_assoc, ← inter_assoc, hB]
      simp only [TopologicalSpace.Compacts.carrier_eq_coe, prod_iUnion, iUnion_prod_const, U1, U2]
      apply @closed_in_finite _ _ _ (hD.compact_inter_finite ⟨Prod.snd '' K.1, IsCompact.image K.2 continuous_snd⟩) _
      · intro i1
        apply @isClosed_iUnion_of_finite _ _ _ (hC.compact_inter_finite ⟨Prod.fst '' K.1, IsCompact.image K.2 continuous_fst⟩) _
        intro i2
        apply IsClosed.prod (hC.isClosed_map_closedBall i2.1 i2.2.1) (hD.isClosed_map_closedBall i1.1 i1.2.1)
      intro ⟨m, j, _⟩
      apply @closed_in_finite _ _ _ (hC.compact_inter_finite ⟨Prod.fst '' K.1, IsCompact.image K.2 continuous_fst⟩) _
      · intro i2
        apply IsClosed.prod (hC.isClosed_map_closedBall i2.1 i2.2.1) (hD.isClosed_map_closedBall m j)
      intro ⟨n, i, _⟩
      replace hA := hA (n + m) ⟨n, m, rfl, i, j⟩
      rw [prod_map_image_closedball] at hA
      simp only [Equiv.transPartialEquiv_apply, IsometryEquiv.coe_toEquiv, PartialEquiv.prod_coe,
       TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Compacts.coe_mk] at hA ⊢
      rw [@kification.closed_iff _ instTopologicalSpaceProd _] at hA
      rcases hA ⟨(hC.map n i '' closedBall 0 1) ×ˢ (hD.map m j '' closedBall 0 1), IsCompact.prod (hC.isCompact_map_closedBall n i) (hD.isCompact_map_closedBall m j)⟩ with ⟨C1, hC1⟩
      use C1
      rw [← hC1, inter_assoc, inter_self]
  union := by
    have : ⋃ (n : ℕ), ⋃ (j : (m : ℕ) ×' (l : ℕ) ×' (_ : m + l = n) ×' hC.cell m × hD.cell l), (fun a ↦  (j.2.2.fst ▸ (IsometryEquivFinMap j.fst j.2.fst).symm.transPartialEquiv
        ((hC.map j.fst j.2.2.2.1).prod (hD.map j.2.fst j.2.2.2.2))) a) '' closedBall 0 1 =
        ⋃ (n : ℕ), ⋃ (j : (m : ℕ) ×' (l : ℕ) ×' (_ : m + l = n) ×' hC.cell m × hD.cell l), (hC.map j.fst j.2.2.2.1 '' closedBall 0 1) ×ˢ (hD.map j.2.fst j.2.2.2.2 '' closedBall 0 1) := by
      apply Set.iUnion_congr
      intro n
      apply Set.iUnion_congr
      intro ⟨m, l, hmln, j, k⟩
      subst hmln
      simp only [prod_map_image_closedball]
    simp_rw [this, ← hC.union, ← hD.union, Set.prod_iUnion, Set.iUnion_prod_const]
    ext x
    simp only [mem_iUnion, mem_prod, PSigma.exists, Prod.exists, exists_and_right, exists_and_left]
    exact ⟨fun ⟨n, m, l, hnml, j, k, x1mem, x2mem⟩ ↦ ⟨⟨m, ⟨j, x1mem⟩⟩, ⟨l, ⟨k, x2mem⟩⟩⟩,
      fun ⟨⟨m, j, x1mem⟩, ⟨l, k, x2mem⟩⟩ ↦ ⟨m + l, ⟨m, ⟨l, ⟨rfl, ⟨j, ⟨k, ⟨x1mem, x2mem⟩⟩⟩⟩⟩⟩⟩⟩

infixr:35 " × " => CWComplex_product


end
