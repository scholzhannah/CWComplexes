import CWcomplexes.Lemmas
import CWcomplexes.kification
import Mathlib.Data.Finset.NatAntidiagonal


set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open Metric Set KSpace

namespace CWComplex

-- this needs a masssive refactor
-- separating out definitions, and lemmas ...

section

variable {X : Type*} {Y : Type*} [t1 : TopologicalSpace X] [t2 : TopologicalSpace Y] [T2Space X]
  [T2Space Y] {C : Set X} {D : Set Y} [CWComplex C] [CWComplex D]

def Prodkification X Y := kification (X × Y)

infixr:35 " ×ₖ "  => Prodkification

instance instprodkification : TopologicalSpace (X ×ₖ Y) := instkification

def prodcell (C : Set X) (D : Set Y) [CWComplex C] [CWComplex D] (n : ℕ) :=
  (Σ' (m : ℕ) (l : ℕ) (hml : m + l = n), cell C m × cell D l)

example (n m l : ℕ) (hmnl : m + l = n) : Fin n ≃ Fin (m + l) := finCongr hmnl.symm

def prodisometryequiv {n m l : ℕ}  (hmln : m + l = n) (j : cell C m) (k : cell D l) :=
  (IsometryEquiv.arrowCongrleft ℝ (finCongr hmln.symm)).trans
  ((IsometryEquivFinMap m l).symm)

def prodmap {n m l : ℕ} (hmln : m + l = n) (j : cell C m) (k : cell D l) :=
  (prodisometryequiv hmln j k).transPartialEquiv
  (PartialEquiv.prod (map m j) (map l k))

lemma prodisometryequiv_zero {n m l : ℕ} {hmln : m + l = n} {j : cell C m} {k : cell D l} :
    (prodisometryequiv hmln j k) 0 = 0 :=
  rfl

lemma prodisometryequiv_image_closedBall {n m l : ℕ} {hmln : m + l = n} {j : cell C m}
    {k : cell D l} :
    ⇑(prodisometryequiv hmln j k) '' closedBall 0 1 =  closedBall 0 1 ×ˢ closedBall 0 1 := by
  ext _
  simp only [IsometryEquiv.image_closedBall, prodisometryequiv_zero, mem_closedBall,
    dist_zero_right, closedBall_prod_same, ← Prod.zero_eq_mk]

lemma prodisometryequiv_image_ball {n m l : ℕ} {hmln : m + l = n} {j : cell C m}
    {k : cell D l} :
    ⇑(prodisometryequiv hmln j k) '' ball 0 1 =  ball 0 1 ×ˢ ball 0 1 := by
  ext _
  simp only [IsometryEquiv.image_ball, prodisometryequiv_zero, mem_ball, dist_zero_right,
    ball_prod_same, ← Prod.zero_eq_mk]

lemma prodisometryequiv_image_sphere {n m l : ℕ} {hmln : m + l = n} {j : cell C m} {k : cell D l} :
    prodisometryequiv hmln j k '' sphere 0 1 =
    sphere 0 1 ×ˢ closedBall 0 1 ∪ closedBall 0 1 ×ˢ sphere 0 1 := by
  rw [prodisometryequiv, IsometryEquiv.trans_image]
  have : ⇑(IsometryEquiv.arrowCongrleft ℝ (finCongr hmln.symm)) '' sphere 0 1 = sphere 0 1 := by
    ext x
    simp only [IsometryEquiv.image_sphere, mem_sphere_iff_norm, sub_zero]
    have : (IsometryEquiv.arrowCongrleft ℝ (finCongr hmln.symm)) 0 = 0 := by rfl
    rw [this, sub_zero]
  rw [this, IsometryEquivFinMapR_image_sphere]

lemma prodmap_image_ball {n m l : ℕ} {hmln : m + l = n} {j : cell C m} {k : cell D l} :
    prodmap hmln j k ''
    ball 0 1 = (openCell m j) ×ˢ (openCell l k) := by
  rw [prodmap, Equiv.transPartialEquiv_image, IsometryEquiv.coe_toEquiv,
    prodisometryequiv_image_ball, PartialEquiv.prod_coe, ← prod_image_image_eq]
  rfl

lemma prodmap_image_sphere {n m l : ℕ} {hmln : m + l = n} {j : cell C m} {k : cell D l} :
    prodmap hmln j k '' sphere 0 1 = (cellFrontier m j) ×ˢ (closedCell l k) ∪
    (closedCell m j) ×ˢ (cellFrontier l k) := by
  simp_rw [prodmap, Equiv.transPartialEquiv_image, IsometryEquiv.coe_toEquiv,
    prodisometryequiv_image_sphere, image_union, PartialEquiv.prod_coe, ← prod_image_image_eq]
  rfl

lemma prodmap_image_closedBall {n m l : ℕ} {hmln : m + l = n} {j : cell C m} {k : cell D l} :
    prodmap hmln j k ''
    closedBall 0 1 = (closedCell m j) ×ˢ (closedCell l k) := by
  rw [prodmap, Equiv.transPartialEquiv_image, IsometryEquiv.coe_toEquiv,
    prodisometryequiv_image_closedBall, PartialEquiv.prod_coe, ← prod_image_image_eq]
  rfl

open Classical in
def frontierset (m l: ℕ) (j : cell C m) (k : cell D l)
    (J1 :(m : ℕ) → Finset (cell C m))
    (hJ1 : cellFrontier m j ⊆ ⋃ m_1, ⋃ (_ : m_1 < m), ⋃ j_1 ∈ J1 m_1, closedCell m_1 j_1)
    (J2 :(m : ℕ) → Finset (cell D m))
    (hJ2 : cellFrontier l k ⊆ ⋃ m_1, ⋃ (_ : m_1 < l), ⋃ j_1 ∈ J2 m_1, closedCell m_1 j_1)
    (n : ℕ):
    Finset (Σ' (k m : ℕ) (h : k + m = n), cell C k × cell D m) :=
  ((Finset.antidiagonal n).attach.biUnion fun ⟨(o, p), h⟩ ↦ if h' : p = l then
  (J1 o ×ˢ {k}).image fun (x, y) ↦ ⟨o, l, by rw [← h']; simpa using h, x, y⟩ else ∅)
  ∪ ((Finset.antidiagonal n).attach.biUnion fun ⟨(o, p), h⟩ ↦ if h' : o = m then
  ({j} ×ˢ J2 p).image fun (x, y) ↦ ⟨m, p, by rw [← h']; simpa using h, x, y⟩ else ∅)

-- this is worse than the actual proof...
-- this is just horrible
lemma frontierset_eq (m l: ℕ) (j : cell C m) (k : cell D l)
    (J1 :(m : ℕ) → Finset (cell C m))
    (hJ1 : cellFrontier m j ⊆ ⋃ m_1, ⋃ (_ : m_1 < m), ⋃ j_1 ∈ J1 m_1, closedCell m_1 j_1)
    (J2 :(m : ℕ) → Finset (cell D m))
    (hJ2 : cellFrontier l k ⊆ ⋃ m_1, ⋃ (_ : m_1 < l), ⋃ j_1 ∈ J2 m_1, closedCell m_1 j_1)
    (n : ℕ):
    (frontierset m l j k J1 hJ1 J2 hJ2 n).toSet =
    (⋃ (o : ℕ) (holn : o + l = n) (x : J1 o), {⟨o, l, holn, x, k⟩})
    ∪ ⋃ (p : ℕ) (hmpn : m + p = n) (y : J2 p), {⟨m, p, hmpn, j, y⟩} := by
  ext a
  simp only [frontierset, Prod.mk.eta, Finset.product_singleton, Finset.singleton_product,
    Finset.coe_union, Finset.coe_biUnion, Finset.mem_coe, Finset.mem_attach, iUnion_true, mem_union,
    mem_iUnion, Subtype.exists, Finset.mem_antidiagonal, Prod.exists, iUnion_singleton_eq_range,
    mem_range, exists_prop]
  apply Iff.or
  · constructor
    · intro ⟨o, p, hopn, amem⟩
      have : p = l := by
        by_contra h
        simp only [h, ↓reduceDIte, Finset.not_mem_empty] at amem
      subst p
      simp only [↓reduceDIte, Finset.mem_image, Finset.mem_map, Function.Embedding.coeFn_mk,
        exists_exists_and_eq_and] at amem
      use o, hopn
    · intro ⟨o, holn, amem⟩
      use o, l, holn
      simp only [↓reduceDIte, Finset.mem_image, Finset.mem_map, Function.Embedding.coeFn_mk,
        exists_exists_and_eq_and, amem]
  · constructor
    · intro ⟨o, p, hopn, amem⟩
      have : o = m := by
        by_contra h
        simp only [h, ↓reduceDIte, Finset.not_mem_empty] at amem
      subst o
      simp only [↓reduceDIte, Finset.mem_image, Finset.mem_map, Function.Embedding.coeFn_mk,
        exists_exists_and_eq_and] at amem
      use p, hopn
    · intro ⟨p, hmpn, amem⟩
      use m, p, hmpn
      simp only [↓reduceDIte, Finset.mem_image, Finset.mem_map, Function.Embedding.coeFn_mk,
        exists_exists_and_eq_and, amem]


-- See Hatcher p. 533
instance CWComplex_product : CWComplex (X := X ×ₖ Y) (C ×ˢ D) where
  cell n := prodcell C D n
  map n i := match i with
    | ⟨m, l, hmln, j, k⟩ => prodmap hmln j k
  source_eq n i := by
    rcases i with  ⟨m, l, hmln, j, k⟩
    ext x
    simp only [prodmap, Equiv.transPartialEquiv_source, IsometryEquiv.coe_toEquiv,
      PartialEquiv.prod_source, source_eq m j, source_eq, closedBall_prod_same, ← Prod.zero_eq_mk,
      mem_preimage, mem_closedBall, dist_zero_right]
    rw [Isometry.norm_map_of_map_zero (by exact (prodisometryequiv hmln j k).isometry_toFun)]
    rfl
  cont n i := by
    rcases i with  ⟨m, l, hmln, j, k⟩
    simp only [Equiv.transPartialEquiv_eq_trans, PartialEquiv.coe_trans, prodmap]
    apply ContinuousOn.image_comp_continuous
    · rw [Equiv.toPartialEquiv_apply, IsometryEquiv.coe_toEquiv]
      exact (prodisometryequiv hmln j k).continuous
    · rw [Equiv.toPartialEquiv_apply, IsometryEquiv.coe_toEquiv, prodisometryequiv_image_closedBall]
      simp only [PartialEquiv.prod_coe]
      apply continuousOn_compact_to_kification
        (by rw [closedBall_prod_same]; exact isCompact_closedBall _ _)
      exact ContinuousOn.prod_map (CWComplex.cont _ _) (CWComplex.cont _ _)
  cont_symm n i := by
    rcases i with ⟨m, l, hmln, j, k⟩
    simp only [Equiv.transPartialEquiv_eq_trans, PartialEquiv.coe_trans_symm,
      Equiv.toPartialEquiv_symm_apply, PartialEquiv.trans_target, PartialEquiv.prod_target,
      Equiv.toPartialEquiv_target, preimage_univ, inter_univ, prodmap]
    apply (prodisometryequiv hmln j k).symm.continuous.comp_continuousOn
    rw [PartialEquiv.prod_symm]
    exact from_kification_continuouson_of_continuouson ((map m j).symm.prod (map l k).symm)
      ((map m j).target ×ˢ (map l k).target) ((cont_symm m j).prod_map (cont_symm l k))
  pairwiseDisjoint' := by
    intro ⟨n1, m, l, hmln1, j, k⟩ _ ⟨n2, p, q, hpqn2, i, o⟩ _ ne
    simp only [Function.onFun, disjoint_iff_inter_eq_empty]
    rw [prodmap_image_ball, prodmap_image_ball, prod_inter_prod, prod_eq_empty_iff]
    suffices (⟨m, j⟩ : Σ n, cell C n) ≠ ⟨p, i⟩ ∨  (⟨l, k⟩ : Σ n, cell D n) ≠ ⟨q, o⟩ by
      rcases this with ne1 | ne2
      · exact Or.intro_left _ (disjoint_openCell_of_ne ne1)
      · exact Or.intro_right _ (disjoint_openCell_of_ne ne2)
    by_contra h
    push_neg at h
    apply ne
    aesop
  mapsto n i := by
    classical
    rcases i with ⟨m, l, hmln, j, k⟩
    --subst hmln
    obtain ⟨J1, hJ1⟩ := cellFrontier_subset m j
    obtain ⟨J2, hJ2⟩ := cellFrontier_subset l k
    use frontierset m l j k J1 hJ1 J2 hJ2
    rw [mapsTo']
    intro ⟨x1, x2⟩ xmem
    rw [prodmap_image_sphere] at xmem
    rcases xmem with xmem1 | xmem2
    · obtain ⟨x1mem, x2mem⟩ := xmem1
      replace hJ1 := hJ1 x1mem
      simp only [mem_iUnion, PSigma.exists, Prod.exists] at hJ1 ⊢
      obtain ⟨o, oltm, p, pmemo, hop⟩ := hJ1
      use o + l, (by rw [← hmln]; exact Nat.add_lt_add_right oltm l), ⟨o, l, rfl, p, k⟩
      suffices ⟨o, ⟨l, ⟨rfl, (p, k)⟩⟩⟩ ∈ frontierset m l j k J1 hJ1 J2 hJ2 (o + l) by
        use this
        rw [prodmap_image_closedBall]
        exact ⟨hop, x2mem⟩
      simp only [frontierset, Finset.singleton_product, Finset.mem_union, Finset.mem_biUnion,
          Finset.mem_attach, true_and, Subtype.exists, Finset.mem_antidiagonal, Prod.exists]
      left
      use o, l, rfl
      simp only [↓reduceDIte, Prod.mk.eta, Finset.product_singleton, Finset.mem_image,
        Finset.mem_map, Function.Embedding.coeFn_mk, PSigma.mk.injEq, heq_eq_eq, true_and,
        exists_eq_right, Prod.mk.injEq, and_true, pmemo]
    · obtain ⟨x1mem, x2mem⟩ := xmem2
      replace hJ2 := hJ2 x2mem
      simp only [mem_iUnion, PSigma.exists, Prod.exists] at hJ2 ⊢
      rcases hJ2 with ⟨o, oltl, p, pmemo, hop⟩
      use m + o, (by rw [← hmln]; exact Nat.add_lt_add_left oltl m), ⟨m, o, rfl, j, p⟩
      suffices ⟨m, ⟨o, ⟨rfl, (j, p)⟩⟩⟩ ∈ frontierset m l j k J1 hJ1 J2 hJ2 (m + o) by
        use this
        rw [prodmap_image_closedBall]
        exact ⟨x1mem, hop⟩
      simp only [frontierset, Finset.singleton_product, Finset.mem_union, Finset.mem_biUnion,
        Finset.mem_attach, true_and, Subtype.exists, Finset.mem_antidiagonal, Prod.exists]
      right
      use m, o, rfl
      simp only [↓reduceDIte, Prod.mk.eta, Finset.product_singleton, Finset.mem_image,
        Finset.mem_map, Function.Embedding.coeFn_mk, PSigma.mk.injEq, heq_eq_eq, true_and,
        exists_eq_right, Prod.mk.injEq, and_true, pmemo]
  closed' A Asub := by
    constructor
    · intro closedA n ⟨m, l, hmln, j, k⟩
      apply closedA.inter
      rw [prodmap_image_closedBall]
      refine IsClosed.mono ?_ kification_le
      exact isClosed_closedCell.prod isClosed_closedCell
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
        use ⟨B.1 ∩ (C ×ˢ D), IsClosed.inter B.2 (isClosed.prod isClosed)⟩
        simp only
        rw [inter_assoc, inter_comm (C ×ˢ D), ← inter_eq_right.2 KsubK', ← inter_assoc, hB.symm,
          inter_assoc, inter_eq_right.2 KsubK', inter_comm K.carrier (C ×ˢ D),
          ← inter_assoc, inter_eq_left.2 Asub]
      let U1 := ⋃ (x : Σ (m : ℕ), {j : cell C m // ¬ Disjoint (Prod.fst '' K.1)
        (map m j '' ball 0 1)}), map (C := C) x.1 x.2 '' closedBall 0 1
      let U2 := ⋃ (x : Σ (m : ℕ), {j : cell D m // ¬ Disjoint (Prod.snd '' K.1)
        (map m j '' ball 0 1)}), map (C := D) x.1 x.2 '' closedBall 0 1
      have sub : K' ⊆ U1 ×ˢ U2 := by
        simp only [K', prod_subset_prod_iff]
        left
        exact ⟨subset_not_disjoint _, subset_not_disjoint _⟩
      suffices ∃ (C_1 : TopologicalSpace.Closeds (X × Y)), A ∩ (U1 ×ˢ U2) =
          C_1.carrier ∩ (U1 ×ˢ U2) by
        rcases this with ⟨B, hB⟩
        use B
        rw [← inter_eq_right.2 sub, ← inter_assoc, ← inter_assoc, hB]
      simp only [TopologicalSpace.Compacts.carrier_eq_coe, prod_iUnion, iUnion_prod_const, U1, U2]
      apply @closed_in_finite _ _ _
        (compact_inter_finite (Prod.snd '' K.1) (K.2.image continuous_snd))
      · intro i1
        apply @isClosed_iUnion_of_finite _ _ _
          (compact_inter_finite (Prod.fst '' K.1) (K.2.image continuous_fst)) _
        intro i2
        apply isClosed_closedCell.prod isClosed_closedCell
      intro ⟨m, j, _⟩
      apply @closed_in_finite _ _ _
        (compact_inter_finite (Prod.fst '' K.1) (K.2.image continuous_fst)) _
      · intro i2
        apply isClosed_closedCell.prod isClosed_closedCell
      intro ⟨n, i, _⟩
      replace hA := hA (n + m) ⟨n, m, rfl, i, j⟩
      rw [prodmap_image_closedBall] at hA
      simp only [Equiv.transPartialEquiv_apply, IsometryEquiv.coe_toEquiv, PartialEquiv.prod_coe,
       TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Compacts.coe_mk] at hA ⊢
      rw [@kification.closed_iff _ instTopologicalSpaceProd _] at hA
      rcases hA ⟨(map n i '' closedBall 0 1) ×ˢ (map m j '' closedBall 0 1),
        (isCompact_closedCell.prod isCompact_closedCell)⟩ with ⟨C1, hC1⟩
      use C1
      simp only [← hC1, closedCell, inter_assoc, inter_self]
  union' := by
    simp_rw [← union (C := C), ← union (C := D), ← iUnion_prod, iUnion_prod', prodcell]
    -- sorry
    /-have : ⋃ (n : ℕ), ⋃ (j : (m : ℕ) ×' (l : ℕ) ×' (_ : m + l = n) ×' cell C m × cell D l),
        (fun a ↦  (j.2.2.fst ▸ (IsometryEquivFinMap j.fst j.2.fst).symm.transPartialEquiv
        ((map j.fst j.2.2.2.1).prod (map j.2.fst j.2.2.2.2))) a) '' closedBall 0 1 =
        ⋃ (n : ℕ), ⋃ (j : (m : ℕ) ×' (l : ℕ) ×' (_ : m + l = n) ×' cell C m × cell D l),
        (map j.fst j.2.2.2.1 '' closedBall 0 1) ×ˢ (map j.2.fst j.2.2.2.2 '' closedBall 0 1) := by
      apply Set.iUnion_congr
      intro n
      apply Set.iUnion_congr
      intro ⟨m, l, hmln, j, k⟩
      subst hmln
      simp only [prodmap_image_closedBall]

    simp_rw [this, ← union (C := C), ← union, Set.prod_iUnion, Set.iUnion_prod_const]
    ext x
    simp only [mem_iUnion, mem_prod, PSigma.exists, Prod.exists, exists_and_right, exists_and_left]
    exact ⟨fun ⟨n, m, l, hnml, j, k, x1mem, x2mem⟩ ↦ ⟨⟨m, ⟨j, x1mem⟩⟩, ⟨l, ⟨k, x2mem⟩⟩⟩,
      fun ⟨⟨m, j, x1mem⟩, ⟨l, k, x2mem⟩⟩ ↦ ⟨m + l, ⟨m, ⟨l, ⟨rfl, ⟨j, ⟨k, ⟨x1mem, x2mem⟩⟩⟩⟩⟩⟩⟩⟩
    -/
    sorry

infixr:35 " × " => CWComplex_product

end
