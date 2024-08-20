import CWcomplexes.Lemmas
import CWcomplexes.kification
import Mathlib.Data.Finset.NatAntidiagonal

/-!
# The product of CW-complexes

In this file we proof the follwoing two statements:
* `CWComplex_product`: If `C` and `D` are CW-complexes in `C` and `D`, and `X × Y` is a k-space,
  then `C ×ˢ D` is a CW-complex.
* `CWComplex_product_kification`: If `C` and `D` are CW-complexes in `X` and `Y` then `C ×ˢ D` is
  a CW-complex in the k-ification of `X × Y`.

## References
[A. Hatcher, *Algebraic Topology*]
-/
noncomputable section

open Metric Set KSpace

namespace CWComplex


section

variable {X : Type*} {Y : Type*} [t1 : TopologicalSpace X] [t2 : TopologicalSpace Y]
  {C : Set X} {D : Set Y} [CWComplex C] [CWComplex D]

/-- The indexing types of cells of the product of two CW-complexes.-/
def prodcell (C : Set X) (D : Set Y) [CWComplex C] [CWComplex D] (n : ℕ) :=
  (Σ' (m : ℕ) (l : ℕ) (_ : m + l = n), cell C m × cell D l)

/-- The natural `IsometryEquiv` `(Fin n → ℝ) ≃ᵢ (Fin m → ℝ) × (Fin l → ℝ)` when `n = m + n`.-/
def prodisometryequiv {n m l : ℕ}  (hmln : m + l = n) :=
  (IsometryEquiv.arrowCongrLeftofFintype (X := ℝ) (finCongr hmln.symm)).trans
  ((IsometryEquiv.finArrowProdHomeomorphFinAddArrow m l).symm)

/-- The characterstic maps of the product of CW-complexes.-/
def prodmap {n m l : ℕ} (hmln : m + l = n) (j : cell C m) (k : cell D l) :=
  (prodisometryequiv hmln).transPartialEquiv
  (PartialEquiv.prod (map m j) (map l k))

lemma prodisometryequiv_image_closedBall {n m l : ℕ} {hmln : m + l = n} :
    prodisometryequiv hmln '' closedBall 0 1 = closedBall 0 1 ×ˢ closedBall 0 1 := by
  rw [IsometryEquiv.image_closedBall, closedBall_prod_same]
  rfl

lemma prodisometryequiv_image_ball {n m l : ℕ} {hmln : m + l = n} :
    ⇑(prodisometryequiv hmln) '' ball 0 1 =  ball 0 1 ×ˢ ball 0 1 := by
  simp only [IsometryEquiv.image_ball, ball_prod_same]
  rfl

lemma prodisometryequiv_image_sphere {n m l : ℕ} {hmln : m + l = n} :
    prodisometryequiv hmln '' sphere 0 1 =
    sphere 0 1 ×ˢ closedBall 0 1 ∪ closedBall 0 1 ×ˢ sphere 0 1 := by
  simp only [IsometryEquiv.image_sphere, sphere_prod]
  rfl

lemma prodmap_image_ball {n m l : ℕ} {hmln : m + l = n} {j : cell C m} {k : cell D l} :
    prodmap hmln j k '' ball 0 1 = (openCell m j) ×ˢ (openCell l k) := by
  simp_rw [prodmap, Equiv.transPartialEquiv_apply, ← image_image, IsometryEquiv.coe_toEquiv,
    prodisometryequiv_image_ball, PartialEquiv.prod_coe, ← prod_image_image_eq]
  rfl

lemma prodmap_image_sphere {n m l : ℕ} {hmln : m + l = n} {j : cell C m} {k : cell D l} :
    prodmap hmln j k '' sphere 0 1 = (cellFrontier m j) ×ˢ (closedCell l k) ∪
    (closedCell m j) ×ˢ (cellFrontier l k) := by
  simp_rw [prodmap, Equiv.transPartialEquiv_apply, ← image_image , IsometryEquiv.coe_toEquiv,
    prodisometryequiv_image_sphere, image_union, PartialEquiv.prod_coe, ← prod_image_image_eq]
  rfl

lemma prodmap_image_closedBall {n m l : ℕ} {hmln : m + l = n} {j : cell C m} {k : cell D l} :
    prodmap hmln j k ''
    closedBall 0 1 = (closedCell m j) ×ˢ (closedCell l k) := by
  simp_rw [prodmap, Equiv.transPartialEquiv_apply, ← image_image , IsometryEquiv.coe_toEquiv,
    prodisometryequiv_image_closedBall, PartialEquiv.prod_coe, ← prod_image_image_eq]
  rfl

variable [T2Space X] [T2Space Y]

/-- If `C` and `D` are CW-complexes in `C` and `D`, and `X × Y` is a k-space, then `C ×ˢ D` is a
  CW-complex.-/
instance CWComplex_product [KSpace (X × Y)] : CWComplex (C ×ˢ D) where
  cell n := prodcell C D n
  map n i := prodmap i.2.2.1 i.2.2.2.1 i.2.2.2.2
  source_eq n i := by
    rcases i with  ⟨m, l, hmln, j, k⟩
    ext x
    simp only [prodmap, Equiv.transPartialEquiv_source, IsometryEquiv.coe_toEquiv,
      PartialEquiv.prod_source, source_eq m j, source_eq, closedBall_prod_same, ← Prod.zero_eq_mk,
      mem_preimage, mem_closedBall, dist_zero_right]
    rw [Isometry.norm_map_of_map_zero (by exact (prodisometryequiv hmln).isometry_toFun)]
    rfl
  cont n i := by
    rcases i with  ⟨m, l, hmln, j, k⟩
    simp only [Equiv.transPartialEquiv_eq_trans, PartialEquiv.coe_trans, prodmap]
    apply ContinuousOn.image_comp_continuous
    · rw [Equiv.toPartialEquiv_apply, IsometryEquiv.coe_toEquiv]
      exact (prodisometryequiv hmln).continuous
    · rw [Equiv.toPartialEquiv_apply, IsometryEquiv.coe_toEquiv, prodisometryequiv_image_closedBall]
      simp only [PartialEquiv.prod_coe]
      exact ContinuousOn.prod_map (CWComplex.cont _ _) (CWComplex.cont _ _)
  cont_symm n i := by
    rcases i with ⟨m, l, hmln, j, k⟩
    simp only [Equiv.transPartialEquiv_eq_trans, PartialEquiv.coe_trans_symm,
      Equiv.toPartialEquiv_symm_apply, PartialEquiv.trans_target, PartialEquiv.prod_target,
      Equiv.toPartialEquiv_target, preimage_univ, inter_univ, prodmap]
    apply (prodisometryequiv hmln).symm.continuous.comp_continuousOn
    rw [PartialEquiv.prod_symm]
    exact ((cont_symm m j).prod_map (cont_symm l k))
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
    -- We first use `prodmap_image_sphere` to write the edge of the cell as a union.
    -- We then use `exists_iff_and_of_upwards_closed` to show that we can verify the
    -- statement seperately for the two parts of the union.
    -- We then do two completely symmetric proofs.
    classical
    rcases i with ⟨m, l, hmln, j, k⟩
    simp_rw [mapsTo', prodmap_image_sphere, union_subset_iff]
    rw [exists_iff_and_of_upwards_closed]
    swap
    · refine fun J sub K JleK ↦ sub.trans ?_
      repeat apply iUnion_mono fun _ ↦ ?_
      exact iUnion_subset_iUnion_const (fun a ↦ JleK _ a)
    swap
    · refine fun J sub K JleK ↦ sub.trans ?_
      repeat apply iUnion_mono fun _ ↦ ?_
      exact iUnion_subset_iUnion_const (fun a ↦ JleK _ a)
    constructor
    · obtain ⟨J1, hJ1⟩ := cellFrontier_subset_finite_closedCell m j
      use fun n ↦ ((Finset.antidiagonal n).attach.biUnion fun ⟨(o, p), h⟩ ↦ if h' : p = l then
        (J1 o ×ˢ {k}).image fun (x, y) ↦ ⟨o, l, by rw [← h']; simpa using h, x, y⟩ else ∅)
      intro ⟨x1, x2⟩ ⟨x1mem, x2mem⟩
      replace hJ1 := hJ1 x1mem
      simp only [Prod.mk.eta, Finset.product_singleton, Finset.mem_biUnion, Finset.mem_attach,
        true_and, Subtype.exists, Finset.mem_antidiagonal, Prod.exists, iUnion_exists, id_eq,
        eq_mp_eq_cast, eq_mpr_eq_cast, mem_iUnion, exists_prop, exists_and_right] at hJ1 ⊢
      obtain ⟨o, oltm, i, imem, x1mem'⟩ := hJ1
      use o + l, (by rw [← hmln]; exact Nat.add_lt_add_right oltm l), ⟨o, l, rfl, i,  k⟩
      refine ⟨?_, by rw [prodmap_image_closedBall]; exact ⟨x1mem', x2mem⟩⟩
      use o, l, rfl
      simp only [↓reduceDIte, Finset.mem_image, Finset.mem_map, Function.Embedding.coeFn_mk,
        exists_exists_and_eq_and]
      use i, imem
    · obtain ⟨J2, hJ2⟩ := cellFrontier_subset_finite_closedCell l k
      use fun n ↦ ((Finset.antidiagonal n).attach.biUnion fun ⟨(o, p), h⟩ ↦ if h' : o = m then
        ({j} ×ˢ J2 p).image fun (x, y) ↦ ⟨m, p, by rw [← h']; simpa using h, x, y⟩ else ∅)
      intro ⟨x1, x2⟩ ⟨x1mem, x2mem⟩
      replace hJ2 := hJ2 x2mem
      simp only [Prod.mk.eta, Finset.product_singleton, Finset.mem_biUnion, Finset.mem_attach,
        true_and, Subtype.exists, Finset.mem_antidiagonal, Prod.exists, iUnion_exists, id_eq,
        eq_mp_eq_cast, eq_mpr_eq_cast, mem_iUnion, exists_prop, exists_and_right] at hJ2 ⊢
      obtain ⟨o, oltm, i, imem, x2mem'⟩ := hJ2
      use m + o, (by rw [← hmln]; exact Nat.add_lt_add_left oltm m), ⟨m, o, rfl, j, i⟩
      refine ⟨?_, by rw [prodmap_image_closedBall]; exact ⟨x1mem, x2mem'⟩⟩
      use m, o, rfl
      simp only [↓reduceDIte, Finset.singleton_product, Finset.mem_image, Finset.mem_map,
        Function.Embedding.coeFn_mk, exists_exists_and_eq_and]
      use i, imem
  closed' A Asub := by
    constructor
    · intro closedA n ⟨m, l, hmln, j, k⟩
      apply closedA.inter
      rw [prodmap_image_closedBall]
      exact isClosed_closedCell.prod isClosed_closedCell
    · intro hA
      rw [KSpace.closed_iff]
      intro K hK
      suffices IsClosed (A ∩ K) by
        exact ⟨A ∩ K, this, by simp only [left_eq_inter, inter_subset_right]⟩
      -- We have `A ∩ K ⊆ (Prod.fst '' K ∩ C) × (Prod.snd '' K ∩ D)`.
      -- Since `Prod.fst '' K` and `Prod.snd '' K` are compact by `IsCompact.image` they are
      -- subsets of a finite union of cells. We call these union `E` and `F`.
      -- So we have `K ⊆ E ×ˢ F`.
      -- But `E ×ˢ F` is just a finite union of cells of the product.
      -- Therefore we are done by `isClosed_iUnion_of_finite` and the assumption `hA`.
      let E := ⋃ (x : Σ (m : ℕ),
        {j : cell C m // ¬ Disjoint (Prod.fst '' K) (openCell m j)}), closedCell (C := C) x.1 x.2
      let F := ⋃ (x : Σ (m : ℕ),
        {j : cell D m // ¬ Disjoint (Prod.snd '' K) (openCell m j)}), closedCell (C := D) x.1 x.2
      have hE : Prod.fst '' K ∩ C ⊆ E := subset_not_disjoint (C := C) (Prod.fst '' K)
      have hF : Prod.snd '' K ∩ D ⊆ F := subset_not_disjoint (C := D) (Prod.snd '' K)
      have hEfinite := compact_inter_finite (C := C) (Prod.fst '' K) (hK.image continuous_fst)
      have hFfinite := compact_inter_finite (C := D) (Prod.snd '' K) (hK.image continuous_snd)
      have Asub' : A ∩ K ⊆ A ∩ E ×ˢ F := by
        apply subset_inter inter_subset_left
        refine subset_trans ?_ (prod_mono hE hF)
        intro ⟨x1, x2⟩ xmem
        constructor
        · exact ⟨((subset_trans inter_subset_right subset_product) xmem).1,
            ((subset_trans inter_subset_left Asub) xmem).1⟩
        · exact ⟨((subset_trans inter_subset_right subset_product) xmem).2,
            ((subset_trans inter_subset_left Asub) xmem).2⟩
      suffices IsClosed (A ∩ E ×ˢ F) by
        rw [← inter_eq_left.2 Asub', ← inter_assoc, inter_comm A K, inter_assoc K A, inter_self,
          inter_assoc]
        exact hK.isClosed.inter this
      simp_rw [E, F, prod_iUnion, iUnion_prod_const, inter_iUnion]
      refine isClosed_iUnion_of_finite fun ⟨n, j, hnj⟩ ↦
        isClosed_iUnion_of_finite fun ⟨m, i, hmi⟩ ↦ ?_
      replace hA : IsClosed (A ∩ prodmap rfl i j '' closedBall 0 1) := hA (m + n) ⟨m, n, rfl, i, j⟩
      rw [prodmap_image_closedBall] at hA
      exact hA
  union' := by
    ext x
    simp_rw [← union (C := C), ← union (C := D), ← iUnion_prod, iUnion_prod', prodcell, mem_iUnion]
    constructor
    · intro ⟨_, ⟨m, l, _, i, j⟩, h⟩
      rw [prodmap_image_closedBall] at h
      use m, l, i, j
    · intro ⟨m, l, i, j, h⟩
      rw [← prodmap_image_closedBall] at h
      use (m + l), ⟨m, l, rfl, i, j⟩

/-- If `C` and `D` are CW-complexes in `X` and `Y` then `C ×ˢ D` is a CW-complex in the k-ification
  of `X × Y`.-/
instance CWComplex_product_kification : CWComplex (X := kification (X × Y)) (C ×ˢ D) where
  cell n := prodcell C D n
  map n i := match i with
    | ⟨m, l, hmln, j, k⟩ => prodmap hmln j k
  source_eq n i := by
    rcases i with  ⟨m, l, hmln, j, k⟩
    ext x
    simp only [prodmap, Equiv.transPartialEquiv_source, IsometryEquiv.coe_toEquiv,
      PartialEquiv.prod_source, source_eq m j, source_eq, closedBall_prod_same, ← Prod.zero_eq_mk,
      mem_preimage, mem_closedBall, dist_zero_right]
    rw [Isometry.norm_map_of_map_zero (by exact (prodisometryequiv hmln).isometry_toFun)]
    rfl
  cont n i := by
    rcases i with  ⟨m, l, hmln, j, k⟩
    simp only [Equiv.transPartialEquiv_eq_trans, PartialEquiv.coe_trans, prodmap]
    apply ContinuousOn.image_comp_continuous
    · rw [Equiv.toPartialEquiv_apply, IsometryEquiv.coe_toEquiv]
      exact (prodisometryequiv hmln).continuous
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
    apply (prodisometryequiv hmln).symm.continuous.comp_continuousOn
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
    -- We first use `prodmap_image_sphere` to write the edge of the cell as a union.
    -- We then use `exists_iff_and_of_upwards_closed` to show that we can verify the
    -- statement seperately for the two parts of the union.
    -- We then do two completely symmetric proofs.
    classical
    rcases i with ⟨m, l, hmln, j, k⟩
    simp_rw [mapsTo']
    rw [prodmap_image_sphere]
    simp_rw [union_subset_iff]
    rw [exists_iff_and_of_upwards_closed]
    swap
    · refine fun J sub K JleK ↦ sub.trans ?_
      repeat apply iUnion_mono fun _ ↦ ?_
      exact iUnion_subset_iUnion_const (fun a ↦ JleK _ a)
    swap
    · refine fun J sub K JleK ↦ sub.trans ?_
      repeat apply iUnion_mono fun _ ↦ ?_
      exact iUnion_subset_iUnion_const (fun a ↦ JleK _ a)
    constructor
    · obtain ⟨J1, hJ1⟩ := cellFrontier_subset_finite_closedCell m j
      use fun n ↦ ((Finset.antidiagonal n).attach.biUnion fun ⟨(o, p), h⟩ ↦ if h' : p = l then
        (J1 o ×ˢ {k}).image fun (x, y) ↦ ⟨o, l, by rw [← h']; simpa using h, x, y⟩ else ∅)
      intro ⟨x1, x2⟩ ⟨x1mem, x2mem⟩
      replace hJ1 := hJ1 x1mem
      simp only [Prod.mk.eta, Finset.product_singleton, Finset.mem_biUnion, Finset.mem_attach,
        true_and, Subtype.exists, Finset.mem_antidiagonal, Prod.exists, iUnion_exists, id_eq,
        eq_mp_eq_cast, eq_mpr_eq_cast, mem_iUnion, exists_prop, exists_and_right] at hJ1 ⊢
      obtain ⟨o, oltm, i, imem, x1mem'⟩ := hJ1
      use o + l, (by rw [← hmln]; exact Nat.add_lt_add_right oltm l), ⟨o, l, rfl, i,  k⟩
      refine ⟨?_, by rw [prodmap_image_closedBall]; exact ⟨x1mem', x2mem⟩⟩
      use o, l, rfl
      simp only [↓reduceDIte, Finset.mem_image, Finset.mem_map, Function.Embedding.coeFn_mk,
        exists_exists_and_eq_and]
      use i, imem
    · obtain ⟨J2, hJ2⟩ := cellFrontier_subset_finite_closedCell l k
      use fun n ↦ ((Finset.antidiagonal n).attach.biUnion fun ⟨(o, p), h⟩ ↦ if h' : o = m then
        ({j} ×ˢ J2 p).image fun (x, y) ↦ ⟨m, p, by rw [← h']; simpa using h, x, y⟩ else ∅)
      intro ⟨x1, x2⟩ ⟨x1mem, x2mem⟩
      replace hJ2 := hJ2 x2mem
      simp only [Prod.mk.eta, Finset.product_singleton, Finset.mem_biUnion, Finset.mem_attach,
        true_and, Subtype.exists, Finset.mem_antidiagonal, Prod.exists, iUnion_exists, id_eq,
        eq_mp_eq_cast, eq_mpr_eq_cast, mem_iUnion, exists_prop, exists_and_right] at hJ2 ⊢
      obtain ⟨o, oltm, i, imem, x2mem'⟩ := hJ2
      use m + o, (by rw [← hmln]; exact Nat.add_lt_add_left oltm m), ⟨m, o, rfl, j, i⟩
      refine ⟨?_, by rw [prodmap_image_closedBall]; exact ⟨x1mem, x2mem'⟩⟩
      use m, o, rfl
      simp only [↓reduceDIte, Finset.singleton_product, Finset.mem_image, Finset.mem_map,
        Function.Embedding.coeFn_mk, exists_exists_and_eq_and]
      use i, imem
  closed' A Asub := by
    constructor
    · intro closedA n ⟨m, l, hmln, j, k⟩
      apply closedA.inter
      rw [prodmap_image_closedBall]
      exact (isClosed_closedCell.prod isClosed_closedCell).mono kification_le
    · intro hA
      rw [KSpace.closed_iff]
      intro K hK
      suffices IsClosed (A ∩ K) by
        exact ⟨A ∩ K, this, by simp only [left_eq_inter, inter_subset_right]⟩
      -- We have `A ∩ K ⊆ (Prod.fst '' K ∩ C) × (Prod.snd '' K ∩ D)`.
      -- Since `Prod.fst '' K` and `Prod.snd '' K` are compact by `IsCompact.image` they are
      -- subsets of a finite union of cells. We call these union `E` and `F`.
      -- So we have `K ⊆ E ×ˢ F`.
      -- But `E ×ˢ F` is just a finite union of cells of the product.
      -- Therefore we are done by `isClosed_iUnion_of_finite` and the assumption `hA`.
      let E := ⋃ (x : Σ (m : ℕ),
        {j : cell C m // ¬ Disjoint (Prod.fst '' K) (openCell m j)}), closedCell (C := C) x.1 x.2
      let F := ⋃ (x : Σ (m : ℕ),
        {j : cell D m // ¬ Disjoint (Prod.snd '' K) (openCell m j)}), closedCell (C := D) x.1 x.2
      have hE : Prod.fst '' K ∩ C ⊆ E := subset_not_disjoint (C := C) (Prod.fst '' K)
      have hF : Prod.snd '' K ∩ D ⊆ F := subset_not_disjoint (C := D) (Prod.snd '' K)
      have hEfinite := compact_inter_finite (C := C) (Prod.fst '' K)
        (hK.image (from_kification_continuous_of_continuous _ continuous_fst))
      have hFfinite := compact_inter_finite (C := D) (Prod.snd '' K)
        (hK.image (from_kification_continuous_of_continuous _ continuous_snd))
      have Asub' : A ∩ K ⊆ A ∩ E ×ˢ F := by
        apply subset_inter inter_subset_left
        refine subset_trans ?_ (prod_mono hE hF)
        intro ⟨x1, x2⟩ xmem
        constructor
        · exact ⟨((subset_trans inter_subset_right subset_product) xmem).1,
            ((subset_trans inter_subset_left Asub) xmem).1⟩
        · exact ⟨((subset_trans inter_subset_right subset_product) xmem).2,
            ((subset_trans inter_subset_left Asub) xmem).2⟩
      suffices IsClosed (A ∩ E ×ˢ F) by
        rw [← inter_eq_left.2 Asub', ← inter_assoc, inter_comm A K, inter_assoc K A, inter_self,
          inter_assoc]
        exact hK.isClosed.inter this
      simp_rw [E, F, prod_iUnion, iUnion_prod_const, inter_iUnion]
      refine isClosed_iUnion_of_finite fun ⟨n, j, hnj⟩ ↦
        isClosed_iUnion_of_finite fun ⟨m, i, hmi⟩ ↦ ?_
      replace hA : IsClosed (A ∩ prodmap rfl i j '' closedBall 0 1) := hA (m + n) ⟨m, n, rfl, i, j⟩
      rw [prodmap_image_closedBall] at hA
      exact hA
  union' := by
    ext x
    simp_rw [← union (C := C), ← union (C := D), ← iUnion_prod, iUnion_prod', prodcell, mem_iUnion]
    constructor
    · intro ⟨_, ⟨m, l, _, i, j⟩, h⟩
      rw [prodmap_image_closedBall] at h
      use m, l, i, j
    · intro ⟨m, l, i, j, h⟩
      rw [← prodmap_image_closedBall] at h
      use (m + l), ⟨m, l, rfl, i, j⟩


end
