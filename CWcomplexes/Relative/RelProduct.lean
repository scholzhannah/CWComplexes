import CWcomplexes.Relative.RelLemmas
import CWcomplexes.Relative.KSpace
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

open Metric Set Set.Notation KSpace

namespace CWComplex


section

variable {X : Type*} {Y : Type*} [t1 : TopologicalSpace X] [t2 : TopologicalSpace Y]
  {C D : Set X} {E F : Set Y}

/-- The indexing types of cells of the product of two CW-complexes.-/
def prodcell (C : Set X) {D : Set X} (E : Set Y) {F : Set Y} [RelCWComplex C D] [RelCWComplex E F]
    (n : ℕ) :=
  (Σ' (m : ℕ) (l : ℕ) (_ : m + l = n), cell C m × cell E l)

/-- The natural `IsometryEquiv` `(Fin n → ℝ) ≃ᵢ (Fin m → ℝ) × (Fin l → ℝ)` when `n = m + n`.-/
def prodisometryequiv {n m l : ℕ}  (hmln : m + l = n) :=
  (IsometryEquiv.piCongrLeft (Y := fun _ ↦ ℝ) (finCongr hmln.symm)).trans
  ((Fin.appendIsometry m l).symm)

/-- The characterstic maps of the product of CW-complexes.-/
def prodmap [RelCWComplex C D] [RelCWComplex E F] {n m l : ℕ} (hmln : m + l = n)
    (j : cell C m) (k : cell E l) :=
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

lemma prodmap_image_ball [RelCWComplex C D] [RelCWComplex E F] {n m l : ℕ} {hmln : m + l = n}
    {j : cell C m} {k : cell E l} :
    prodmap hmln j k '' ball 0 1 = (openCell m j) ×ˢ (openCell l k) := by
  simp_rw [prodmap, Equiv.transPartialEquiv_apply, ← image_image, IsometryEquiv.coe_toEquiv,
    prodisometryequiv_image_ball, PartialEquiv.prod_coe, ← prod_image_image_eq]
  rfl

lemma prodmap_image_sphere [RelCWComplex C D] [RelCWComplex E F] {n m l : ℕ} {hmln : m + l = n}
    {j : cell C m} {k : cell E l} :
    prodmap hmln j k '' sphere 0 1 = (cellFrontier m j) ×ˢ (closedCell l k) ∪
    (closedCell m j) ×ˢ (cellFrontier l k) := by
  simp_rw [prodmap, Equiv.transPartialEquiv_apply, ← image_image , IsometryEquiv.coe_toEquiv,
    prodisometryequiv_image_sphere, image_union, PartialEquiv.prod_coe, ← prod_image_image_eq]
  rfl

lemma prodmap_image_closedBall [RelCWComplex C D] [RelCWComplex E F] {n m l : ℕ} {hmln : m + l = n}
    {j : cell C m} {k : cell E l} : prodmap hmln j k ''
    closedBall 0 1 = (closedCell m j) ×ˢ (closedCell l k) := by
  simp_rw [prodmap, Equiv.transPartialEquiv_apply, ← image_image , IsometryEquiv.coe_toEquiv,
    prodisometryequiv_image_closedBall, PartialEquiv.prod_coe, ← prod_image_image_eq]
  rfl

lemma iUnion_prodcell [RelCWComplex C D] [RelCWComplex E F] :
    ⋃ n, ⋃ (i : prodcell C E n), prodmap i.2.2.1 i.2.2.2.1 i.2.2.2.2 '' closedBall 0 1
    = (⋃ m, ⋃ (i : cell C m), closedCell m i) ×ˢ ⋃ l, ⋃ (j : cell E l), closedCell l j := by
  ext x
  simp only [prodcell, prodmap_image_closedBall, iUnion_psigma, iUnion_sigma, prod_iUnion,
    iUnion_prod_const, iUnion_prod, mem_iUnion]
  constructor
  · intro ⟨n, m, l, _, i, j, h⟩
    use l, i, m, j
  · intro ⟨m, i, l, j, h⟩
    use m + l, l, m, add_comm l m, i, j

variable [T2Space X] [T2Space Y]

/-- If `C` and `E` are CW-complexes in `X` and `Y` relative to `D` and `F`,
  and `X × Y` is a k-space, then `C ×ˢ D` is a CW-complex relative to `D ×ˢ E ∪ C ×ˢ F`.-/
@[simps]
instance RelCWComplex_product [RelCWComplex C D] [RelCWComplex E F] [KSpace (X × Y)] :
    RelCWComplex (C ×ˢ E) (D ×ˢ E ∪ C ×ˢ F) where
  cell n := prodcell C E n
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
    · rw [Equiv.toPartialEquiv_apply, IsometryEquiv.coe_toEquiv, prodisometryequiv_image_closedBall]
      simp only [PartialEquiv.prod_coe]
      exact ContinuousOn.prod_map (CWComplex.cont _ _) (CWComplex.cont _ _)
    · rw [Equiv.toPartialEquiv_apply, IsometryEquiv.coe_toEquiv]
      exact (prodisometryequiv hmln).continuous
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
    suffices (⟨m, j⟩ : Σ n, cell C n) ≠ ⟨p, i⟩ ∨  (⟨l, k⟩ : Σ n, cell E n) ≠ ⟨q, o⟩ by
      rcases this with ne1 | ne2
      · exact Or.intro_left _ (disjoint_openCell_of_ne ne1)
      · exact Or.intro_right _ (disjoint_openCell_of_ne ne2)
    by_contra h
    push_neg at h
    apply ne
    aesop
  disjointBase' n := by
    intro ⟨m, l, hml, i, j⟩
    simp [prodmap_image_ball, disjoint_iff_inter_eq_empty, inter_union_distrib_left,
      prod_inter_prod, (disjointBase _ _).inter_eq]
  mapsto n i := by
    -- We first use `prodmap_image_sphere` to write the edge of the cell as a union.
    -- We then use `exists_and_iff_of_monotone` to show that we can verify the
    -- statement seperately for the two parts of the union.
    -- We then do two completely symmetric proofs.
    classical
    rcases i with ⟨m, l, hmln, j, k⟩
    simp_rw [mapsTo', prodmap_image_sphere, union_subset_iff]
    rw [← exists_and_iff_of_monotone]
    swap
    · refine fun J K JleK sub ↦ sub.trans ?_
      apply union_subset_union_right
      repeat apply iUnion_mono fun _ ↦ ?_
      exact iUnion_subset_iUnion_const (fun a ↦ JleK _ a)
    swap
    · refine fun J K JleK sub ↦ sub.trans ?_
      apply union_subset_union_right
      repeat apply iUnion_mono fun _ ↦ ?_
      exact iUnion_subset_iUnion_const (fun a ↦ JleK _ a)
    constructor
    · obtain ⟨J1, hJ1⟩ := cellFrontier_subset_base_union_finite_closedCell m j
      use fun n ↦ ((Finset.antidiagonal n).attach.biUnion fun ⟨(o, p), h⟩ ↦ if h' : p = l then
        (J1 o ×ˢ {k}).image fun (x, y) ↦ ⟨o, l, by rw [← h']; simpa using h, x, y⟩ else ∅)
      intro ⟨x1, x2⟩ ⟨x1mem, x2mem⟩
      specialize hJ1 x1mem
      simp only [mem_union, mem_iUnion, exists_prop, Prod.mk.eta, Finset.product_singleton,
        Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists, Finset.mem_antidiagonal,
        Prod.exists, iUnion_exists, id_eq, eq_mp_eq_cast, eq_mpr_eq_cast, exists_and_right] at hJ1 ⊢
      rcases hJ1 with hx1D | hJ1
      · left; left
        rw [mem_prod]
        exact ⟨hx1D, mem_of_mem_of_subset x2mem (closedCell_subset_complex l k)⟩
      right
      obtain ⟨o, oltm, i, imem, x1mem'⟩ := hJ1
      use o + l, (by rw [← hmln]; exact Nat.add_lt_add_right oltm l), ⟨o, l, rfl, i,  k⟩
      refine ⟨?_, by rw [prodmap_image_closedBall]; exact ⟨x1mem', x2mem⟩⟩
      use o, l, rfl
      simp only [↓reduceDIte, Finset.mem_image, Finset.mem_map, Function.Embedding.coeFn_mk,
        exists_exists_and_eq_and]
      use i, imem
    · obtain ⟨J2, hJ2⟩ := cellFrontier_subset_base_union_finite_closedCell l k
      use fun n ↦ ((Finset.antidiagonal n).attach.biUnion fun ⟨(o, p), h⟩ ↦ if h' : o = m then
        ({j} ×ˢ J2 p).image fun (x, y) ↦ ⟨m, p, by rw [← h']; simpa using h, x, y⟩ else ∅)
      intro ⟨x1, x2⟩ ⟨x1mem, x2mem⟩
      replace hJ2 := hJ2 x2mem
      simp only [mem_union, mem_iUnion, exists_prop, Prod.mk.eta, Finset.mem_biUnion,
        Finset.mem_attach, true_and, Subtype.exists, Finset.mem_antidiagonal, Prod.exists,
        iUnion_exists, id_eq, eq_mp_eq_cast, eq_mpr_eq_cast, exists_and_right] at hJ2 ⊢
      rcases hJ2 with hx2F | hJ2
      · left; right
        rw [mem_prod]
        exact ⟨mem_of_mem_of_subset x1mem (closedCell_subset_complex m j), hx2F⟩
      right
      obtain ⟨o, oltm, i, imem, x2mem'⟩ := hJ2
      use m + o, (by rw [← hmln]; exact Nat.add_lt_add_left oltm m), ⟨m, o, rfl, j, i⟩
      refine ⟨?_, by rw [prodmap_image_closedBall]; exact ⟨x1mem, x2mem'⟩⟩
      use m, o, rfl
      simp only [↓reduceDIte, Finset.singleton_product, Finset.mem_image, Finset.mem_map,
        Function.Embedding.coeFn_mk, exists_exists_and_eq_and]
      use i, imem
  closed' A Asub := by
    intro ⟨hA, hbase⟩
    rw [KSpace.isClosed_iff]
    intro K hK
    suffices IsClosed (A ∩ K) by
      rw [← Subtype.preimage_coe_inter_self]
      exact isClosed_in_of_isClosed this
    -- We have `A ∩ K ⊆ (Prod.fst '' K ∩ C) × (Prod.snd '' K ∩ E)`.
    -- Since `Prod.fst '' K` and `Prod.snd '' K` are compact by `IsCompact.image` they are
    -- subsets of a finite union of cells. We call these union `H` and `G`.
    -- So we have `K ⊆ H ×ˢ G`.
    -- But `H ×ˢ G` is just a finite union of cells of the product.
    -- Therefore we are done by `isClosed_iUnion_of_finite` and the assumption `hA`.
    let H := D ∪ ⋃ (x : Σ (m : ℕ),
      {j : cell C m // ¬ Disjoint (Prod.fst '' K) (openCell m j)}), closedCell (C := C) x.1 x.2
    let G := F ∪ ⋃ (x : Σ (m : ℕ),
      {j : cell E m // ¬ Disjoint (Prod.snd '' K) (openCell m j)}), closedCell (C := E) x.1 x.2
    have hH : Prod.fst '' K ∩ C ⊆ H := subset_not_disjoint (C := C) (Prod.fst '' K)
    have hG : Prod.snd '' K ∩ E ⊆ G := subset_not_disjoint (C := E) (Prod.snd '' K)
    have hHfinite := compact_inter_finite (C := C) (Prod.fst '' K) (hK.image continuous_fst)
    have hGfinite := compact_inter_finite (C := E) (Prod.snd '' K) (hK.image continuous_snd)
    have Asub' : A ∩ K ⊆ A ∩ H ×ˢ G := by
      apply subset_inter inter_subset_left
      refine subset_trans ?_ (prod_mono hH hG)
      intro ⟨x1, x2⟩ xmem
      constructor
      · exact ⟨((subset_trans inter_subset_right subset_product) xmem).1,
          ((subset_trans inter_subset_left Asub) xmem).1⟩
      · exact ⟨((subset_trans inter_subset_right subset_product) xmem).2,
          ((subset_trans inter_subset_left Asub) xmem).2⟩
    suffices IsClosed (A ∩ H ×ˢ G) by
      rw [← inter_eq_left.2 Asub', ← inter_assoc, inter_comm A K, inter_assoc K A, inter_self,
        inter_assoc]
      exact hK.isClosed.inter this
    simp_rw [H, G, prod_union, union_prod, prod_iUnion, iUnion_prod_const, ← union_assoc]
    rw [inter_union_distrib_left]
    apply IsClosed.union
    · have : (D ×ˢ F ∪ ⋃ (i : (m : ℕ) × { j // ¬Disjoint (Prod.fst '' K) (openCell (C := C) m j) }),
          closedCell i.fst i.snd.1 ×ˢ F) ∪
          ⋃ (i : (m : ℕ) × { j // ¬Disjoint (Prod.snd '' K) (openCell (C := E) m j) }),
          (D ×ˢ closedCell i.fst i.snd.1) ⊆
          (D ×ˢ E ∪ C ×ˢ F) := by
        rw [← iUnion_prod_const, ← prod_iUnion]
        apply union_subset
        apply union_subset
        · exact subset_union_of_subset_left (prod_mono Subset.rfl (base_subset_complex (C := E))) _
        · refine subset_union_of_subset_right (prod_mono ?_ Subset.rfl) _
          exact iUnion_subset fun _ ↦  closedCell_subset_complex _ _
        · apply subset_union_of_subset_left
          apply prod_mono Subset.rfl
          exact iUnion_subset fun _ ↦ closedCell_subset_complex _ _
      rw [← inter_eq_right.2 this, ← inter_assoc]
      apply hbase.inter
      apply IsClosed.union
      apply IsClosed.union
      · exact (isClosedBase C).prod (isClosedBase E)
      · exact isClosed_iUnion_of_finite fun ⟨n, j, hnj⟩ ↦ isClosed_closedCell.prod (isClosedBase E)
      · exact isClosed_iUnion_of_finite fun ⟨n, j, hnj⟩ ↦ (isClosedBase C).prod isClosed_closedCell
    simp_rw [inter_iUnion]
    refine isClosed_iUnion_of_finite fun ⟨n, j, hnj⟩ ↦
      isClosed_iUnion_of_finite fun ⟨m, i, hmi⟩ ↦ ?_
    replace hA : IsClosed (A ∩ prodmap rfl i j '' closedBall 0 1) := hA (m + n) ⟨m, n, rfl, i, j⟩
    rw [prodmap_image_closedBall] at hA
    exact hA
  isClosedBase := ((isClosedBase C).prod isClosed).union (isClosed.prod (isClosedBase E))
  union' := by
    apply subset_antisymm
    · refine union_subset (union_subset (prod_mono base_subset_complex Subset.rfl)
          (prod_mono Subset.rfl base_subset_complex)) ?_
      intro x
      simp only [mem_iUnion, mem_prod, prodcell]
      intro ⟨n, ⟨m, l, eq, i, j⟩, h⟩
      rw [prodmap_image_closedBall] at h
      exact ⟨closedCell_subset_complex m i h.1, closedCell_subset_complex l j h.2⟩
    · simp_rw [iUnion_prodcell]
      intro ⟨x1, x2⟩ ⟨hx1, hx2⟩
      have hx1' := hx1
      simp_rw [← union] at hx1'
      obtain hx1' | hx1' := hx1'
      · left; left
        exact mk_mem_prod hx1' hx2
      simp_rw [← union] at hx2
      obtain hx2 | hx2 := hx2
      · left; right
        exact mk_mem_prod hx1 hx2
      · right
        exact mk_mem_prod hx1' hx2

-- seems like `▸` cannot see through `abbrev`. How do I fix this

/-- If `C` and `E` are CW-complexes in `X` and `Y`, and `X × Y` is a k-space, then `C ×ˢ D` is a
  CW-complex.-/
instance CWComplex_product [CWComplex C] [CWComplex E] [KSpace (X × Y)] : RelCWComplex (C ×ˢ E) ∅ :=
  (congrArg (fun s ↦ RelCWComplex (C ×ˢ E) s) (union_empty_iff.2 ⟨empty_prod, prod_empty⟩)) ▸
    RelCWComplex_product

lemma CWComplex_product_cell [CWComplex C] [CWComplex E] [KSpace (X × Y)] (n : ℕ) :
    cell (C ×ˢ E) n = prodcell C E n :=
  sorry

/-- If `C` and `D` are CW-complexes in `X` and `Y` then `C ×ˢ D` is a CW-complex in the k-ification
  of `X × Y`.-/
@[simps]
instance RelCWComplex_product_kification [RelCWComplex C D] [RelCWComplex E F] :
    RelCWComplex (X := kification (X × Y)) (C ×ˢ E) (D ×ˢ E ∪ C ×ˢ F) where
  cell n := prodcell C E n
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
    · rw [Equiv.toPartialEquiv_apply, IsometryEquiv.coe_toEquiv, prodisometryequiv_image_closedBall]
      simp only [PartialEquiv.prod_coe]
      apply continuousOn_compact_to_kification
        (by rw [closedBall_prod_same]; exact isCompact_closedBall _ _)
      exact ContinuousOn.prod_map (CWComplex.cont _ _) (CWComplex.cont _ _)
    · rw [Equiv.toPartialEquiv_apply, IsometryEquiv.coe_toEquiv]
      exact (prodisometryequiv hmln).continuous
  cont_symm n i := by
    rcases i with ⟨m, l, hmln, j, k⟩
    simp only [Equiv.transPartialEquiv_eq_trans, PartialEquiv.coe_trans_symm,
      Equiv.toPartialEquiv_symm_apply, PartialEquiv.trans_target, PartialEquiv.prod_target,
      Equiv.toPartialEquiv_target, preimage_univ, inter_univ, prodmap]
    apply (prodisometryequiv hmln).symm.continuous.comp_continuousOn
    rw [PartialEquiv.prod_symm]
    exact from_kification_continuousOn_of_continuousOn ((map m j).symm.prod (map l k).symm)
      ((map m j).target ×ˢ (map l k).target) ((cont_symm m j).prod_map (cont_symm l k))
  pairwiseDisjoint' := by
    intro ⟨n1, m, l, hmln1, j, k⟩ _ ⟨n2, p, q, hpqn2, i, o⟩ _ ne
    simp only [Function.onFun, disjoint_iff_inter_eq_empty]
    rw [prodmap_image_ball, prodmap_image_ball, prod_inter_prod, prod_eq_empty_iff]
    suffices (⟨m, j⟩ : Σ n, cell C n) ≠ ⟨p, i⟩ ∨  (⟨l, k⟩ : Σ n, cell E n) ≠ ⟨q, o⟩ by
      rcases this with ne1 | ne2
      · exact Or.intro_left _ (disjoint_openCell_of_ne ne1)
      · exact Or.intro_right _ (disjoint_openCell_of_ne ne2)
    by_contra h
    push_neg at h
    apply ne
    aesop
  disjointBase' n := by
    intro ⟨m, l, hml, i, j⟩
    rw [prodmap_image_ball]
    simp [disjoint_iff_inter_eq_empty, inter_union_distrib_left,
      prod_inter_prod, (disjointBase _ _).inter_eq]
  mapsto n i := by
    -- We first use `prodmap_image_sphere` to write the edge of the cell as a union.
    -- We then use `exists_and_iff_of_monotone` to show that we can verify the
    -- statement seperately for the two parts of the union.
    -- We then do two completely symmetric proofs.
    classical
    rcases i with ⟨m, l, hmln, j, k⟩
    simp_rw [mapsTo']
    rw [prodmap_image_sphere]
    simp_rw [union_subset_iff]
    rw [← exists_and_iff_of_monotone]
    swap
    · refine fun J K JleK sub ↦ sub.trans ?_
      apply union_subset_union_right
      repeat apply iUnion_mono fun _ ↦ ?_
      exact iUnion_subset_iUnion_const (fun a ↦ JleK _ a)
    swap
    · refine fun J K JleK sub ↦ sub.trans ?_
      apply union_subset_union_right
      repeat apply iUnion_mono fun _ ↦ ?_
      exact iUnion_subset_iUnion_const (fun a ↦ JleK _ a)
    constructor
    · obtain ⟨J1, hJ1⟩ := cellFrontier_subset_base_union_finite_closedCell m j
      use fun n ↦ ((Finset.antidiagonal n).attach.biUnion fun ⟨(o, p), h⟩ ↦ if h' : p = l then
        (J1 o ×ˢ {k}).image fun (x, y) ↦ ⟨o, l, by rw [← h']; simpa using h, x, y⟩ else ∅)
      intro ⟨x1, x2⟩ ⟨x1mem, x2mem⟩
      replace hJ1 := hJ1 x1mem
      simp only [mem_union, mem_iUnion, exists_prop, Prod.mk.eta, Finset.product_singleton,
        Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists, Finset.mem_antidiagonal,
        Prod.exists, iUnion_exists, id_eq, eq_mp_eq_cast, eq_mpr_eq_cast, exists_and_right] at hJ1 ⊢
      rcases hJ1 with hx1D | hJ1
      · left; left
        rw [mem_prod]
        exact ⟨hx1D, mem_of_mem_of_subset x2mem (closedCell_subset_complex l k)⟩
      right
      obtain ⟨o, oltm, i, imem, x1mem'⟩ := hJ1
      use o + l, (by rw [← hmln]; exact Nat.add_lt_add_right oltm l), ⟨o, l, rfl, i,  k⟩
      refine ⟨?_, by rw [prodmap_image_closedBall]; exact ⟨x1mem', x2mem⟩⟩
      use o, l, rfl
      simp only [↓reduceDIte, Finset.mem_image, Finset.mem_map, Function.Embedding.coeFn_mk,
        exists_exists_and_eq_and]
      use i, imem
    · obtain ⟨J2, hJ2⟩ := cellFrontier_subset_base_union_finite_closedCell l k
      use fun n ↦ ((Finset.antidiagonal n).attach.biUnion fun ⟨(o, p), h⟩ ↦ if h' : o = m then
        ({j} ×ˢ J2 p).image fun (x, y) ↦ ⟨m, p, by rw [← h']; simpa using h, x, y⟩ else ∅)
      intro ⟨x1, x2⟩ ⟨x1mem, x2mem⟩
      replace hJ2 := hJ2 x2mem
      simp only [mem_union, mem_iUnion, exists_prop, Prod.mk.eta, Finset.mem_biUnion,
        Finset.mem_attach, true_and, Subtype.exists, Finset.mem_antidiagonal, Prod.exists,
        iUnion_exists, id_eq, eq_mp_eq_cast, eq_mpr_eq_cast, exists_and_right] at hJ2 ⊢
      rcases hJ2 with hx2F | hJ2
      · left; right
        rw [mem_prod]
        exact ⟨mem_of_mem_of_subset x1mem (closedCell_subset_complex m j), hx2F⟩
      right
      obtain ⟨o, oltm, i, imem, x2mem'⟩ := hJ2
      use m + o, (by rw [← hmln]; exact Nat.add_lt_add_left oltm m), ⟨m, o, rfl, j, i⟩
      refine ⟨?_, by rw [prodmap_image_closedBall]; exact ⟨x1mem, x2mem'⟩⟩
      use m, o, rfl
      simp only [↓reduceDIte, Finset.singleton_product, Finset.mem_image, Finset.mem_map,
        Function.Embedding.coeFn_mk, exists_exists_and_eq_and]
      use i, imem
  closed' A Asub := by
    intro ⟨hA, hbase⟩
    rw [KSpace.isClosed_iff]
    intro K hK
    suffices IsClosed (A ∩ K) by
      rw [← Subtype.preimage_coe_inter_self]
      exact isClosed_in_of_isClosed this
    -- We have `A ∩ K ⊆ (Prod.fst '' K ∩ C) × (Prod.snd '' K ∩ E)`.
    -- Since `Prod.fst '' K` and `Prod.snd '' K` are compact by `IsCompact.image` they are
    -- subsets of a finite union of cells. We call these union `H` and `G`.
    -- So we have `K ⊆ H ×ˢ G`.
    -- But `H ×ˢ G` is just a finite union of cells of the product.
    -- Therefore we are done by `isClosed_iUnion_of_finite` and the assumption `hA`.
    let H := D ∪ ⋃ (x : Σ (m : ℕ),
      {j : cell C m // ¬ Disjoint (Prod.fst '' K) (openCell m j)}), closedCell (C := C) x.1 x.2
    let G := F ∪ ⋃ (x : Σ (m : ℕ),
      {j : cell E m // ¬ Disjoint (Prod.snd '' K) (openCell m j)}), closedCell (C := E) x.1 x.2
    have hH : Prod.fst '' K ∩ C ⊆ H := subset_not_disjoint (C := C) (Prod.fst '' K)
    have hG : Prod.snd '' K ∩ E ⊆ G := subset_not_disjoint (C := E) (Prod.snd '' K)
    have hHfinite := compact_inter_finite (C := C) (Prod.fst '' K)
      (hK.image (from_kification_continuous_of_continuous _ continuous_fst))
    have hGfinite := compact_inter_finite (C := E) (Prod.snd '' K)
      (hK.image (from_kification_continuous_of_continuous _ continuous_snd))
    have Asub' : A ∩ K ⊆ A ∩ H ×ˢ G := by
      apply subset_inter inter_subset_left
      refine subset_trans ?_ (prod_mono hH hG)
      intro ⟨x1, x2⟩ xmem
      constructor
      · exact ⟨((subset_trans inter_subset_right subset_product) xmem).1,
          ((subset_trans inter_subset_left Asub) xmem).1⟩
      · exact ⟨((subset_trans inter_subset_right subset_product) xmem).2,
          ((subset_trans inter_subset_left Asub) xmem).2⟩
    suffices IsClosed (A ∩ H ×ˢ G) by
      rw [← inter_eq_left.2 Asub', ← inter_assoc, inter_comm A K, inter_assoc K A, inter_self,
        inter_assoc]
      exact hK.isClosed.inter this
    simp_rw [H, G, prod_union, union_prod, prod_iUnion, iUnion_prod_const, ← union_assoc]
    rw [inter_union_distrib_left]
    apply IsClosed.union
    · have : (D ×ˢ F ∪ ⋃ (i : (m : ℕ) × { j // ¬Disjoint (Prod.fst '' K) (openCell (C := C) m j) }),
          closedCell i.fst i.snd.1 ×ˢ F) ∪
          ⋃ (i : (m : ℕ) × { j // ¬Disjoint (Prod.snd '' K) (openCell (C := E) m j) }),
          (D ×ˢ closedCell i.fst i.snd.1) ⊆
          (D ×ˢ E ∪ C ×ˢ F) := by
        rw [← iUnion_prod_const, ← prod_iUnion]
        apply union_subset
        apply union_subset
        · exact subset_union_of_subset_left (prod_mono Subset.rfl (base_subset_complex (C := E))) _
        · refine subset_union_of_subset_right (prod_mono ?_ Subset.rfl) _
          exact iUnion_subset fun _ ↦  closedCell_subset_complex _ _
        · apply subset_union_of_subset_left
          apply prod_mono Subset.rfl
          exact iUnion_subset fun _ ↦ closedCell_subset_complex _ _
      rw [← inter_eq_right.2 this, ← inter_assoc]
      apply hbase.inter
      apply IsClosed.union
      apply IsClosed.union
      · exact ((isClosedBase C).prod (isClosedBase E)).mono kification_le
      · exact isClosed_iUnion_of_finite fun ⟨n, j, hnj⟩ ↦
          (isClosed_closedCell.prod (isClosedBase E)).mono kification_le
      · exact isClosed_iUnion_of_finite fun ⟨n, j, hnj⟩ ↦
          ((isClosedBase C).prod isClosed_closedCell).mono kification_le
    simp_rw [inter_iUnion]
    refine isClosed_iUnion_of_finite fun ⟨n, j, hnj⟩ ↦
      isClosed_iUnion_of_finite fun ⟨m, i, hmi⟩ ↦ ?_
    replace hA : IsClosed (A ∩ prodmap rfl i j '' closedBall 0 1) := hA (m + n) ⟨m, n, rfl, i, j⟩
    rw [prodmap_image_closedBall] at hA
    exact hA
  isClosedBase := (((isClosedBase C).prod isClosed).union (isClosed.prod (isClosedBase E))).mono
    kification_le
  union' := by
    apply subset_antisymm
    · refine union_subset (union_subset (prod_mono base_subset_complex Subset.rfl)
          (prod_mono Subset.rfl base_subset_complex)) ?_
      intro x
      simp only [mem_iUnion, mem_prod, prodcell]
      intro ⟨n, ⟨m, l, eq, i, j⟩, h⟩
      rw [prodmap_image_closedBall] at h
      exact ⟨closedCell_subset_complex m i h.1, closedCell_subset_complex l j h.2⟩
    · rw [iUnion_prodcell]
      intro ⟨x1, x2⟩ ⟨hx1, hx2⟩
      have hx1' := hx1
      simp_rw [← union] at hx1'
      obtain hx1' | hx1' := hx1'
      · left; left
        exact mk_mem_prod hx1' hx2
      simp_rw [← union] at hx2
      obtain hx2 | hx2 := hx2
      · left; right
        exact mk_mem_prod hx1 hx2
      · right
        exact mk_mem_prod hx1' hx2

/-- If `C` and `E` are CW-complexes in `X` and `Y`, and `X × Y` is a k-space, then `C ×ˢ D` is a
  CW-complex.-/
instance CWComplex_product_kification [CWComplex C] [CWComplex E] :
    CWComplex (X := kification (X × Y)) (C ×ˢ E) :=
  (congrArg (fun s ↦ RelCWComplex (X := kification (X × Y)) (C ×ˢ E) s)
    (union_empty_iff.2 ⟨empty_prod (t := E), prod_empty (s := C)⟩)).mp
    RelCWComplex_product_kification

end