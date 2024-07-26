import CWcomplexes.auxiliary

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

class KSpace  (X : Type*) [TopologicalSpace X] where
  isOpen_iff A : IsOpen A ↔
    ∀ (B : TopologicalSpace.Compacts X), ∃ (C : TopologicalSpace.Opens X), A ∩ B.1 = C.1 ∩ B.1

namespace KSpace

lemma closed_iff {X : Type*} [TopologicalSpace X] [KSpace X] {A : Set X} :
    IsClosed A ↔ ∀ (B : TopologicalSpace.Compacts X),
    ∃ (C: TopologicalSpace.Closeds X), A ∩ B.1 = C.1 ∩ B.1 :=
  calc
    IsClosed A ↔ IsOpen  Aᶜ := isOpen_compl_iff.symm
    _ ↔ ∀ (B : TopologicalSpace.Compacts X), ∃ (C: TopologicalSpace.Opens X),
        Aᶜ ∩ B.1 = C.1 ∩ B.1 := KSpace.isOpen_iff Aᶜ
    _ ↔ ∀ (B : TopologicalSpace.Compacts X), ∃ (C: TopologicalSpace.Closeds X),
        A ∩ B.1 = C.1 ∩ B.1 := by
      congrm ∀ B, ?_
      nth_rw 2 [← compl_compl A]
      exact open_in_iff_compl_closed_in Aᶜ B

def kspace_of_closed_iff {X : Type*} [TopologicalSpace X]
    (closed_iff : ∀ (A : Set X), IsClosed A ↔ ∀ (B : TopologicalSpace.Compacts X),
    ∃ (C: TopologicalSpace.Closeds X), A ∩ B.1 = C.1 ∩ B.1) : KSpace X where
  isOpen_iff := fun A ↦
    calc
    IsOpen A ↔ IsClosed Aᶜ := isClosed_compl_iff.symm
    _ ↔ ∀ (B : TopologicalSpace.Compacts X), ∃ (C: TopologicalSpace.Closeds X),
        Aᶜ ∩ B.1 = C.1 ∩ B.1 := closed_iff Aᶜ
    _ ↔ ∀ (B : TopologicalSpace.Compacts X), ∃ (C: TopologicalSpace.Opens X),
        A ∩ B.1 = C.1 ∩ B.1 := by
      congrm ∀ B, ?_
      exact (open_in_iff_compl_closed_in A B).symm

def kification (X : Type*) := X

instance instkification {X : Type*} [t : TopologicalSpace X] : TopologicalSpace (kification X) where
  IsOpen A := ∀ (B : t.Compacts), ∃ (C: t.Opens), A ∩ B.1 = C.1 ∩ B.1
  isOpen_univ := fun B ↦ (by use ⟨Set.univ, isOpen_univ⟩)
  isOpen_inter := by
    intro A1 A2 h1 h2 B
    rcases h1 B with ⟨C1, g1⟩
    rcases h2 B with ⟨C2, g2⟩
    use ⟨C1.1 ∩ C2.1, IsOpen.inter C1.2 C2.2⟩
    calc
      A1 ∩ A2 ∩ B.1 = (A1 ∩ B.1) ∩ (A2 ∩ B.1) := by simp [Set.inter_assoc, Set.inter_comm]
      _ = (C1.1 ∩ B.1) ∩ (C2.1 ∩ B.1) := by rw [g1, g2]
      _ = C1.1 ∩ C2.1 ∩ B.1 := by simp [← Set.inter_assoc, Set.inter_comm]
  isOpen_sUnion := by
    intro s h B
    let f := fun (t1 : s) ↦ Classical.choose (h t1 (by simp only [Subtype.coe_prop]) B)
    use ⟨⋃ (t : s), (f t).1 , isOpen_iUnion (fun t ↦ (f t).2)⟩
    simp_rw [Set.sUnion_eq_iUnion, Set.iUnion_inter]
    apply Set.iUnion_congr
    intro i
    simp only [TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Opens.carrier_eq_coe, f]
    exact Classical.choose_spec (h i (by simp only [Subtype.coe_prop]) B)

lemma kification.closed_iff {X : Type*} [t : TopologicalSpace X] {A : Set X} :
    IsClosed (X := kification X) A ↔ ∀ (B : t.Compacts), ∃ (C: t.Closeds), A ∩ B.1 = C.1 ∩ B.1 := by
  calc
    IsClosed (X := kification X) A ↔ IsOpen (X := kification X) Aᶜ :=
      (@isOpen_compl_iff (kification X) A _).symm
    _ ↔ ∀ (B : t.Compacts), ∃ (C: t.Opens), Aᶜ ∩ B.1 = C.1 ∩ B.1 := by
      simp only [IsOpen, instkification, TopologicalSpace.Compacts.carrier_eq_coe,
        TopologicalSpace.Opens.carrier_eq_coe]
    _ ↔ ∀ (B : t.Compacts), ∃ (C: t.Closeds), A ∩ B.1 = C.1 ∩ B.1 := by
      congrm ∀ B, ?_
      nth_rw 2 [← compl_compl A]
      exact open_in_iff_compl_closed_in Aᶜ B

def tokification (X : Type*) : X ≃ kification X :=
  ⟨fun x ↦ x, fun x ↦ x, fun _ ↦ rfl, fun _ ↦ rfl⟩

def fromkification (X : Type*) : kification X ≃ X :=
  ⟨fun x ↦ x, fun x ↦ x, fun _ ↦ rfl, fun _ ↦ rfl⟩

lemma continuous_fromkification {X : Type*} [t : TopologicalSpace X] :
    Continuous (fromkification X) where
  isOpen_preimage A hA := by
    simp only [fromkification, instkification, Equiv.coe_fn_mk, Set.preimage_id', IsOpen]
    intro B
    use ⟨A, hA⟩

lemma isopenmap_tokification {X : Type*} [t: TopologicalSpace X] : IsOpenMap (tokification X) := by
  unfold IsOpenMap tokification
  intro A hA
  simp only [IsOpen, instkification, TopologicalSpace.Compacts.carrier_eq_coe,
    TopologicalSpace.Opens.carrier_eq_coe, Equiv.coe_fn_mk, Set.image_id']
  intro B
  use ⟨A, hA⟩
  simp only [TopologicalSpace.Opens.coe_mk]

lemma kification_le {X : Type*} [t : TopologicalSpace X] :
    (instkification : TopologicalSpace X) ≤ (t : TopologicalSpace X) := by
  rw [← continuous_id_iff_le]
  suffices Continuous (fromkification X) by
    simpa only [fromkification, Equiv.coe_fn_mk]
  exact continuous_fromkification

lemma isCompact_iff_isCompact_tokification_image {X : Type*} [TopologicalSpace X] (C : Set X) :
    IsCompact C ↔ IsCompact (tokification X '' C) := by
  constructor
  swap
  · intro compactC
    simp only [tokification, Equiv.coe_fn_mk, Set.image_id'] at compactC
    suffices IsCompact (fromkification X '' C) by
      simpa only [fromkification, Equiv.coe_fn_mk, Set.image_id']
    exact IsCompact.image compactC continuous_fromkification
  intro compactC
  rw [isCompact_iff_finite_subcover]
  intro ι U openU CsubU
  unfold IsOpen instkification at openU
  choose U' hU' using openU
  have CsubU' : C ⊆ ⋃ i, U' i ⟨C, compactC⟩ := by
    calc
      C = C ∩ ⋃ i, U i := by
        simp_rw [tokification, Equiv.coe_fn_mk, Set.image_id'] at CsubU
        rw [Set.inter_eq_left.2 CsubU]
      _ = ⋃ i, C ∩ U i := Set.inter_iUnion _ _
      _ = ⋃ i, C ∩ U' i ⟨C, compactC⟩ := by
        apply Set.iUnion_congr
        intro i
        rw [Set.inter_comm, Set.inter_comm C, hU' i ⟨C, compactC⟩]
        rfl
      _ = C ∩ ⋃ i, U' i ⟨C, compactC⟩ := (Set.inter_iUnion _ _).symm
      _ ⊆ ⋃ i, U' i ⟨C, compactC⟩ := Set.inter_subset_right
  rcases (isCompact_iff_finite_subcover.1 compactC) (fun i ↦ U' i ⟨C, compactC⟩)
    (fun i ↦ (U' i ⟨C, compactC⟩).2) CsubU' with ⟨ι', hι'⟩
  use ι'
  simp_rw [tokification, Equiv.coe_fn_mk, Set.image_id']
  calc
    C = C ∩ ⋃ i ∈ ι', U' i ⟨C, compactC⟩ := (Set.inter_eq_left.2 hι').symm
    _ = ⋃ i ∈ ι', C ∩ U' i ⟨C, compactC⟩ := by simp_rw [Set.inter_iUnion]
    _ = ⋃ i ∈ ι', C ∩ U i := by
      apply Set.iUnion_congr
      intro i
      apply Set.iUnion_congr
      intro _
      rw [Set.inter_comm, Set.inter_comm C, hU' i ⟨C, compactC⟩]
      rfl
    _ = C ∩ ⋃ i ∈ ι', U i := by simp_rw [Set.inter_iUnion]
    _ ⊆ ⋃ i ∈ ι', U i := Set.inter_subset_right

lemma isCompact_iff_isCompact_in_kification {X : Type*} [TopologicalSpace X] (C : Set X) :
    IsCompact C ↔ IsCompact (X := kification X) C := by
  suffices IsCompact C ↔ IsCompact (tokification X '' C) by
    simpa only [tokification, Equiv.coe_fn_mk, Set.image_id']
  exact isCompact_iff_isCompact_tokification_image C

instance kspace_kification {X : Type*} [TopologicalSpace X] : KSpace (kification X) where
  isOpen_iff A := by
    refine ⟨fun openA _ ↦ ⟨⟨A, openA⟩, rfl⟩ , ?_⟩
    intro h
    unfold IsOpen instkification
    intro C
    rcases h ⟨tokification X '' C.1, (isCompact_iff_isCompact_tokification_image C).1 C.2⟩
      with ⟨⟨E, openE⟩, hE⟩
    unfold IsOpen instkification at openE
    rcases openE C with ⟨F, hF⟩
    use F
    simp_rw [tokification, Equiv.coe_fn_mk, Set.image_id'] at hE
    rw [hE, hF]

lemma kification_kspace_eq_self {X :Type*} [t : TopologicalSpace X] [KSpace X] :
    t = instkification := by
  simp_rw [TopologicalSpace.ext_iff, KSpace.isOpen_iff, IsOpen, instkification]
  exact fun _ ↦ trivial

lemma from_kification_continuous_of_continuous {X Y : Type*} [tX : TopologicalSpace X]
    [tY : TopologicalSpace Y] (f : X → Y) (cont : Continuous f) :
    Continuous (X := kification X) f := by
  rw [continuous_def] at cont ⊢
  intro s opens
  exact (TopologicalSpace.le_def.1 kification_le) (f ⁻¹' s) (cont s opens)

lemma from_kification_continuouson_of_continuouson {X Y : Type*} [tX : TopologicalSpace X]
    [tY : TopologicalSpace Y] (f : X → Y) (s : Set X) (conton : ContinuousOn f s) :
    ContinuousOn (X := kification X) f s := by
  rw [continuousOn_iff'] at conton ⊢
  intro t opent
  rcases conton t opent with ⟨u, openu, usub⟩
  use u
  exact ⟨(TopologicalSpace.le_def.1 kification_le) u openu, usub⟩

lemma continuous_compact_to_kification {X Y : Type*} [tX : TopologicalSpace X]
    [tY : TopologicalSpace Y] [CompactSpace X] (f : X → Y) (cont : Continuous f) :
    Continuous (Y := kification Y) f := by
  simp_rw [continuous_iff_isClosed]
  intro s closeds
  simp_rw [kification.closed_iff, kification] at closeds
  rcases closeds ⟨Set.range f, isCompact_range cont⟩ with ⟨u, hu⟩
  suffices IsClosed (f ⁻¹' (s ∩ Set.range f)) by
    simpa only [Set.preimage_inter, Set.preimage_range, Set.inter_univ]
  rw [hu, Set.preimage_inter, Set.preimage_range, Set.inter_univ]
  exact IsClosed.preimage cont u.2

lemma continuousOn_compact_to_kification {X Y : Type*} [tX : TopologicalSpace X]
    [tY : TopologicalSpace Y] {A : Set X} (compact : IsCompact A)
    (f : X → Y) (conton : ContinuousOn f A) : ContinuousOn (Y := kification Y) f A := by
  rw [continuousOn_iff_continuous_restrict] at conton ⊢
  have _ := isCompact_iff_compactSpace.1 compact
  exact continuous_compact_to_kification (A.restrict f) conton

-- proof from Munkres, James Raymond. Topology. 2. ed., Pearson new internat. ed. Harlow: Pearson, 2014. Print. Lemma 46.4
lemma continuous_kification_of_continuousOn_compact {X Y : Type*} [tX : TopologicalSpace X]
    [tY : TopologicalSpace Y] (f : X → Y) (conton : ∀ (C : tX.Compacts), ContinuousOn f C) :
    Continuous (X := kification X) (Y := kification Y) f := by
  have conton' :  ∀ (C : tX.Compacts), ContinuousOn (Y := kification Y) f C :=
    fun C ↦ continuousOn_compact_to_kification C.2 f (conton C)
  rw [continuous_def]
  intro V openV
  simp only [IsOpen, instkification, TopologicalSpace.Compacts.carrier_eq_coe,
    TopologicalSpace.Opens.carrier_eq_coe]
  intro C
  replace conton' := conton' C
  rw [continuousOn_iff'] at conton'
  rcases conton' V openV with ⟨U, openU, hU⟩
  use ⟨U, openU⟩
  exact hU

lemma continuous_kification_of_continuous {X Y : Type*} [tX : TopologicalSpace X]
    [tY : TopologicalSpace Y] (f : X → Y) (cont : Continuous f) :
    @Continuous (kification X) (kification Y) instkification instkification f := by
  apply continuous_kification_of_continuousOn_compact
  intro C
  exact Continuous.continuousOn cont

-- proof from Munkres, James Raymond. Topology. 2. ed., Pearson new internat. ed. Harlow: Pearson, 2014. Print. Lemma 46.3
instance kspace_kification_of_WeaklyLocallyCompactSpace {X : Type*} [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] : KSpace X where
  isOpen_iff := by
    intro A
    refine ⟨fun openA _ ↦ ⟨⟨A, openA ⟩, rfl⟩, ?_⟩
    intro hA
    rw [isOpen_iff_mem_nhds]
    intro x xmemA
    rcases WeaklyLocallyCompactSpace.exists_compact_mem_nhds x with ⟨C, compact, Cnhds⟩
    rw [mem_nhds_iff] at Cnhds ⊢
    rcases Cnhds with ⟨U, Usub, openU, xmemU⟩
    use A ∩ U
    refine ⟨Set.inter_subset_left, ?_, ⟨xmemA, xmemU⟩⟩
    rcases hA ⟨C, compact⟩ with ⟨⟨V, openV⟩, hV⟩
    rw [← Set.inter_eq_right.2 Usub, ← Set.inter_assoc, hV, Set.inter_assoc,
      Set.inter_eq_right.2 Usub]
    exact IsOpen.inter openV openU

-- proof from https://math.stackexchange.com/questions/2026072/a-first-countable-hausdorff-space-is-compactly-generated
-- and Munkres
instance kspace_of_SequentialSpace {X : Type*} [TopologicalSpace X]
    [SequentialSpace X]: KSpace X := kspace_of_closed_iff (by
  intro A
  refine ⟨fun closedA _ ↦ ⟨⟨A, closedA⟩, rfl⟩, ?_⟩
  intro hA
  rw [← isSeqClosed_iff_isClosed]
  apply isSeqClosed_of_seqClosure_eq
  refine subset_antisymm ?_ subset_seqClosure
  intro p pmem
  rw [seqClosure, Set.mem_setOf_eq] at pmem
  rcases pmem with ⟨x, xmem, tendsto⟩
  rcases hA ⟨insert p (Set.range x), Filter.Tendsto.isCompact_insert_range tendsto⟩ with
    ⟨⟨C, closedC⟩, hC⟩
  suffices p ∈ A ∩ insert p (Set.range x) by
    simpa only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_range, true_or, and_true]
  rw [hC, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_range, eq_self, true_or, and_true]
  rw [← isSeqClosed_iff_isClosed, IsSeqClosed] at closedC
  refine closedC ?_ tendsto
  intro n
  suffices x n ∈ C ∩ insert p (Set.range x) by simpa only [Set.mem_inter_iff, Set.mem_insert_iff,
    Set.mem_range, exists_apply_eq_apply, or_true, and_true]
  rw [← hC]
  simp_rw [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_range, exists_apply_eq_apply, or_true,
    and_true]
  exact xmem n
  )
