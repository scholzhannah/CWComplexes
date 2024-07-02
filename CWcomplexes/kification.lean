import CWcomplexes.auxiliary

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Kification

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

def tokification (X : Type*) : X ≃ kification X := ⟨fun x ↦ x, fun x ↦ x, fun _ ↦ rfl, fun _ ↦ rfl⟩

def fromkification (X : Type*) : kification X ≃ X := ⟨fun x ↦ x, fun x ↦ x, fun _ ↦ rfl, fun _ ↦ rfl⟩

lemma continuous_fromkification {X : Type*} [t : TopologicalSpace X] : Continuous (fromkification X) where
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

lemma kification_le {X : Type*} [t : TopologicalSpace X] : (instkification : TopologicalSpace X) ≤ (t : TopologicalSpace X) := by
  intro A OpenA
  simp only [IsOpen, instkification, TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Opens.carrier_eq_coe]
  intro B
  use ⟨A, OpenA⟩
  simp only [TopologicalSpace.Opens.coe_mk]

lemma kification.closed_iff {X : Type*} [t : TopologicalSpace X] {A : Set X} : @IsClosed (kification X) _ A ↔ ∀ (B : t.Compacts), ∃ (C: t.Closeds), A ∩ B.1 = C.1 ∩ B.1 := by
  calc
    @IsClosed (kification X) _ A ↔ @IsOpen (kification X) _ Aᶜ := (@isOpen_compl_iff (kification X) A _).symm
    _ ↔ ∀ (B : t.Compacts), ∃ (C: t.Opens), Aᶜ ∩ B.1 = C.1 ∩ B.1 := by simp only [IsOpen,
      instkification, TopologicalSpace.Compacts.carrier_eq_coe,
      TopologicalSpace.Opens.carrier_eq_coe]
    _ ↔ ∀ (B : t.Compacts), ∃ (C: t.Closeds), A ∩ B.1 = C.1 ∩ B.1 := by
      constructor
      · intro h B
        rcases h B with ⟨O, hO⟩
        use ⟨Oᶜ, isClosed_compl_iff.2 O.2⟩
        rw [inter_eq_inter_iff_compl]
        simp only [TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Opens.carrier_eq_coe,
          compl_compl] at hO ⊢
        exact hO
      · intro h B
        rcases h B with ⟨C, hC⟩
        use ⟨Cᶜ, isOpen_compl_iff.2 C.2⟩
        rw [inter_eq_inter_iff_compl]
        simp only [TopologicalSpace.Compacts.carrier_eq_coe, compl_compl] at hC ⊢
        exact hC

lemma from_kification_continuous_of_continuous {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] (f : X → Y)
(cont : Continuous f) : @Continuous _ _ instkification _ f := by
  rw [continuous_def] at cont ⊢
  intro s opens
  exact (TopologicalSpace.le_def.1 kification_le) (f ⁻¹' s) (cont s opens)

lemma from_kification_continuouson_of_continuouson {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] (f : X → Y) (s : Set X)
(conton : ContinuousOn f s) : @ContinuousOn _ _ instkification _ f s := by
  rw [continuousOn_iff'] at conton ⊢
  intro t opent
  rcases conton t opent with ⟨u, openu, usub⟩
  use u
  exact ⟨(TopologicalSpace.le_def.1 kification_le) u openu, usub⟩

-- proof from Munkres, James Raymond. Topology. 2. ed., Pearson new internat. ed. Harlow: Pearson, 2014. Print. Lemma 46.3
lemma kification_eq_self_of_WeaklyLocallyCompactSpace {X : Type*} [t : TopologicalSpace X] [WeaklyLocallyCompactSpace X] : instkification = t := by
  apply le_antisymm
  · exact kification_le
  · intro A hA
    unfold IsOpen instkification at hA
    simp only [TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Opens.carrier_eq_coe] at hA
    simp only [kification]
    rw [@isOpen_iff_mem_nhds X A t]
    intro x xmemA
    rcases WeaklyLocallyCompactSpace.exists_compact_mem_nhds x with ⟨C, compact, Cnhds⟩
    rw [@mem_nhds_iff X x _ t] at Cnhds ⊢
    rcases Cnhds with ⟨U, Usub, openU, xmemU⟩
    use A ∩ U
    refine ⟨Set.inter_subset_left, ?_, ⟨xmemA, xmemU⟩⟩
    rcases hA ⟨C, compact⟩ with ⟨⟨V, openV⟩, hV⟩
    simp only [TopologicalSpace.Compacts.coe_mk, TopologicalSpace.Opens.coe_mk] at hV
    rw [← Set.inter_eq_right.2 Usub, ← Set.inter_assoc, hV, Set.inter_assoc, Set.inter_eq_right.2 Usub]
    exact IsOpen.inter openV openU

lemma continuous_compact_to_kification {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] (compact : CompactSpace X)
(f: X → Y) (cont : Continuous f) : @Continuous X Y tX instkification f := by
  rw [@continuous_iff_isClosed _ _ _ instkification]
  intro s closeds
  rw [@kification.closed_iff _ tY _] at closeds
  rcases closeds ⟨Set.range f, isCompact_range cont⟩ with ⟨u, hu⟩
  have : f ⁻¹' s = f ⁻¹' (s ∩ Set.range f) := by
    rw [Set.preimage_inter, Set.preimage_range, Set.inter_univ]
  rw [this, hu, Set.preimage_inter, Set.preimage_range, Set.inter_univ]
  exact IsClosed.preimage cont u.2

lemma continuousOn_compact_to_kification {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {A : Set X} (compact : IsCompact A)
(f : X → Y) (conton : ContinuousOn f A) : @ContinuousOn _ _ _ instkification f A := by
  rw [continuousOn_iff_continuous_restrict] at conton ⊢
  exact continuous_compact_to_kification (isCompact_iff_compactSpace.1 compact) (A.restrict f) conton

-- proof from Munkres, James Raymond. Topology. 2. ed., Pearson new internat. ed. Harlow: Pearson, 2014. Print. Lemma 46.4
lemma continuous_kification_of_continuousOn_compact {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] (f : X → Y)
    (conton : ∀ (C : tX.Compacts), ContinuousOn f C) :
    @Continuous (kification X) (kification Y) instkification instkification f := by
  have conton' :  ∀ (C : tX.Compacts), @ContinuousOn _ _ _ instkification f C := fun C ↦ continuousOn_compact_to_kification C.2 f (conton C)
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

lemma continuous_kification_of_continuous {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] (f : X → Y) (cont : Continuous f) :
    @Continuous (kification X) (kification Y) instkification instkification f := by
  apply continuous_kification_of_continuousOn_compact
  intro C
  exact Continuous.continuousOn cont

-- I don't need this right now but this would be a nice property to have since it is very fundamental
lemma compacts_kification_eq_compacts {X : Type*} [t : TopologicalSpace X] (C : Set X) : IsCompact C  ↔ @IsCompact _ instkification C := by
  constructor
  · intro compact
    sorry
  · sorry

-- then show that this the kification is idempotent

--This is probably too complicated with the types but I feel like it would still be useful
/-
lemma instkification_instTopologicalSpaceSubstype_comm {X : Type*} [t : TopologicalSpace X] {p : Set X} (compact : IsCompact p) :
      @instTopologicalSpaceSubtype X p instkification = @instkification {x : X // p x} instTopologicalSpaceSubtype := by
  let C := Subtype.val '' (Set.univ : Set {x : X // p x})
  have compactC := Subtype.isCompact_iff.1 (@CompactSpace.isCompact_univ {x : X // p x} _ compact)
  rw [@TopologicalSpace.ext_iff]
  intro s
  unfold instTopologicalSpaceSubtype instkification TopologicalSpace.induced IsOpen
  simp
  constructor
  · intro ⟨u, hu, subtypeu⟩ B
    rcases hu ⟨Subtype.val '' B.1, Subtype.isCompact_iff.1 B.2⟩ with ⟨O, hO⟩
    simp at hO
    use ⟨Subtype.val ⁻¹' O.1, IsOpen.preimage continuous_subtype_val O.2⟩
    simp
    rw [← subtypeu]
    sorry
  · intro h
    use Subtype.val '' s
    simp [Function.Injective.preimage_image Subtype.val_injective]
    intro B
    rcases h ⟨(@Subtype.val X p) ⁻¹' B.1, aux B⟩ with ⟨U, hU⟩
    simp at hU
    sorry
-/

-- I think I might need some more properties here for example that the compact sets of the kification
-- are again the original compact sets
-- I think taking two times the k-ification should then be again the k-ification maybe?
