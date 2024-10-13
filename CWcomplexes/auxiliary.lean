import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Fintype.Lattice

/-!
# Auxiliary lemmas and definitions

In this file we have auxiliary lemmas that are not in mathlib but do not have any direct relation
to CW-complexes.
They are sorted by topics.
At the bottom of the file there are lemmas that are not used in this project but relate to
definitions and lemmas in this file.
-/

noncomputable section

/-! ### Basic logic and set theory-/

lemma biSup_lt_eq_iSup {X Y : Type*} [LT X] [NoMaxOrder X] (I : X → Set Y) :
    ⨆ (x : X) (x' < x), I x' = ⨆ x, I x := by
  apply le_antisymm
  · exact iSup_le fun _ ↦ iSup_le fun _ ↦ iSup_le fun _ ↦ le_iSup _ _
  · apply iSup_le (fun x ↦ ?_)
    obtain ⟨x', xlt⟩ := exists_gt x
    exact le_iSup_of_le x' (le_iSup_of_le x (le_iSup_of_le xlt (le_refl _)))

lemma biInf_lt_eq_iInf {X Y : Type*} [LT X] [NoMaxOrder X] (I : X → Set Y) :
    ⨅ (x : X) (x' < x), I x' = ⨅ x, I x := by
  apply le_antisymm
  · apply le_iInf (fun x ↦ ?_)
    obtain ⟨x', xlt⟩ := exists_gt x
    apply iInf_le_of_le x' (iInf_le_of_le x (iInf_le_of_le xlt (le_refl _)))
  · exact le_iInf fun _ ↦ le_iInf fun _ ↦ le_iInf fun _ ↦ iInf_le _ _

-- is this needed?
lemma biUnion_lt_eq_iUnion {X : Type*} (I : ℕ → Set X) :
  ⋃ (n : ℕ) (m < n), I m  = ⋃ (n : ℕ), I n := biSup_lt_eq_iSup _

-- is this needed?
lemma biInter_lt_eq_iInter {X : Type*} (I : ℕ → Set X) :
  ⋂ (n : ℕ) (m < n), I m  = ⋂ (n : ℕ), I n := biInf_lt_eq_iInf _

-- needed in constructions file
-- in mathlib
lemma Set.iUnion_sum {X Y Z: Type*} {f : X ⊕ Y → Set Z} :
    ⋃ x : X ⊕ Y, f x = (⋃ x : X, f (.inl x)) ∪ ⋃ x : Y, f (.inr x) := by
  ext; simp

--needed in this file
lemma inter_eq_inter_iff_compl {X : Type*} {A B C : Set X} : A ∩ B = C ∩ B ↔ Aᶜ ∩ B = Cᶜ ∩ B := by
  constructor <;> (intro; simp_all [Set.ext_iff, not_iff_not])

--needed in product file
lemma Set.subset_product {α β : Type*} {s : Set (α × β)} :
    s ⊆ (Prod.fst '' s) ×ˢ (Prod.snd '' s) :=
  fun _ hp ↦ mem_prod.2 ⟨mem_image_of_mem _ hp, mem_image_of_mem _ hp⟩

-- needed in product file
lemma exists_iff_and_of_monotone {L : Type*} [SemilatticeSup L] {P Q : L → Prop}
    (monP : Monotone P) (monQ : Monotone Q):
    (∃ i, P i ∧ Q i) ↔ (∃ i, P i) ∧ ∃ i, Q i :=
  ⟨fun ⟨i, hP, hQ⟩ ↦ ⟨⟨i, hP⟩, ⟨i, hQ⟩⟩,
    fun ⟨⟨i, hP⟩, ⟨j, hQ⟩⟩ ↦ ⟨i ⊔ j, ⟨monP le_sup_left hP,  monQ le_sup_right hQ⟩⟩⟩

/-! ### ENat-/

-- needed in definition file
lemma ENat.add_one_pos {n : ℕ∞} : 0 < n + 1 := by
  rw [← ENat.one_le_iff_pos]
  exact le_add_self

-- needed in definition file
lemma ENat.add_finite_lt_add_finite_right {n m k : ℕ∞} (ne : k ≠ ⊤) : n + k < m + k ↔ n < m := by
  cases' k with k
  · contradiction
  cases' n with n
  · simp
  cases' m with m
  · norm_cast; simp [ENat.coe_lt_top, -Nat.cast_add]
  · norm_cast; simp_all

/-! ### Different maps -/

-- needed in this file and in examples file
/-- `Function.const` as a `PartialEquiv`.
  It consists of two constant maps in opposite directions. -/
def PartialEquiv.single {X Y : Type*} (x : X) (y : Y) : PartialEquiv X Y where
  toFun := Function.const X y
  invFun := Function.const Y x
  source := {x}
  target := {y}
  map_source' := fun _ _ ↦ by rfl
  map_target' := fun _ _ ↦ by rfl
  left_inv' := fun x' x'mem  ↦ by rw [Set.eq_of_mem_singleton x'mem]; rfl
  right_inv' := fun y' y'mem ↦ by rw [Set.eq_of_mem_singleton y'mem]; rfl

-- needed in this file
/-- `Equiv.piCongrLeft` as an `IsometryEquiv`: this is the natural
`∀ i, Y i ≃ᵢ ∀ j, Y (e.symm j)` obtained from a bijection `ι ≃ ι'` of finite types.-/
def IsometryEquiv.piCongrLeftofFintype' {ι ι' : Type*} [Fintype ι] [Fintype ι'] {Y : ι → Type*}
    [∀ j, PseudoEMetricSpace (Y j)]
    (e : ι ≃ ι') : (∀ i, Y i) ≃ᵢ ∀ j, Y (e.symm j) := IsometryEquiv.mk (Equiv.piCongrLeft' _ e)
  (by
    intro x1 x2
    simp_rw [PseudoEMetricSpace.toEDist, pseudoEMetricSpacePi, instEDistForall,
      Finset.sup_univ_eq_iSup]
    exact (Equiv.iSup_comp (g := fun b ↦ edist (x1 b) (x2 b)) e.symm))

-- needed in this file
/-- `Equiv.piCongrLeft` as an `IsometryEquiv`: this is the natural
`∀ i, Y (e i) ≃ᵢ ∀ j, Y j` obtained from a bijection `ι ≃ ι'` of finite types.-/
def IsometryEquiv.piCongrLeftofFintype {ι ι' : Type*} [Fintype ι] [Fintype ι'] {Y : ι' → Type*}
    [∀ j, PseudoEMetricSpace (Y j)]
    (e : ι ≃ ι') : (∀ i, Y (e i)) ≃ᵢ ∀ j, Y j := (piCongrLeftofFintype' e.symm).symm

-- needed in this file
/-- An equivalence `ι ≃ ι'` of finite types yields the `IsometryEquiv` `(ι → X) ≃ᵢ (ι' → X)`. -/
def IsometryEquiv.arrowCongrLeftofFintype {ι ι' X : Type*} [Fintype ι] [Fintype ι']
    [PseudoEMetricSpace X] (e : ι ≃ ι') : (ι → X) ≃ᵢ (ι' → X) :=
  piCongrLeftofFintype (Y := fun _ ↦ X) e

-- needed in this file
/-- `Equiv.sumArrowEquivProdArrow` as an `IsometryEquiv`.-/
def IsometryEquiv.sumArrowEquivProdArrowofFintype (α β γ : Type*) [Fintype α] [Fintype β]
    [PseudoEMetricSpace γ] : (α ⊕ β → γ) ≃ᵢ (α → γ) × (β → γ) :=
  mk (Equiv.sumArrowEquivProdArrow _ _ _) (by
    intro f1 f2
    simp_rw [PseudoEMetricSpace.toEDist, Prod.pseudoEMetricSpaceMax, pseudoEMetricSpacePi,
      instEDistForall, Finset.sup_univ_eq_iSup, iSup_sum]
    rfl)

-- needed in product file
/-- The natural `IsometryEquiv` between `(Fin m → X) × (Fin n → X)` and `(Fin (m + n) → X)`.-/
def IsometryEquiv.finArrowProdHomeomorphFinAddArrow {X : Type*} [PseudoEMetricSpace X] (m n : ℕ) :
    (Fin m → X) × (Fin n → X) ≃ᵢ (Fin (m + n) → X) :=
  (sumArrowEquivProdArrowofFintype _ _ _).symm.trans (arrowCongrLeftofFintype finSumFinEquiv)

/-! ### Topology -/

lemma closedBall_eq_singleton_of_unique {X : Type*} [Unique X] [PseudoMetricSpace X] {ε : ℝ}
    (h : 0 ≤ ε) : Metric.closedBall default ε = {default (α := X)} := by
  ext
  simp [Unique.eq_default, h]

-- needed because this cannot be done by a rewrite
-- needed in examples file
lemma closedBall_zero_dim_singleton {X : Type*} [PseudoMetricSpace (Fin 0 → X)] :
    (Metric.closedBall ![] 1 : Set (Fin 0 → X)) = {![]} :=
  closedBall_eq_singleton_of_unique zero_le_one

lemma sphere_eq_empty_of_unique {X : Type*} [Unique X] [PseudoMetricSpace X] {ε : ℝ} (h : 0 < ε) :
    (Metric.sphere default ε : Set X) = ∅ := by
  simp [Metric.sphere, Unique.eq_default, ne_of_lt h]

-- needed in definition file and examples file
lemma sphere_zero_dim_empty {X : Type*} {h : PseudoMetricSpace (Fin 0 → X)} :
    (Metric.sphere ![] 1 : Set (Fin 0 → X)) = ∅ := sphere_eq_empty_of_unique zero_lt_one

-- needed in kification file
/-- This lemma states that a set `A` is open in a set `B` iff `Aᶜ` is closed in `B`.-/
lemma open_in_iff_compl_closed_in {X : Type*} [TopologicalSpace X] {A B : Set X} :
    (∃ (C : Set X), IsOpen C ∧  A ∩ B = C ∩ B) ↔
    ∃ (C : Set X), IsClosed C ∧  Aᶜ ∩ B = C ∩ B := by
  constructor
  · intro ⟨C, openC, hC⟩
    use Cᶜ
    rw [inter_eq_inter_iff_compl, compl_compl, compl_compl]
    exact ⟨isClosed_compl_iff.2 openC, hC⟩
  · intro ⟨C, closedC, hC⟩
    use Cᶜ
    rw [inter_eq_inter_iff_compl, compl_compl]
    exact ⟨isOpen_compl_iff.2 closedC, hC⟩

-- needed in constructions file and product file
lemma ContinuousOn.image_comp_continuous {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] {g : β → γ} {f : α → β} {s : Set α} (conton : ContinuousOn g (f '' s))
    (cont : Continuous f) : ContinuousOn (g ∘ f) s :=
  conton.comp cont.continuousOn (s.mapsTo_image f)

-- needed in examples file
lemma affineHomeomorph_trans {𝕜 : Type*} [Field 𝕜] [NoZeroDivisors 𝕜] [TopologicalSpace 𝕜]
    [TopologicalRing 𝕜] (a b c d : 𝕜) (h1 : a ≠ 0) (h2 : c ≠ 0) :
    (affineHomeomorph a b h1).trans (affineHomeomorph c d h2) =
    affineHomeomorph (c * a) (c * b + d) (mul_ne_zero h2 h1)  := by
  ext
  simp_rw [Homeomorph.trans_apply, affineHomeomorph_apply]
  ring

-- needed in kification file
lemma T2Space.mono {X : Type*} {s t : TopologicalSpace X}
    (le : t ≤ s) [t2 : @T2Space X s] : @T2Space X t where
  t2 := by
    intro i j ne
    rw [t2Space_iff] at t2
    obtain ⟨u, v, openu, openv, huv⟩ := t2 ne
    exact ⟨u, v, le _ openu, le _ openv, huv⟩

/-! ### Lemmas that I am not using but relate to things I have defined above -/

/-- The natural `Equiv` between `(Fin m → X) × (Fin n → X)` and `(Fin (m + n) → X)`.-/
def Equiv.finArrowProdEQuivFinAddArrow {X : Type*} (m n : ℕ) :
    (Fin m → X) × (Fin n → X) ≃ (Fin (m + n) → X) :=
  (sumArrowEquivProdArrow _ _ _).symm.trans (finSumFinEquiv.arrowCongr (Equiv.refl _))

/-- `Equiv.sumArrowEquivProdArrow` as a homeomorphism. The natural homeomoorphism
`(ι ⊕ ι' → X) ≃ₜ (ι → X) × (ι' → X)` -/
def Homeomorph.sumArrowEquivProdArrow {ι ι' X: Type*} [TopologicalSpace X]:
    (ι ⊕ ι' → X) ≃ₜ (ι → X) × (ι' → X)  where
  toEquiv := Equiv.sumArrowEquivProdArrow _ _ _
  continuous_toFun := by
    simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_mk, continuous_prod_mk]
    continuity
  continuous_invFun := continuous_pi fun i ↦ match i with
    | .inl i => by apply (continuous_apply _).comp' continuous_fst
    | .inr i => by apply (continuous_apply _).comp' continuous_snd

/-- An equivalence `ι ≃ ι'` yields the homeomorphism `(ι → X) ≃ₜ (ι' → X)`.-/
def Homeomorph.arrowCongrLeft {ι ι' X : Type*} [TopologicalSpace X] (e : ι ≃ ι') :
    (ι → X) ≃ₜ (ι' → X) :=
  piCongrLeft (Y := fun _ ↦ X) e

/-- The natural homeomorphism between `(Fin m → X) × (Fin n → X)` and `(Fin (m + n) → X)`.-/
def Homeomorph.finArrowProdHomeomorphFinAddArrow {X: Type*} [TopologicalSpace X] (m n : ℕ) :
    (Fin m → X) × (Fin n → X) ≃ₜ (Fin (m + n) → X) :=
  (sumArrowEquivProdArrow).symm.trans (arrowCongrLeft finSumFinEquiv)
