import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Fintype.Lattice

noncomputable section

/-Basic logic and set theory-/

-- needed in definition file
lemma biUnion_lt_eq_iUnion {X : Type*} (I : ℕ → Set X) :
    ⋃ (n : ℕ) (m : ℕ) (_ : m < n), I m  = ⋃ (n : ℕ), I n := by
  ext
  simp_rw [Set.mem_iUnion]
  exact ⟨fun ⟨_, m, _, mem⟩ ↦ ⟨m, mem⟩, fun ⟨n, mem⟩ ↦  ⟨n + 1, n, lt_add_one n, mem⟩⟩

-- needed in constructions file
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
lemma exists_iff_and_of_upwards_closed {L : Type*} [SemilatticeSup L] {P Q : L → Prop}
    (ucP : ∀ l : L, P l → ∀ m ≥ l, P m) (ucQ : ∀ l : L, Q l → ∀ m ≥ l, Q m):
    (∃ i, P i ∧ Q i) ↔ (∃ i, P i) ∧ ∃ i, Q i :=
  ⟨fun ⟨i, hP, hQ⟩ ↦ ⟨⟨i, hP⟩, ⟨i, hQ⟩⟩, fun ⟨⟨i, hP⟩, ⟨j, hQ⟩⟩ ↦
    ⟨i ⊔ j, ucP i hP (i ⊔ j) (le_sup_left), ucQ j hQ (i ⊔ j) (le_sup_right)⟩⟩

/-ENat-/

-- needed in definition file
lemma ENat.add_one_pos {n : ℕ∞} : 0 < n + 1 := by
  rw [← ENat.one_le_iff_pos]
  exact le_add_self

-- needed in definition file
lemma ENat.add_coe_lt_add_coe_right {n m : ℕ∞} {k : ℕ} : n + k < m + k ↔ n < m := by
  cases' n with n
  · simp
  cases' m with m
  · norm_cast; simp [ENat.coe_lt_top, -Nat.cast_add]
  · norm_cast; simp_all

/- Different types of maps -/

-- needed in this file and in examples file
def PartialEquiv.const {X Y : Type*} (x : X) (y : Y) : PartialEquiv X Y where
  toFun := Function.const X y
  invFun := Function.const Y x
  source := {x}
  target := {y}
  map_source' := fun _ _ ↦ by rfl
  map_target' := fun _ _ ↦ by rfl
  left_inv' := fun x' x'mem  ↦ by rw [Set.eq_of_mem_singleton x'mem]; rfl
  right_inv' := fun y' y'mem ↦ by rw [Set.eq_of_mem_singleton y'mem]; rfl

-- needed in this file
def IsometryEquiv.piCongrLeftofFintype' {ι ι' : Type*} [Fintype ι] [Fintype ι'] {Y : ι → Type*}
    [∀ j, PseudoEMetricSpace (Y j)]
    (e : ι ≃ ι') : (∀ i, Y i) ≃ᵢ ∀ j, Y (e.symm j) := IsometryEquiv.mk (Equiv.piCongrLeft' _ e)
  (by
    intro x1 x2
    simp_rw [PseudoEMetricSpace.toEDist, pseudoEMetricSpacePi, instEDistForall,
      Finset.sup_univ_eq_iSup]
    exact (Equiv.iSup_comp (g := fun b ↦ edist (x1 b) (x2 b)) e.symm))

-- needed in this file
def IsometryEquiv.piCongrLeftofFintype {ι ι' : Type*} [Fintype ι] [Fintype ι'] {Y : ι' → Type*}
    [∀ j, PseudoEMetricSpace (Y j)]
    (e : ι ≃ ι') : (∀ i, Y (e i)) ≃ᵢ ∀ j, Y j := (piCongrLeftofFintype' e.symm).symm

-- needed in this file
def IsometryEquiv.congrLeftofFintype {ι ι' X : Type*} [Fintype ι] [Fintype ι']
    [PseudoEMetricSpace X] (e : ι ≃ ι') : (ι → X) ≃ᵢ (ι' → X) :=
  piCongrLeftofFintype (Y := fun _ ↦ X) e

-- needed in this file
def IsometryEquiv.sumArrowEquivProdArrowofFintype (α β γ : Type*) [Fintype α] [Fintype β]
    [PseudoEMetricSpace γ] : (α ⊕ β → γ) ≃ᵢ (α → γ) × (β → γ) :=
  mk (Equiv.sumArrowEquivProdArrow _ _ _) (by
    intro f1 f2
    simp_rw [PseudoEMetricSpace.toEDist, Prod.pseudoEMetricSpaceMax, pseudoEMetricSpacePi,
      instEDistForall, Finset.sup_univ_eq_iSup, iSup_sum]
    rfl)

-- needed in product file
def IsometryEquiv.finArrowProdHomeomorphFinAddArrow {X : Type*} [PseudoEMetricSpace X] (m n : ℕ) :
    (Fin m → X) × (Fin n → X) ≃ᵢ (Fin (m + n) → X) :=
  (sumArrowEquivProdArrowofFintype _ _ _).symm.trans (congrLeftofFintype finSumFinEquiv)


/- Topology -/

-- needed in examples file
lemma closedBall_zero_dim_singleton {X : Type*} {h : PseudoMetricSpace (Fin 0 → X)} :
    (Metric.closedBall ![] 1 : Set (Fin 0 → X)) = {![]} := by
  ext
  simp only [Matrix.empty_eq, Metric.mem_closedBall, dist_self, zero_le_one, Set.mem_singleton_iff]

-- needed in definition file and examples file
lemma sphere_zero_dim_empty {X : Type*} {h : PseudoMetricSpace (Fin 0 → X)} :
    (Metric.sphere ![] 1 : Set (Fin 0 → X)) = ∅ := by
  simp only [Metric.sphere, Matrix.empty_eq, dist_self, zero_ne_one, Set.setOf_false]

-- needed in kification file
lemma open_in_iff_compl_closed_in {X : Type*} [TopologicalSpace X] (A B : Set X) :
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
    [TopologicalSpace γ] {g : β → γ} {f : α → β} {s : Set α} (cont : Continuous f)
    (conton : ContinuousOn g (f '' s)) : ContinuousOn (g ∘ f) s :=
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

/- Lemmas that I am not using but relate to things I have defined above -/

lemma PartialEquiv.const_continuousOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) : ContinuousOn (PartialEquiv.const x y) {x}
  := continuousOn_singleton (PartialEquiv.const x y) x

def Equiv.finArrowProdEQuivFinAddArrow {X : Type*} (m n : ℕ) :
    (Fin m → X) × (Fin n → X) ≃ (Fin (m + n) → X) :=
  (sumArrowEquivProdArrow _ _ _).symm.trans (finSumFinEquiv.arrowCongr (Equiv.refl _))

def Homeomorph.sumArrowEquivProdArrow {ι ι' X: Type*} [TopologicalSpace X]:
    (ι ⊕ ι' → X) ≃ₜ (ι → X) × (ι' → X)  where
  toEquiv := Equiv.sumArrowEquivProdArrow _ _ _
  continuous_toFun := by
    simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_mk, continuous_prod_mk]
    continuity
  continuous_invFun := continuous_pi fun i ↦ match i with
    | .inl i => by apply (continuous_apply _).comp' continuous_fst
    | .inr i => by apply (continuous_apply _).comp' continuous_snd

def Homeomorph.congrLeft {ι ι' X : Type*} [TopologicalSpace X] (e : ι ≃ ι') :
    (ι → X) ≃ₜ (ι' → X) :=
  piCongrLeft (Y := fun _ ↦ X) e

def Homeomorph.finArrowProdHomeomorphFinAddArrow {X: Type*} [TopologicalSpace X] (m n : ℕ) :
    (Fin m → X) × (Fin n → X) ≃ₜ (Fin (m + n) → X) :=
  (sumArrowEquivProdArrow).symm.trans (congrLeft finSumFinEquiv)
