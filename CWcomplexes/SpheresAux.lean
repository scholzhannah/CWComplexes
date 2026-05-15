module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Inv
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import CWcomplexes.Auxiliary
public import CWcomplexes.RelConstructions
public import Mathlib.Data.Fin.Tuple.Take
public import CWcomplexes.PartialHomeomorph.Constructions

@[expose] public noncomputable section

open Metric Set

/-
Do this for Lp-spaces in general (maybe it exists there?)
-/

open Classical in
@[simps]
def Function.Embedding.toPartialEquiv {α β : Type*} [Inhabited α] (f : α ↪ β) :
    PartialEquiv α β where
  toFun := f
  invFun y := if h : y ∈ range f then choose (mem_range.1 h) else default
      -- replace by Function.invFun
  source := univ
  target := range f
  map_source' x _ := mem_range_self x
  map_target' y _ := mem_univ y
  left_inv' x _ := by simp
  right_inv' y hy := by simp [hy, choose_spec (mem_range.1 hy)]

@[simps!]
def PartialEquiv.transEmbedding {α β γ : Type*} [Inhabited β] (e : PartialEquiv α β) (f : β ↪ γ) :
    PartialEquiv α γ :=
  (e.trans f.toPartialEquiv)

@[simp]
theorem PartialEquiv.coe_transEmbedding {α β γ : Type*} [Inhabited β] (e : PartialEquiv α β)
    (f : β ↪ γ) : (e.transEmbedding f : α → γ) = f ∘ e :=
  rfl

open Function in
lemma Pi.injective_compRightL_of_injective(R : Type*) [Semiring R] {ι : Type*} (φ : ι → Type*)
    [(i : ι) → TopologicalSpace (φ i)] [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]
    {α : Type*} (f : α → ι) (h : Surjective f) : Injective (Pi.compRightL R φ f) := by
  intro a b
  simp_rw [funext_iff]
  intro h' x
  obtain ⟨y, rfl⟩ := h x
  exact h' y

@[simps!]
def PiLp.compRightL (p : ENNReal) (𝕜 : Type*) [SeminormedRing 𝕜] {ι κ : Type*}
    (β : κ → Type*) (f : ι → κ) [(i : ι) → SeminormedAddCommGroup (β (f i))]
    [(i : ι) → Module 𝕜 (β (f i))]
    [(i : κ) → SeminormedAddCommGroup (β i)] [(i : κ) → Module 𝕜 (β i)] :
    PiLp p β →L[𝕜] PiLp p (fun i ↦ β (f i)) :=
  ((continuousLinearEquiv p 𝕜 (fun i ↦ β (f i))).symm.toContinuousLinearMap).comp
    ((Pi.compRightL 𝕜 β f).comp (continuousLinearEquiv p 𝕜 β).toContinuousLinearMap)

open Function in
lemma PiLp.injective_compRightL_of_injective (p : ENNReal) (𝕜 : Type*) [SeminormedRing 𝕜]
    {ι κ : Type*} (β : κ → Type*) (f : ι → κ) [(i : ι) → SeminormedAddCommGroup (β (f i))]
    [(i : ι) → Module 𝕜 (β (f i))]
    [(i : κ) → SeminormedAddCommGroup (β i)] [(i : κ) → Module 𝕜 (β i)] (h : Surjective f) :
    Injective (compRightL p 𝕜 β f) := by
  simp only [compRightL, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
    EmbeddingLike.comp_injective, EquivLike.injective_comp]
  exact Pi.injective_compRightL_of_injective 𝕜 β f h

def EuclideanSpace.compRightL (𝕜 : Type*) [SeminormedRing 𝕜] {n m : Type*} (f : m → n) :
    EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 m :=
  PiLp.compRightL 2 𝕜 (fun _ ↦ 𝕜) f

open Classical in
@[simps]
def Function.Embedding.euclidean (𝕜 : Type*) {n m : Type*} [Inhabited 𝕜] (f : n ↪ m) :
    EuclideanSpace 𝕜 n ↪ EuclideanSpace 𝕜 m where
  toFun s := WithLp.toLp 2 fun i ↦  if h : i ∈ range f then s (choose (mem_range.1 h)) else default
  inj' s1 s2 h := by
    ext i
    rw [PiLp.ext_iff] at h
    specialize h (f i)
    simp only [mem_range, EmbeddingLike.apply_eq_iff_eq, exists_eq, ↓reduceDIte, choose_eq] at h
    have := choose_spec (p := fun x ↦ f x = f i) (mem_range.mp (mem_range_self i))
    apply f.injective at this
    exact this ▸ h

lemma h {𝕜 n m : Type*} [Inhabited 𝕜] {f : n ↪ m} {i : n} {s : EuclideanSpace 𝕜 n} :
    f.euclidean 𝕜 s (f i) = s i := by
  simp only [f.euclidean_apply_ofLp 𝕜, mem_range_self i, ↓reduceDIte]
  have := Classical.choose_spec (p := fun x ↦ f x = f i) (mem_range.1 (mem_range_self i))
  rw [f.injective.eq_iff.1 this]

abbrev Hyperplane (n m : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i (h1 : i ≥  m) (h2 : i < n), x ⟨i, by simp [h2]⟩ = 0}

example (n m : ℕ) : range ((Fin.castAddEmb m).euclidean ℝ) = Hyperplane (n + m) n := by
  apply subset_antisymm
  · intro x
    simp only [mem_range, mem_setOf_eq, ge_iff_le, forall_exists_index]
    intro y hyx i hi1 hi2
    rw [← hyx]
    have : (⟨i, hi2⟩ : Fin (n + m)) ∉ range (Fin.castAddEmb m) := sorry
    simp only [Function.Embedding.euclidean, Function.Embedding.coeFn_mk, this,↓reduceDIte]
    rfl
  · intro x hx
    simp only [mem_setOf_eq, ge_iff_le] at hx

    sorry

example (n m : ℕ) : EuclideanSpace ℝ (Fin n) ↪ EuclideanSpace ℝ (Fin (n + m)) :=
  (Fin.castAddEmb m).euclidean ℝ
