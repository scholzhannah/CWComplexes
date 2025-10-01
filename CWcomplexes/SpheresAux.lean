import Mathlib.Analysis.NormedSpace.HomeomorphBall
import Mathlib.Geometry.Manifold.Instances.Sphere
import CWcomplexes.Auxiliary
import CWcomplexes.RelConstructions
import Mathlib.Data.Fin.Tuple.Take

noncomputable section

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

-- Pi.compRightL
-- compose that with PiLp to get ContinuousLinearMap
-- PiLp.proj

variable (𝕜 : Type*) {n m : Type*} [TopologicalSpace 𝕜]  [SeminormedAddCommGroup 𝕜]

/-
#synth Module 𝕜 (EuclideanSpace 𝕜 n)

def test (𝕜 : Type*) {n m : Type*} [TopologicalSpace 𝕜] [SeminormedAddCommGroup 𝕜]  (f : m → n) :
    EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 m :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun (_ : m) ↦ ℝ)).symm.toContinuousLinearMap.comp
    ((Pi.compRightL ℝ (fun _ ↦ ℝ) f).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun (_ : n) ↦ ℝ)).toContinuousLinearMap)

def test' (𝕜 : Type*) {n m : Type*} [Semiring 𝕜] [TopologicalSpace 𝕜] (f : m → n) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun (_ : m) ↦ ℝ)).symm.toContinuousLinearMap.comp
    ((Pi.compRightL ℝ (fun _ ↦ ℝ) f).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun (_ : n) ↦ ℝ)).toContinuousLinearMap)

  --(PiLp.continuousLinearEquiv _ _ _).trans ((Pi.compRightL ℝ _ _ _ f).trans
-- (PiLp.continuousLinearEquiv _ _ _).symm)
-/
open Classical in
@[simps]
def Function.Embedding.euclidean (𝕜 : Type*) {n m : Type*} [Inhabited 𝕜] (f : n ↪ m) :
    EuclideanSpace 𝕜 n ↪ EuclideanSpace 𝕜 m where
  toFun s i := if h : i ∈ range f then s (choose (mem_range.1 h)) else default
  inj' s1 s2 h := by
    ext i
    rw [PiLp.ext_iff] at h
    specialize h (f i)
    simp at h
    change s1 (choose (mem_range.mp (mem_range_self i))) =
      s2 (choose (mem_range.mp (mem_range_self i))) at h
    have := choose_spec (p := fun x ↦ f x = f i) (mem_range.mp (mem_range_self i))
    apply f.injective at this
    exact this ▸ h

lemma h {𝕜 n m : Type*} [Inhabited 𝕜] {f : n ↪ m} {i : n} {s : EuclideanSpace 𝕜 n} :
    f.euclidean 𝕜 s (f i) = s i := by
  simp only [f.euclidean_apply 𝕜, mem_range_self i, ↓reduceDIte]
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

example (n m : ℕ) :  EuclideanSpace ℝ (Fin n) ↪ EuclideanSpace ℝ (Fin (n + m)) :=
  (Fin.castAddEmb m).euclidean ℝ
