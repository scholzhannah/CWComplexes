import Mathlib.Analysis.NormedSpace.HomeomorphBall
import Mathlib.Geometry.Manifold.Instances.Sphere
import CWcomplexes.Auxiliary
import CWcomplexes.RelConstructions
import Mathlib.Data.Fin.Tuple.Take

noncomputable section

open Metric Set

open Classical in
@[simps]
def Function.Embedding.toPartialEquiv {α β : Type*} [Inhabited α] (f : α ↪ β) :
    PartialEquiv α β where
  toFun := f
  invFun y := if h : y ∈ range f then choose (mem_range.1 h) else default
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
  sorry

abbrev Hyperplane (n m : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i (h1 : i ≥  m) (h2 : i < n), x ⟨i, by simp [h2]⟩ = 0}

example (n m : ℕ) : range ((Fin.castAddEmb m).euclidean ℝ)= Hyperplane (n + m) n := by
  apply subset_antisymm
  · intro x
    simp only [mem_range, mem_setOf_eq, ge_iff_le, forall_exists_index]
    intro y hyx i hi1 hi2
    rw [← hyx]
    have : (⟨i, hi2⟩ : Fin (n + m)) ∉ range (Fin.castAddEmb m) := sorry
    simp only [Function.Embedding.euclidean, Function.Embedding.coeFn_mk, this,↓reduceDIte]
    sorry
  · sorry

example (n m : ℕ) :  EuclideanSpace ℝ (Fin n) ↪ EuclideanSpace ℝ (Fin (n + m)) :=
  (Fin.castAddEmb m).euclidean ℝ
