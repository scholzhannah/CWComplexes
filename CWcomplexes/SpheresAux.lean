import Mathlib.Analysis.NormedSpace.HomeomorphBall
import Mathlib.Geometry.Manifold.Instances.Sphere
import CWcomplexes.Auxiliary
import CWcomplexes.RelConstructions
import Mathlib.Data.Fin.Tuple.Take

noncomputable section

open Metric Set

open Classical in
def Function.Embedding.toPartialEquiv (α β : Type*) [Inhabited α] (f : α ↪ β) :
    PartialEquiv α β where
  toFun := f
  invFun y := if h : y ∈ range f then choose (mem_range.1 h) else default
  source := univ
  target := range f
  map_source' x _ := mem_range_self x
  map_target' y _ := mem_univ y
  left_inv' x _ := by simp
  right_inv' y hy := by simp [hy, choose_spec (mem_range.1 hy)]
