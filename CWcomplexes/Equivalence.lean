import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Abstract.Basic

noncomputable section

open Set HomotopicalAlgebra

variable {X : Type*} [TopologicalSpace X] (C D : Set X) [Topology.RelCWComplex C D]

def direction1 : TopCat.RelativeCWComplex (X := TopCat.of D) (Y := TopCat.of C)
    (TopCat.ofHom (ContinuousMap.inclusion Topology.RelCWComplex.base_subset_complex))where
  F := {
    obj n := TopCat.of (Topology.RelCWComplex.skeletonLT C n)
    map h := TopCat.ofHom (ContinuousMap.inclusion (Topology.RelCWComplex.skeletonLT_mono sorry))
    map_id := sorry
    map_comp := sorry
  }
  isoBot := sorry
  isWellOrderContinuous := sorry
  incl := sorry
  isColimit := sorry
  fac := sorry
  attachCells := sorry
