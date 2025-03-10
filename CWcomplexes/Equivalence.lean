import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Abstract.Basic

open Set

variable {X : Type*} [TopologicalSpace X] (C D : Set X) [Topology.RelCWComplex C D]

def direction1 : TopCat.RelativeCWComplex (X := TopCat.of D) (Y := TopCat.of C) sorry := sorry
