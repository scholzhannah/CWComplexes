import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Abstract.Basic

noncomputable section

open Set HomotopicalAlgebra

universe v

variable {X : Type v} [TopologicalSpace X] (C D : Set X) [Topology.RelCWComplex C D]


def test.{u} (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) :
    TopCat.of X ≅ TopCat.of Y := by
  exact TopCat.isoOfHomeo h

#check TopCat.isColimitCoconeOfForget

def direction1: TopCat.RelativeCWComplex.{v} (X := TopCat.of D) (Y := TopCat.of C)
    (TopCat.ofHom (ContinuousMap.inclusion Topology.RelCWComplex.base_subset_complex)) :=
  let F : CategoryTheory.Functor ℕ TopCat.{v} := {
    obj n := TopCat.of (Topology.RelCWComplex.skeletonLT C n)
    map h := TopCat.ofHom (ContinuousMap.inclusion (Topology.RelCWComplex.skeletonLT_mono
        (by
          rw [ENat.coe_le_coe]
          exact h.le)))
  }
  { F := F
    isoBot := TopCat.isoOfHomeo (Homeomorph.setCongr Topology.RelCWComplex.skeletonLT_zero_eq_base)
    --isWellOrderContinuous := {nonempty_isColimit := by simp}
    incl := {
      app n :=
        (TopCat.ofHom (ContinuousMap.inclusion Topology.RelCWComplex.skeletonLT_subset_complex))
    }
    isColimit :=
      { desc s := sorry }
      /-
      let c : CategoryTheory.Limits.Cocone (F.comp (CategoryTheory.forget TopCat)) := {
        pt := C
        ι := { app := fun n ↦
          CategoryTheory.asHom (inclusion Topology.RelCWComplex.skeletonLT_subset_complex)}
      }
      apply CategoryTheory.Limits.IsColimit.ofIsoColimit (r := TopCat.coconeOfCoconeForget c)
      · apply TopCat.isColimitCoconeOfForget
        sorry
      · sorry
        /-apply CategoryTheory.eqToIso
        --unfold TopCat.coconeOfCoconeForget
        rw [CategoryTheory.Limits.Cocone.mk.injEq]
        simp
        sorry-/
      -/
    attachCells n hn := {
      ι := Topology.RelCWComplex.cell C n.succ
      π i := ()
      cofan₁ := CategoryTheory.Limits.Cofan.mk sorry sorry
      cofan₂ := sorry
      isColimit₁ := sorry
      isColimit₂ := sorry
      m := sorry
      hm := sorry
      g₁ := sorry
      g₂ := sorry
      isPushout := sorry
    } }

  /-
  {
    F := {
      obj n := TopCat.of (Topology.RelCWComplex.skeletonLT C n)
      map h := TopCat.ofHom (ContinuousMap.inclusion (Topology.RelCWComplex.skeletonLT_mono
        (by
          rw [ENat.coe_le_coe]
          exact h.le)))}
    isoBot :=
      TopCat.isoOfHomeo (Homeomorph.setCongr Topology.RelCWComplex.skeletonLT_zero_eq_base)
    isWellOrderContinuous := {nonempty_isColimit := by simp}
    incl := {
      app n :=
        (TopCat.ofHom (ContinuousMap.inclusion Topology.RelCWComplex.skeletonLT_subset_complex))
    }
  isColimit := by
    let c : CategoryTheory.Limits.Cocone ((F : CategoryTheory.Functor ℕ TopCat).comp (CategoryTheory.forget TopCat)) := sorry

    have := TopCat.isColimitCoconeOfForget
    simp
    sorry
  fac := sorry
  attachCells := sorry
  }
-/
