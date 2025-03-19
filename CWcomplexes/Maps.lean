import CWcomplexes.Basic

open Metric Set Function

namespace Topology.RelCWComplex

section CellularMap

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]

/-- A cellular map is a map between two CW complexes `C` and `E` that respects the skeletal
structure: Sending the `n`-skelton of `C` to the `n`-skeleton of `E` for every `n : ℕ`. -/
structure CellularMap (C : Set X) {D : Set X} [RelCWComplex C D] (E : Set Y) {F : Set Y}
    [RelCWComplex E F] where
  /-- The underlying function. -/
  protected toFun : X → Y
  /-- `toFun` is continuous on the domain of the CW complex `C`. Use `CellularMap.continuousOn`
  instead. -/
  protected continuousOn_toFun : ContinuousOn toFun C
  /-- `toFun` sends the `n`-skeleton of the CW complex `C` to the `n`-skeleton of the CW complex
  `E`. Use `CellularMap.image_skeletonLT_subset` instead. -/
  image_skeletonLT_subset' (n : ℕ) : toFun '' (skeletonLT C n) ⊆ skeletonLT E n

namespace CellularMap

variable {C D : Set X} [RelCWComplex C D] {E F : Set Y} [RelCWComplex E F]

instance instFunLike : FunLike (CellularMap C E) X Y where
  coe := CellularMap.toFun
  coe_injective' f g h := by cases f; cases g; congr

lemma continuousOn (f : CellularMap C E) : ContinuousOn f C := f.continuousOn_toFun

@[ext]
theorem ext {f g : CellularMap C E} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `ContinuousMap` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : CellularMap C E) (f' : X → Y) (h : f' = f) : CellularMap C E where
  toFun := f'
  continuousOn_toFun := h.symm ▸ f.continuousOn_toFun
  image_skeletonLT_subset' n := h.symm ▸ f.image_skeletonLT_subset' n

@[simp] lemma coe_copy (f : CellularMap C E) (f' : X → Y) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl

lemma copy_eq (f : CellularMap C E) (f' : X → Y) (h : f' = f) : f.copy f' h = f := DFunLike.ext' h

/-- The identitiy is a cellular map. -/
protected def id (C : Set X) {D : Set X} [RelCWComplex C D] : CellularMap C C where
  toFun := _root_.id
  continuousOn_toFun := continuous_id.continuousOn
  image_skeletonLT_subset' n := by rw [image_id]

@[simp, norm_cast] theorem coe_id : ⇑(CellularMap.id C) = id := rfl

@[simp] theorem id_apply (x : X) : CellularMap.id C x = x := rfl

lemma image_skeletonLT_subset (f : CellularMap C E) (n : ℕ∞) :
    f '' (skeletonLT C n) ⊆ skeletonLT E n :=
  match n with
    | (m : ℕ) => f.image_skeletonLT_subset' m
    | ⊤ => by
      simp_rw [skeletonLT_top, image_subset_iff]
      intro x hx
      simp_rw [← iUnion_skeletonLT_eq_complex, mem_iUnion] at hx
      rw [mem_preimage]
      obtain ⟨n, hxn⟩ := hx
      apply skeletonLT_subset_complex
      exact f.image_skeletonLT_subset' n (mem_image_of_mem f hxn)

lemma image_skeleton_subset (f : CellularMap C E) (n : ℕ∞) : f '' (skeleton C n) ⊆ skeleton E n :=
  f.image_skeletonLT_subset _

def comp {Z : Type*} [TopologicalSpace Z] [T2Space Z] {G H : Set Z} [RelCWComplex G H]
    (f : CellularMap E G) (g : CellularMap C E) : CellularMap C G where
  toFun := f ∘ g
  continuousOn_toFun := by
    apply f.continuousOn.comp g.continuousOn
    simp_rw [Set.mapsTo', ← skeletonLT_top]
    exact g.image_skeletonLT_subset ⊤
  image_skeletonLT_subset' n := by
    rw [image_comp]
    exact (image_mono (image_skeletonLT_subset g n)).trans (image_skeletonLT_subset f n)

@[simp]
lemma coe_comp {Z : Type*} [TopologicalSpace Z] [T2Space Z] {G H : Set Z} [RelCWComplex G H]
    (f : CellularMap E G) (g : CellularMap C E) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
lemma comp_apply {Z : Type*} [TopologicalSpace Z] [T2Space Z] {G H : Set Z} [RelCWComplex G H]
    (f : CellularMap E G) (g : CellularMap C E) (x : X) : f.comp g x = f (g x) :=
  rfl

@[simp]
lemma comp_assoc {Z Z' : Type*} [TopologicalSpace Z] [T2Space Z] {G H : Set Z} [RelCWComplex G H]
    [TopologicalSpace Z'] [T2Space Z'] {I J : Set Z'} [RelCWComplex I J]
    (f : CellularMap G I) (g : CellularMap E G) (h : CellularMap C E) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
lemma id_comp (f : CellularMap C E) : (CellularMap.id _).comp f = f :=
  ext fun _ => rfl

@[simp]
lemma comp_id (f : CellularMap C E) : f.comp (CellularMap.id _) = f :=
  ext fun _ => rfl

@[simp]
lemma cancel_right {Z : Type*} [TopologicalSpace Z] [T2Space Z] {G H : Set Z} [RelCWComplex G H]
    {f₁ f₂ : CellularMap E G} {g : CellularMap C E} (hg : Surjective g) :
    f₁.comp g = f₂.comp g ↔ f₁ = f₂ :=
  ⟨fun h => ext <| hg.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (CellularMap.comp · g)⟩

@[simp]
lemma cancel_left {Z : Type*} [TopologicalSpace Z] [T2Space Z] {G H : Set Z} [RelCWComplex G H]
    {f : CellularMap E G} {g₁ g₂ : CellularMap C E} (hf : Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h => ext fun a => hf <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end CellularMap

end CellularMap

section CellularEquiv

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]

/-- A cellular equivalence between two CW complexes `C` and `D` is a partial equivalence with
source `C` and target `E` where the map itself and its inverse are cellular maps. -/
structure CellularEquiv (C : Set X) {D : Set X} [RelCWComplex C D] (E : Set Y) {F : Set Y}
    [RelCWComplex E F] extends PartialEquiv X Y where
  /-- `toPartial` is continuous on the domain of the CW complex `C`. Use
  `CellularEquiv.continuousOn` instead. -/
  continuousOn_toPartialEquiv : ContinuousOn toPartialEquiv C
  /-- `toPartialEquiv` sends the `n`-skeleton of the CW complex `C` to the `n`-skeleton of the CW
  complex`E`. -/
  image_topPartialEquiv_skeletonLT_subset' (n : ℕ) :
    toPartialEquiv '' (skeletonLT C n) ⊆ skeletonLT E n
  /-- `toPartialEquiv.symm` is continuous on the domain of the CW complex `E`.
  Use `CellularEquiv.continuousOn_symm` instead. -/
  continuousOn_toPartialEquiv_symm : ContinuousOn toPartialEquiv.symm E
  /-- `toPartialEquiv.symm` sends the `n`-skeleton of the CW complex `E` to the `n`-skeleton of the
  CW complex`C`. -/
  image_topPartialEquiv_symm_skeletonLT_subset' (n : ℕ) :
    toPartialEquiv.symm '' (skeletonLT E n) ⊆ skeletonLT C n
  /-- The source of `toPartialEquiv` is `C`. -/
  source_eq : toPartialEquiv.source = C
  /-- The target of `toPartialEquiv` is `E`. -/
  target_eq : toPartialEquiv.target = E

namespace CellularEquiv

variable {C D : Set X} [RelCWComplex C D] {E F : Set Y} [RelCWComplex E F] (e : CellularEquiv C E)

/-- Coercion of a `CellularEquiv` to function. Note that a `CellularEquiv` is not `DFunLike`. -/
instance : CoeFun (CellularEquiv C E) fun _ => X → Y :=
  ⟨fun e => e.toFun⟩

/-- Coercion of a cellular equivalence to a cellular map. -/
instance : Coe (CellularEquiv C E) (CellularMap C E) :=
  ⟨fun e => ⟨e.toFun, e.continuousOn_toPartialEquiv, e.image_topPartialEquiv_skeletonLT_subset'⟩⟩

/-- The inverse of a cellular equivalence  -/
@[symm]
protected def symm : CellularEquiv E C where
  toPartialEquiv := e.toPartialEquiv.symm
  continuousOn_toPartialEquiv := e.continuousOn_toPartialEquiv_symm
  image_topPartialEquiv_skeletonLT_subset' n := e.image_topPartialEquiv_symm_skeletonLT_subset' n
  continuousOn_toPartialEquiv_symm := e.continuousOn_toPartialEquiv
  image_topPartialEquiv_symm_skeletonLT_subset' n := e.image_topPartialEquiv_skeletonLT_subset' n
  source_eq := e.target_eq
  target_eq := e.source_eq

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (e : CellularEquiv C E) : X → Y := e

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : CellularEquiv C E) : Y → X := e.symm

initialize_simps_projections CellularEquiv (toFun → apply, invFun → symm_apply)

lemma continuousOn : ContinuousOn e C := e.continuousOn_toPartialEquiv

lemma continuousOn_symm : ContinuousOn e.symm E := e.continuousOn_toPartialEquiv_symm

@[simp]
lemma mk_coe (e : PartialEquiv X Y) (a b c d f g) :
    (CellularEquiv.mk e (C := C) (E := E) a b c d f g : X → Y) = e :=
  rfl

@[simp]
lemma mk_coe_symm (e : PartialEquiv X Y) (a b c d f g) :
    ((CellularEquiv.mk e (C := C) (E := E) a b c d f g).symm : Y → X) = e.symm :=
  rfl

lemma toPartialEquiv_injective :
    Injective (toPartialEquiv : CellularEquiv C E → PartialEquiv X Y)
  | ⟨_, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _⟩, rfl => rfl

@[simp] lemma toFun_eq_coe : e.toFun = e := rfl

@[simp] lemma invFun_eq_coe : e.invFun = e.symm := rfl

@[simp] lemma coe_coe : (e.toPartialEquiv : X → Y) = e := rfl

@[simp] lemma coe_coe_symm : (e.toPartialEquiv.symm : Y → X) = e.symm := rfl

@[simp] lemma map_source {x : X} (h : x ∈ e.source) : e x ∈ e.target := e.map_source' h

/-- Variant of `map_source`, stated for images of subsets of `source`. -/
lemma map_source'' : e '' e.source ⊆ e.target :=
  fun _ ⟨_, hx, hex⟩ ↦ mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

@[simp] lemma map_target {x : Y} (h : x ∈ e.target) : e.symm x ∈ e.source := e.map_target' h

@[simp] lemma left_inv {x : X} (h : x ∈ e.source) : e.symm (e x) = x := e.left_inv' h

@[simp] lemma right_inv {x : Y} (h : x ∈ e.target) : e (e.symm x) = x := e.right_inv' h

lemma eq_symm_apply {x : X} {y : Y} (hx : x ∈ e.source) (hy : y ∈ e.target) :
    x = e.symm y ↔ e x = y :=
  e.toPartialEquiv.eq_symm_apply hx hy

protected lemma mapsTo : MapsTo e e.source e.target := fun _ => e.map_source

protected lemma symm_mapsTo : MapsTo e.symm e.target e.source := e.symm.mapsTo

protected lemma leftInvOn : LeftInvOn e.symm e e.source := fun _ => e.left_inv

protected lemma rightInvOn : RightInvOn e.symm e e.target := fun _ => e.right_inv

protected lemma invOn : InvOn e.symm e e.source e.target := ⟨e.leftInvOn, e.rightInvOn⟩

protected lemma injOn : InjOn e e.source := e.leftInvOn.injOn

protected lemma bijOn : BijOn e e.source e.target := e.invOn.bijOn e.mapsTo e.symm_mapsTo

protected lemma surjOn : SurjOn e e.source e.target := e.bijOn.surjOn

/-- Replace `toPartialEquiv` field to provide better definitional equalities. -/
def replaceEquiv (e : CellularEquiv C E) (e' : PartialEquiv X Y) (h : e.toPartialEquiv = e') :
    CellularEquiv C E where
  toPartialEquiv := e'
  continuousOn_toPartialEquiv := h ▸ e.continuousOn_toPartialEquiv
  image_topPartialEquiv_skeletonLT_subset' := h ▸ e.image_topPartialEquiv_skeletonLT_subset'
  continuousOn_toPartialEquiv_symm := h ▸ e.continuousOn_toPartialEquiv_symm
  image_topPartialEquiv_symm_skeletonLT_subset' :=
    h ▸ e.image_topPartialEquiv_symm_skeletonLT_subset'
  source_eq := h ▸ e.source_eq
  target_eq := h ▸ e.target_eq

lemma replaceEquiv_eq_self (e' : PartialEquiv X Y)
    (h : e.toPartialEquiv = e') : e.replaceEquiv e' h = e := by
  cases e
  subst e'
  rfl

lemma source_preimage_target : e.source ⊆ e ⁻¹' e.target := e.mapsTo

/-- Two partial homeomorphisms are equal when they have equal `toFun`, `invFun` and `source`.
It is not sufficient to have equal `toFun` and `source`, as this only determines `invFun` on
the target. -/
@[ext]
protected theorem ext (e' : CellularEquiv C E) (h : ∀ x, e x = e' x)
    (hinv : ∀ x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' :=
  toPartialEquiv_injective (PartialEquiv.ext h hinv hs)

@[simp] lemma symm_toPartialEquiv : e.symm.toPartialEquiv = e.toPartialEquiv.symm := rfl

-- The following lemmas are already simp via `PartialEquiv`
lemma symm_source : e.symm.source = e.target := rfl

lemma symm_target : e.symm.target = e.source := rfl

@[simp] lemma symm_symm : e.symm.symm = e := rfl

lemma symm_bijective : Function.Bijective
    (CellularEquiv.symm : CellularEquiv C E → CellularEquiv E C) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

section IsImage

/-!
### `CellularEquiv.IsImage` relation

We say that `t : Set Y` is an image of `s : Set X` under a cellular equivalence `e` if any of the
following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).

This definition is a restatement of `PartialEquiv.IsImage` for cellular equivalences.
In this section we transfer API about `PartialEquiv.IsImage` to cellular equivalences.
-/

/-- We say that `t : Set Y` is an image of `s : Set X` under a partial homeomorphism `e`
if any of the following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
-/
def IsImage (s : Set X) (t : Set Y) : Prop :=
  ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)

namespace IsImage

variable {e} {s : Set X} {t : Set Y} {x : X} {y : Y}

lemma toPartialEquiv (h : e.IsImage s t) : e.toPartialEquiv.IsImage s t := h

lemma apply_mem_iff (h : e.IsImage s t) (hx : x ∈ e.source) : e x ∈ t ↔ x ∈ s :=
  h hx

protected lemma symm (h : e.IsImage s t) : e.symm.IsImage t s := h.toPartialEquiv.symm

lemma symm_apply_mem_iff (h : e.IsImage s t) (hy : y ∈ e.target) : e.symm y ∈ s ↔ y ∈ t := h.symm hy

@[simp] lemma symm_iff : e.symm.IsImage t s ↔ e.IsImage s t := ⟨fun h => h.symm, fun h => h.symm⟩

protected lemma mapsTo (h : e.IsImage s t) : MapsTo e (e.source ∩ s) (e.target ∩ t) :=
  h.toPartialEquiv.mapsTo

lemma symm_mapsTo (h : e.IsImage s t) : MapsTo e.symm (e.target ∩ t) (e.source ∩ s) := h.symm.mapsTo

lemma image_eq (h : e.IsImage s t) : e '' (e.source ∩ s) = e.target ∩ t :=
  h.toPartialEquiv.image_eq

lemma symm_image_eq (h : e.IsImage s t) : e.symm '' (e.target ∩ t) = e.source ∩ s := h.symm.image_eq

lemma iff_preimage_eq : e.IsImage s t ↔ e.source ∩ e ⁻¹' t = e.source ∩ s :=
  PartialEquiv.IsImage.iff_preimage_eq

alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq

lemma iff_symm_preimage_eq : e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' s = e.target ∩ t :=
  symm_iff.symm.trans iff_preimage_eq

alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq

-- **TODO** : Keep copying lemmas from PartialHomeomorph here!

end IsImage

end IsImage

end CellularEquiv

end CellularEquiv

end Topology.RelCWComplex
