import CWcomplexes.RelSubcomplex
import Mathlib.Topology.PartialHomeomorph
import Mathlib.Data.Setoid.Partition

noncomputable section

open Metric Set Function

namespace Topology

namespace RelCWComplex

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
    f '' skeletonLT C n ⊆ skeletonLT E n :=
  match n with
    | (m : ℕ) => f.image_skeletonLT_subset' m
    | ⊤ => by
      simp_rw [skeletonLT_top, image_subset_iff]
      intro x hx
      simp_rw [← iUnion_skeletonLT_eq_complex (C := C), mem_iUnion] at hx
      rw [mem_preimage]
      obtain ⟨n, hxn⟩ := hx
      apply skeletonLT_subset_complex
      exact f.image_skeletonLT_subset' n (mem_image_of_mem f hxn)

lemma image_skeleton_subset (f : CellularMap C E) (n : ℕ∞) : f '' skeleton C n ⊆ skeleton E n :=
  f.image_skeletonLT_subset _

def comp {Z : Type*} [TopologicalSpace Z] [T2Space Z] {G H : Set Z} [RelCWComplex G H]
    (f : CellularMap E G) (g : CellularMap C E) : CellularMap C G where
  toFun := f ∘ g
  continuousOn_toFun := by
    apply f.continuousOn.comp g.continuousOn
    simp_rw [Set.mapsTo', ← skeletonLT_top (C := C), ← skeletonLT_top (C := E)]
    -- make a lemma for the complex
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

def toCellularMap (e : CellularEquiv C E) : CellularMap C E where
  toFun := e
  continuousOn_toFun := e.continuousOn_toPartialEquiv
  image_skeletonLT_subset' := e.image_topPartialEquiv_skeletonLT_subset'

/-- Coercion of a cellular equivalence to a cellular map. -/
instance : Coe (CellularEquiv C E) (CellularMap C E) := ⟨fun e => e.toCellularMap⟩

/-- The inverse of a cellular equivalence -/
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

protected lemma continuousOn : ContinuousOn e C := e.continuousOn_toPartialEquiv

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

lemma image_eq_target_inter_inv_preimage {s : Set X} (h : s ⊆ e.source) :
    e '' s = e.target ∩ e.symm ⁻¹' s :=
  e.toPartialEquiv.image_eq_target_inter_inv_preimage h

/-- A version of `image_source_inter_eq` in which instead of the preimage of `s` the preimage of the
intersection of the source with `s` is considered. -/
lemma image_source_inter_eq' (s : Set X) : e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' s :=
  e.toPartialEquiv.image_source_inter_eq' s

lemma image_source_inter_eq (s : Set X) :
    e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' (e.source ∩ s) :=
  e.toPartialEquiv.image_source_inter_eq s

lemma symm_image_eq_source_inter_preimage {s : Set Y} (h : s ⊆ e.target) :
    e.symm '' s = e.source ∩ e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h

lemma symm_image_target_inter_eq (s : Set Y) :
    e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' (e.target ∩ s) :=
  e.symm.image_source_inter_eq _

lemma source_inter_preimage_inv_preimage (s : Set X) :
    e.source ∩ e ⁻¹' (e.symm ⁻¹' s) = e.source ∩ s :=
  e.toPartialEquiv.source_inter_preimage_inv_preimage s

lemma target_inter_inv_preimage_preimage (s : Set Y) :
    e.target ∩ e.symm ⁻¹' (e ⁻¹' s) = e.target ∩ s :=
  e.symm.source_inter_preimage_inv_preimage _

lemma source_inter_preimage_target_inter (s : Set Y) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.toPartialEquiv.source_inter_preimage_target_inter s

lemma image_source_eq_target : e '' e.source = e.target := e.toPartialEquiv.image_source_eq_target

lemma symm_image_target_eq_source : e.symm '' e.target = e.source := e.symm.image_source_eq_target

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

lemma apply_mem_iff (h : e.IsImage s t) (hx : x ∈ e.source) : e x ∈ t ↔ x ∈ s := h hx

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

/-- A version of `iff_symm_preimage_eq` in which instead of the preimage of `s` the preimage of the
intersection of the source with `s` is considered. -/
lemma iff_symm_preimage_eq' :
    e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' (e.source ∩ s) = e.target ∩ t := by
  rw [iff_symm_preimage_eq, ← image_source_inter_eq, ← image_source_inter_eq']

alias ⟨symm_preimage_eq', of_symm_preimage_eq'⟩ := iff_symm_preimage_eq'

/-- A version of `iff_preimage_eq` in which instead of the preimage of `t` the preimage of the
intersection of the target with `t` is considered. -/
lemma iff_preimage_eq' : e.IsImage s t ↔ e.source ∩ e ⁻¹' (e.target ∩ t) = e.source ∩ s :=
  symm_iff.symm.trans iff_symm_preimage_eq'

alias ⟨preimage_eq', of_preimage_eq'⟩ := iff_preimage_eq'

lemma of_image_eq (h : e '' (e.source ∩ s) = e.target ∩ t) : e.IsImage s t :=
  PartialEquiv.IsImage.of_image_eq h

lemma of_symm_image_eq (h : e.symm '' (e.target ∩ t) = e.source ∩ s) : e.IsImage s t :=
  PartialEquiv.IsImage.of_symm_image_eq h

protected lemma compl (h : e.IsImage s t) : e.IsImage sᶜ tᶜ := fun _ hx => (h hx).not

protected lemma inter {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∩ s') (t ∩ t') := fun _ hx => (h hx).and (h' hx)

protected lemma union {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∪ s') (t ∪ t') := fun _ hx => (h hx).or (h' hx)

protected lemma diff {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s \ s') (t \ t') :=
  h.inter h'.compl

lemma leftInvOn_piecewise {e' : CellularEquiv C E} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : e.IsImage s t) (h' : e'.IsImage s t) :
    LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source) :=
  h.toPartialEquiv.leftInvOn_piecewise h'

lemma inter_eq_of_inter_eq_of_eqOn {e' : CellularEquiv C E} (h : e.IsImage s t)
    (h' : e'.IsImage s t) (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    e.target ∩ t = e'.target ∩ t :=
  h.toPartialEquiv.inter_eq_of_inter_eq_of_eqOn h' hs Heq

lemma symm_eqOn_of_inter_eq_of_eqOn {e' : CellularEquiv C E} (h : e.IsImage s t)
    (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    EqOn e.symm e'.symm (e.target ∩ t) :=
  h.toPartialEquiv.symm_eq_on_of_inter_eq_of_eqOn hs Heq

/- **Note**: This is the first time I need anything more that CWComplexes.Basic. Maybe this should
be taken out and PR'd later?
-/

/-- Restrict a `PartialHomeomorph` to a pair of corresponding open sets. -/
@[simps toPartialEquiv]
def restr [T2Space X] [T2Space Y] (C' : Subcomplex C) (E' : Subcomplex E) (h : e.IsImage C' E') :
    CellularEquiv C' (D := D) E' (F := F) where
  toPartialEquiv := h.toPartialEquiv.restr
  continuousOn_toPartialEquiv := e.continuousOn.mono C'.subset_complex
  image_topPartialEquiv_skeletonLT_subset' n := by
    simp_rw [PartialEquiv.IsImage.restr_apply, Subcomplex.skeletonLT_eq]
    apply (image_inter_subset _ _ _).trans
    rw [← inter_eq_right.2 C'.subset_complex]
    simp_rw [← e.source_eq, h.image_eq, e.target_eq, inter_eq_right.2 E'.subset_complex]
    apply inter_subset_inter_right
    exact e.image_topPartialEquiv_skeletonLT_subset' n
  continuousOn_toPartialEquiv_symm := e.continuousOn_symm.mono E'.subset_complex
  image_topPartialEquiv_symm_skeletonLT_subset' n := by
    simp only [PartialEquiv.IsImage.restr_symm_apply, coe_coe_symm, symm_toPartialEquiv,
      Subcomplex.skeletonLT_eq]
    apply (image_inter_subset _ _ _).trans
    rw [← inter_eq_right.2 E'.subset_complex]
    simp_rw [← e.symm.source_eq, h.symm.image_eq, e.symm.target_eq,
      inter_eq_right.2 C'.subset_complex]
    apply inter_subset_inter_right
    exact e.symm.image_topPartialEquiv_skeletonLT_subset' n
  source_eq := by simp [e.source_eq, C'.subset_complex]
  target_eq := by simp [e.target_eq, E'.subset_complex]

end IsImage

lemma isImage_source_target : e.IsImage e.source e.target := e.toPartialEquiv.isImage_source_target

lemma isImage_source_target_of_disjoint (e' : CellularEquiv C E)
    (hs : Disjoint e.source e'.source) (ht : Disjoint e.target e'.target) :
    e.IsImage e'.source e'.target :=
  e.toPartialEquiv.isImage_source_target_of_disjoint e'.toPartialEquiv hs ht

end IsImage

end CellularEquiv

end CellularEquiv

end RelCWComplex

section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {C D : Set X}

lemma RelCWComplex.continuousOn_of_continuousOn_closedCell [T2Space X] [RelCWComplex C D]
    (f : X → Y)
    (hf1 : ∀ n (i : cell C n), ContinuousOn f (closedCell n i)) (hf2 : ContinuousOn f D) :
    ContinuousOn f C := by
  rw [continuousOn_iff_isClosed]
  intro A hA
  refine ⟨f ⁻¹' A ∩ C, ?_, by simp⟩
  simp_rw [closed (C := C) _ inter_subset_right, inter_assoc,
    inter_eq_right.2 (closedCell_subset_complex _ _), inter_eq_right.2 base_subset_complex]
  refine ⟨?_, ?_⟩
  · intro n j
    obtain ⟨B, hB, hAB⟩ := (continuousOn_iff_isClosed.1 (hf1 n j)) A hA
    rw [hAB]
    exact hB.inter isClosed_closedCell
  · obtain ⟨B, hB, hAB⟩ := continuousOn_iff_isClosed.1 hf2 A hA
    rw [hAB]
    exact hB.inter (isClosedBase C)

lemma CWComplex.continuousOn_of_continuousOn_closedCell [T2Space X] [CWComplex C] (f : X → Y)
    (hf : ∀ n (i : cell C n), ContinuousOn f (closedCell n i)) : ContinuousOn f C :=
  RelCWComplex.continuousOn_of_continuousOn_closedCell f hf (continuousOn_empty f)

lemma RelCWComplex.continuousOn_iff [T2Space X] [RelCWComplex C D] (f : X → Y) :
    ContinuousOn f C ↔ ContinuousOn f D ∧ ∀ n (i : cell C n), ContinuousOn f (closedCell n i) :=
  ⟨fun hf ↦ ⟨hf.mono base_subset_complex, fun n i ↦ hf.mono (closedCell_subset_complex n i)⟩,
    fun ⟨hf2, hf1⟩ ↦ continuousOn_of_continuousOn_closedCell f hf1 hf2⟩

lemma CWComplex.continuousOn_iff [T2Space X] [CWComplex C] (f : X → Y) :
    ContinuousOn f C ↔ ∀ n (i : cell C n), ContinuousOn f (closedCell n i) :=
  ⟨fun hf ↦ fun n i ↦ hf.mono (closedCell_subset_complex n i),
    fun hf ↦ continuousOn_of_continuousOn_closedCell f hf⟩

lemma RelCWComplex.continuous_of_continuousOn_closedCell [T2Space X] [RelCWComplex C D]
    (f : X → Y)
    (hf : ∀ n (i : cell C n), ContinuousOn f (closedCell n i))
    (hfD : ContinuousOn f D) (hfC : ContinuousOn f (closure Cᶜ)) :
    Continuous f := by
  rw [continuous_iff_continuousOn_univ, ← compl_union_self  (s := C)]
  refine ContinuousOn.mono ?_ (union_subset_union_left C subset_closure)
  apply ContinuousOn.union_isClosed isClosed_closure isClosed hfC
  exact continuousOn_of_continuousOn_closedCell f hf hfD

lemma CWComplex.continuous_of_continuousOn_closedCell [T2Space X] [CWComplex C]
    (f : X → Y) (hf : ∀ n (i : cell C n), ContinuousOn f (closedCell n i))
    (hfC : ContinuousOn f (closure Cᶜ)) :
    Continuous f := by
  exact RelCWComplex.continuous_of_continuousOn_closedCell f hf (continuousOn_empty f) hfC

lemma RelCWComplex.continuous_iff [T2Space X] [RelCWComplex C D] (f : X → Y) :
    Continuous f ↔ ContinuousOn f D ∧ (∀ n (i : cell C n), ContinuousOn f (closedCell n i))
      ∧ ContinuousOn f (closure Cᶜ) :=
  ⟨fun hf ↦ ⟨hf.continuousOn, fun _ _ ↦ hf.continuousOn, hf.continuousOn⟩,
    fun ⟨hfD, hf, hfC⟩ ↦ continuous_of_continuousOn_closedCell f hf hfD hfC⟩

lemma CWComplex.continuous_iff [T2Space X] [CWComplex C] (f : X → Y) :
    Continuous f ↔ (∀ n (i : cell C n), ContinuousOn f (closedCell n i))
      ∧ ContinuousOn f (closure Cᶜ) :=
  ⟨fun hf ↦ ⟨fun _ _ ↦ hf.continuousOn, hf.continuousOn⟩,
    fun ⟨hf, hfC⟩ ↦ continuous_of_continuousOn_closedCell f hf hfC⟩

end

variable {X Y : Type*} [TopologicalSpace X] {C D : Set X}

open Classical in
/-- Defining a piecewise function out of a CW complex `C` in a space `X`. `f` is used on the open
cells, `fD` on the base `D` and `fX` on the rest of `X`. -/
def RelCWComplex.piecewise [RelCWComplex C D] (f : ∀ n (_ : cell C n), X → Y) (fD : X → Y)
    (fX : X → Y) (x : X) : Y :=
  if h : ∃ (n : ℕ) (j : cell C n), x ∈ openCell n j then f (h.choose) ((h.choose_spec).choose) x
    else if x ∈ D then fD x
    else fX x

lemma RelCWComplex.piecewise_apply_of_mem_openCell [RelCWComplex C D]
    {f : ∀ n (_ : cell C n), X → Y} {fD : X → Y} {fX : X → Y} {x : X} {n : ℕ} {j : cell C n}
    (hx : x ∈ openCell n j) : piecewise f fD fX x = f n j x := by
  have h : ∃ (n : ℕ) (j : cell C n), x ∈ openCell n j := ⟨n, j, hx⟩
  have : (⟨h.choose, h.choose_spec.choose⟩ : Σ n, cell C n) = ⟨n, j⟩ := by
    apply eq_of_not_disjoint_openCell
    rw [not_disjoint_iff]
    use x, h.choose_spec.choose_spec
  simp only [piecewise, h, ↓reduceDIte]
  aesop

lemma RelCWComplex.piecewise_apply_of_mem_base [RelCWComplex C D]
    {f : ∀ n (_ : cell C n), X → Y} {fD : X → Y} {fX : X → Y} {x : X}
    (hx : x ∈ D) : piecewise f fD fX x = fD x := by
  have : ¬ ∃ (n : ℕ) (j : cell C n), x ∈ openCell n j :=
    fun ⟨n, j, h⟩ ↦ (disjointBase n j).not_mem_of_mem_left h hx
  simp_all [piecewise]

lemma RelCWComplex.piecewise_apply_of_not_mem_complex [RelCWComplex C D]
    (f : ∀ n (_ : cell C n), X → Y) (fD : X → Y) (fX : X → Y) (x : X) (hx : x ∉ C) :
    piecewise f fD fX x = fX x := by
  have : ¬ ∃ (n : ℕ) (j : cell C n), x ∈ openCell n j := by
    intro ⟨n, j, hj⟩
    exact hx (openCell_subset_complex n j hj)
  have : ¬ x ∈ D := by
    intro h
    exact hx (base_subset_complex h)
  simp_all [piecewise]

lemma RelCWComplex.piecewise_apply_of_mem_closedCell [T2Space X] [RelCWComplex C D]
    {f : ∀ n (_ : cell C n), X → Y} {fD : X → Y} {fX : X → Y}
    (hf1 : ∀ n (i : cell C n) m (j : cell C m) {x} (_ : x ∈ closedCell n i)
      (_ : x ∈ closedCell m j), f n i x = f m j x)
    (hfD1 : ∀ n (i : cell C n) {x} (_ : x ∈ closedCell n i) (_ : x ∈ D), f n i x = fD x)
    {n : ℕ} {i : cell C n} {x : X} (hx : x ∈ closedCell n i) :
    piecewise f fD fX x = f n i x := by
  have hx' := closedCell_subset_skeleton n i hx
  simp_rw [← Subcomplex.mem, mem_skeleton_iff] at hx'
  rcases hx' with hx' | ⟨m, _, j, hx'⟩
  · rw [piecewise_apply_of_mem_base hx']
    exact (hfD1 n i hx hx').symm
  · rw [piecewise_apply_of_mem_openCell hx']
    exact hf1 m j n i (openCell_subset_closedCell m j hx') hx

-- I think everything starting from here needs to be redone

def RelCWComplex.partitionMapComplexNotUniv (C : Set X) [RelCWComplex C D]
  (j : Fin 2 ⊕ Σ n, cell C n) : Set X :=
  match j with
    | .inl 0 => Cᶜ
    | .inl 1 => D
    | .inr ⟨n, i⟩ => openCell n i

def RelCWComplex.indexedPartitionComplexNotUniv [RelCWComplex C D] (hD : D.Nonempty)
    (hC : C ≠ univ) : IndexedPartition (partitionMapComplexNotUniv C) :=
  IndexedPartition.mk' (partitionMapComplexNotUniv C)
    (by
      simp only [Pairwise, onFun]
      intro j j' hjj'
      by_contra h
      rw [not_disjoint_iff] at h
      obtain ⟨x, hxj, hxj'⟩ := h
      apply hjj'
      exact match j, j' with
        | .inl 0, .inl 0 => rfl
        | .inl 0, .inl 1 => by
          simp_all only [partitionMapComplexNotUniv, mem_diff, mem_univ, true_and]
          exact hxj (base_subset_complex hxj')
        | .inl 0, .inr ⟨n, i⟩ => by
          simp_all only [partitionMapComplexNotUniv, mem_diff, mem_univ, true_and]
          exact hxj ((openCell_subset_complex n i) hxj')
        | .inl 1, .inl 0 => by
          simp_all only [partitionMapComplexNotUniv, mem_diff, mem_univ, true_and]
          exact hxj' (base_subset_complex hxj)
        | .inl 1, .inl 1 => rfl
        | .inl 1, .inr ⟨n, i⟩ => by
          simp_all only [partitionMapComplexNotUniv, Fin.isValue, reduceCtorEq]
          exact (disjointBase n i).not_mem_of_mem_left hxj' hxj
        | .inr ⟨n, i⟩, .inl 0 => by
          simp_all only [partitionMapComplexNotUniv, mem_diff, mem_univ, true_and]
          exact hxj' ((openCell_subset_complex n i) hxj)
        | .inr ⟨n, i⟩, .inl 1 => by
          simp_all only [partitionMapComplexNotUniv, Fin.isValue, reduceCtorEq]
          exact (disjointBase n i).not_mem_of_mem_left hxj hxj'
        | .inr ⟨n, i⟩, .inr ⟨m, k⟩ => by
          simp only [partitionMapComplexNotUniv, Sum.inr.injEq] at hxj hxj' ⊢
          apply eq_of_not_disjoint_openCell
          rw [not_disjoint_iff]
          exact ⟨x, hxj, hxj'⟩)
    (fun j ↦ match j with
      | .inl 0 => by
        simp_all only [← compl_ne_univ, ne_eq, compl_univ_iff, partitionMapComplexNotUniv,
          compl_compl, not_false_eq_true]
      | .inl 1 => by simp [partitionMapComplexNotUniv, hD]
      | .inr ⟨n, i⟩ => by
        rw [nonempty_def]
        use (map n i 0)
        simp [partitionMapComplexNotUniv, map_zero_mem_openCell])
    (by
      intro x
      by_cases h : x ∈ C
      · simp only [← union_iUnion_openCell_eq_complex (C := C), mem_union, mem_iUnion] at h
        rcases h with h | ⟨n, i, h⟩
        · use .inl 1
          simp [partitionMapComplexNotUniv, h]
        · use .inr ⟨n, i⟩
          simp [partitionMapComplexNotUniv, h]
      · use .inl 0
        simp [partitionMapComplexNotUniv, h])

lemma RelCWComplex.indexedPartitionComplexNotUniv_index_not_mem_complex (Y : Type*) [Inhabited Y]
    [RelCWComplex C D] {hD : D.Nonempty} {hC : C ≠ univ} {x : X} (hx : x ∉ C) :
    (indexedPartitionComplexNotUniv hD hC).index x = .inl 0 := by
  simp [← IndexedPartition.mem_iff_index_eq, partitionMapComplexNotUniv, hx]

lemma RelCWComplex.indexedPartitionComplexNotUniv_index_mem_base (Y : Type*) [Inhabited Y]
    [RelCWComplex C D] {hD : D.Nonempty} {hC : C ≠ univ} {x : X} (hx : x ∈ D) :
    (indexedPartitionComplexNotUniv hD hC).index x = .inl 1 := by
  simp [← IndexedPartition.mem_iff_index_eq, partitionMapComplexNotUniv, hx]

lemma RelCWComplex.indexedPartitionComplexNotUniv_index_mem_openCell (Y : Type*) [Inhabited Y]
    [RelCWComplex C D] {hD : D.Nonempty} {hC : C ≠ univ} (n : ℕ) (i : cell C n) {x : X}
    (hx : x ∈ openCell n i) :
    (indexedPartitionComplexNotUniv hD hC).index x = .inr ⟨n, i⟩ := by
  simp [← IndexedPartition.mem_iff_index_eq, partitionMapComplexNotUniv, hx]

/-! Defining a function on C -/

open Classical in
def RelCWComplex.mapComplexNotUniv [Inhabited Y] [RelCWComplex C D] (hD : D.Nonempty)
    (hC : C ≠ univ) (f : ∀ n (_ : cell C n), X → Y) (fD : X → Y) : X → Y :=
  (indexedPartitionComplexNotUniv hD hC).piecewise
   (fun j ↦ match j with
    | .inl 0 => default
    | .inl 1 => fD
    | .inr ⟨n, i⟩ => f n i)

lemma RelCWComplex.mapComplexNotUniv_apply_not_mem_complex (Y : Type*) [Inhabited Y]
    [RelCWComplex C D] {hD : D.Nonempty} {hC : C ≠ univ}
    {f : ∀ n (_ : cell C n), X → Y} {fD : X → Y}
    {x : X} (hx : x ∉ C) :
    mapComplexNotUniv hD hC f fD x = default := by
  simp [indexedPartitionComplexNotUniv_index_not_mem_complex Y hx,
    mapComplexNotUniv, IndexedPartition.piecewise_apply, hx]

lemma RelCWComplex.mapComplexNotUniv_apply_mem_base {Y : Type*} [Inhabited Y]
    [RelCWComplex C D] {hD : D.Nonempty} {hC : C ≠ univ}
    {f : ∀ n (_ : cell C n), X → Y} {fD : X → Y} {x : X} (hx : x ∈ D) :
    mapComplexNotUniv hD hC f fD x = fD x := by
  simp [indexedPartitionComplexNotUniv_index_mem_base Y hx, mapComplexNotUniv,
    IndexedPartition.piecewise_apply, hx]

lemma RelCWComplex.mapComplexNotUniv_apply_mem_openCell {Y : Type*} [Inhabited Y]
    [RelCWComplex C D] {hD : D.Nonempty} {hC : C ≠ univ}
    {f : ∀ n (_ : cell C n), X → Y} {fD : X → Y}
    {n : ℕ} {i : cell C n} {x : X} (hx : x ∈ openCell n i) :
    mapComplexNotUniv hD hC f fD x = f n i x := by
  simp [indexedPartitionComplexNotUniv_index_mem_openCell Y n i hx, mapComplexNotUniv,
    IndexedPartition.piecewise_apply, hx]

lemma RelCWComplex.mapComplexNotUniv_apply_mem_closedCell [T2Space X] {Y : Type*} [Inhabited Y]
    [RelCWComplex C D] {hD : D.Nonempty} {hC : C ≠ univ}
    {f : ∀ n (_ : cell C n), X → Y} {fD : X → Y}
    (hf1 : ∀ n (i : cell C n) m (j : cell C m) {x} (_ : x ∈ closedCell n i)
      (_ : x ∈ closedCell m j), f n i x = f m j x)
    (hfD1 : ∀ n (i : cell C n) {x} (_ : x ∈ closedCell n i) (_ : x ∈ D), f n i x = fD x)
    {n : ℕ} {i : cell C n} {x : X} (hx : x ∈ closedCell n i) :
    mapComplexNotUniv hD hC f fD x = f n i x := by
  have hx' := closedCell_subset_skeleton n i hx
  simp_rw [← Subcomplex.mem, mem_skeleton_iff] at hx'
  rcases hx' with hx' | ⟨m, _, j, hx'⟩
  · rw [mapComplexNotUniv_apply_mem_base hx']
    exact (hfD1 n i hx hx').symm
  · rw [mapComplexNotUniv_apply_mem_openCell hx']
    exact hf1 m j n i (openCell_subset_closedCell m j hx') hx

variable [TopologicalSpace Y]

lemma RelCWComplex.mapComplexNotUniv_continuousOn [T2Space X] [Inhabited Y]
    [RelCWComplex C D] (hD : D.Nonempty) (hC : C ≠ univ)
    {f : ∀ n (_ : cell C n), X → Y} {fD : X → Y}
    (hf1 : ∀ n (i : cell C n) m (j : cell C m) {x} (_ : x ∈ closedCell n i)
      (_ : x ∈ closedCell m j), f n i x = f m j x)
    (hfD1 : ∀ n (i : cell C n) {x} (_ : x ∈ closedCell n i) (_ : x ∈ D), f n i x = fD x)
    (hf2 : ∀ n (i : cell C n), ContinuousOn (f n i) (closedCell n i))
    (hfD2 : ContinuousOn fD D) :
    ContinuousOn (mapComplexNotUniv hD hC f fD) C := by
  rw [continuousOn_iff]
  constructor
  · apply hfD2.congr
    intro x hx
    exact mapComplexNotUniv_apply_mem_base hx
  · intro n i
    apply (hf2 n i).congr
    intro x hx
    exact mapComplexNotUniv_apply_mem_closedCell hf1 hfD1 hx

/-! Defining a function on the whole type -/

open Classical in
/-- A version of `mapComplexNotUniv` that also defines a sensible function outside of the
complex. -/
def RelCWComplex.mapComplexNotUniv' [Inhabited Y] [RelCWComplex C D] (hD : D.Nonempty)
    (hC : C ≠ univ) (f : ∀ n (_ : cell C n), X → Y) (fD : X → Y) (fC : X → Y) : X → Y :=
  (indexedPartitionComplexNotUniv hD hC).piecewise
   (fun j ↦ match j with
    | .inl 0 => fC
    | .inl 1 => fD
    | .inr ⟨n, i⟩ => f n i)

lemma RelCWComplex.mapComplexNotUniv'_apply_not_mem_complex (Y : Type*) [Inhabited Y]
    [RelCWComplex C D] {hD : D.Nonempty} {hC : C ≠ univ}
    {f : ∀ n (_ : cell C n), X → Y} {fD : X → Y} {fC : X → Y}
    {x : X} (hx : x ∉ C) :
    mapComplexNotUniv' hD hC f fD fC x = fC x := by
  simp [indexedPartitionComplexNotUniv_index_not_mem_complex Y hx,
    mapComplexNotUniv', IndexedPartition.piecewise_apply, hx]

lemma RelCWComplex.mapComplexNotUniv'_apply_mem_base {Y : Type*} [Inhabited Y]
    [RelCWComplex C D] {hD : D.Nonempty} {hC : C ≠ univ}
    {f : ∀ n (_ : cell C n), X → Y} {fD : X → Y} {fC : X → Y} {x : X} (hx : x ∈ D) :
    mapComplexNotUniv' hD hC f fD fC x = fD x := by
  simp [indexedPartitionComplexNotUniv_index_mem_base Y hx, mapComplexNotUniv',
    IndexedPartition.piecewise_apply, hx]

lemma RelCWComplex.mapComplexNotUniv'_apply_mem_openCell {Y : Type*} [Inhabited Y]
    [RelCWComplex C D] {hD : D.Nonempty} {hC : C ≠ univ}
    {f : ∀ n (_ : cell C n), X → Y} {fD : X → Y} {fC : X → Y}
    {n : ℕ} {i : cell C n} {x : X} (hx : x ∈ openCell n i) :
    mapComplexNotUniv' hD hC f fD fC x = f n i x := by
  simp [indexedPartitionComplexNotUniv_index_mem_openCell Y n i hx, mapComplexNotUniv',
    IndexedPartition.piecewise_apply, hx]

lemma RelCWComplex.mapComplexNotUniv'_apply_mem_closedCell [T2Space X] {Y : Type*} [Inhabited Y]
    [RelCWComplex C D] {hD : D.Nonempty} {hC : C ≠ univ}
    {f : ∀ n (_ : cell C n), X → Y} {fD : X → Y} {fC : X → Y}
    (hf1 : ∀ n (i : cell C n) m (j : cell C m) {x} (_ : x ∈ closedCell n i)
      (_ : x ∈ closedCell m j), f n i x = f m j x)
    (hfD1 : ∀ n (i : cell C n) {x} (_ : x ∈ closedCell n i) (_ : x ∈ D), f n i x = fD x)
    {n : ℕ} {i : cell C n} {x : X} (hx : x ∈ closedCell n i) :
    mapComplexNotUniv' hD hC f fD fC x = f n i x := by
  have hx' := closedCell_subset_skeleton n i hx
  simp_rw [← Subcomplex.mem, mem_skeleton_iff] at hx'
  rcases hx' with hx' | ⟨m, _, j, hx'⟩
  · rw [mapComplexNotUniv'_apply_mem_base hx']
    exact (hfD1 n i hx hx').symm
  · rw [mapComplexNotUniv'_apply_mem_openCell hx']
    exact hf1 m j n i (openCell_subset_closedCell m j hx') hx

lemma RelCWComplex.mapComplexNotUniv'_apply_mem_closure_complex_compl (Y : Type*) [Inhabited Y]
    [RelCWComplex C D] {hD : D.Nonempty} {hC : C ≠ univ}
    {f : ∀ n (_ : cell C n), X → Y} {fD : X → Y} {fC : X → Y}
    (hfC1 : ∀ n (i : cell C n) {x} (_ : x ∈ closedCell n i) (_ : x ∈ closure Cᶜ), f n i x = fC x)
    (hfCD : ∀ {x} (_ : x ∈ closure Cᶜ) (_ : x ∈ D), fC x = fD x)
    {x : X} (hx : x ∈ closure Cᶜ) :
    mapComplexNotUniv' hD hC f fD fC x = fC x := by
  by_cases h : x ∈ Cᶜ
  · exact mapComplexNotUniv'_apply_not_mem_complex Y h
  · simp only [← union_iUnion_openCell_eq_complex, mem_compl_iff, mem_union, mem_iUnion,
      not_not] at h
    rcases h with h | ⟨n, i, h⟩
    · rw [mapComplexNotUniv'_apply_mem_base h]
      exact (hfCD hx h).symm
    · rw [mapComplexNotUniv'_apply_mem_openCell h]
      exact hfC1 n i (openCell_subset_closedCell n i h) hx

lemma RelCWComplex.mapComplexNotUniv'_continuous [T2Space X] [Inhabited Y]
    [RelCWComplex C D] (hD : D.Nonempty) (hC : C ≠ univ)
    {f : ∀ n (_ : cell C n), X → Y} {fD : X → Y} {fC : X → Y}
    (hf1 : ∀ n (i : cell C n) m (j : cell C m) {x} (_ : x ∈ closedCell n i)
      (_ : x ∈ closedCell m j), f n i x = f m j x)
    (hfD1 : ∀ n (i : cell C n) {x} (_ : x ∈ closedCell n i) (_ : x ∈ D), f n i x = fD x)
    (hfC1 : ∀ n (i : cell C n) {x} (_ : x ∈ closedCell n i) (_ : x ∈ closure Cᶜ), f n i x = fC x)
    (hfCD : ∀ {x} (_ : x ∈ closure Cᶜ) (_ : x ∈ D), fC x = fD x)
    (hf2 : ∀ n (i : cell C n), ContinuousOn (f n i) (closedCell n i))
    (hfD2 : ContinuousOn fD D) (hfC2 : ContinuousOn fC (closure Cᶜ)) :
    Continuous (mapComplexNotUniv' hD hC f fD fC) := by
  rw [continuous_iff (C := C)]
  refine ⟨?_, ?_, ?_⟩
  · apply hfD2.congr
    intro x hx
    exact mapComplexNotUniv'_apply_mem_base hx
  · intro n i
    apply (hf2 n i).congr
    intro x hx
    exact mapComplexNotUniv'_apply_mem_closedCell hf1 hfD1 hx
  · apply hfC2.congr
    intro x hx
    exact mapComplexNotUniv'_apply_mem_closure_complex_compl Y hfC1 hfCD hx

end Topology
