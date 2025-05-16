import CWcomplexes.RelLemmas

noncomputable section

open Metric Set

def Set.Quotient.collapse {α : Type*} (s : Set α) : Setoid α where
  r x y := (x ∈ s ∧ y ∈ s) ∨ x = y
  iseqv := {
    refl x := .inr rfl
    symm {x} {y} h := by
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    trans {x} {y} {z} hxy hyz := by
      rcases hxy with hxy | hxy
      · rcases hyz with hyz | hyz
        · exact Or.inl ⟨hxy.1, hyz.2⟩
        · exact Or.inl (hyz ▸ hxy)
      · rcases hyz with hyz | hyz
        · exact Or.inl (hxy ▸ hyz)
        · exact Or.inr (hxy.trans hyz)
  }

instance Set.Quotient.instHasQuotient {α : Type*} : HasQuotient α (Set α) where
  quotient' s := Quotient (collapse s)

def Set.Quotient.mk_collapse {α : Type*} {s : Set α} : α → α ⧸ s := Quotient.mk''

@[simp] lemma Set.Quotient.collapse_equiv_iff {α : Type*} (s : Set α) (a b : α) :
    (mk_collapse a : α ⧸ s) = mk_collapse b ↔ ((a ∈ s ∧ b ∈ s) ∨ a = b) := by
  unfold mk_collapse
  rw [Quotient.eq_iff_equiv]
  rfl

lemma Set.Quotient.injOn_mk {α : Type*} {s : Set α} :
    (univ \ s).InjOn (Set.Quotient.mk_collapse (s := s)) := by
  intro x ⟨_, hx⟩ y ⟨_, hy⟩ hxy
  rw [collapse_equiv_iff] at hxy
  simp_all

def PartialEquiv.SetQuotient {α : Type*} {s : Set α} : PartialEquiv α (α ⧸ s) where
  toFun := Set.Quotient.mk_collapse
  invFun y := Classical.choose (Quotient.exists_rep y)
  source := univ \ s
  target := univ \ (Set.Quotient.mk_collapse '' s)
  map_source' x hy := by
    refine ⟨mem_univ _ , ?_⟩
    intro hx
    obtain ⟨_, hy⟩ := hy
    apply hy
    exact Set.Quotient.injOn_mk.mem_of_mem_image sorry sorry hx --no
  map_target' y := sorry
  left_inv' := sorry
  right_inv' := sorry

-- why doesn't this get inferred automatically???
instance Topology.instTopologicalSpaceQuotient {α : Type*} [TopologicalSpace α] (s : Set α) :
    TopologicalSpace (α ⧸ s) :=
  _root_.instTopologicalSpaceQuotient



namespace Topology.RelCWComplex

variable {X : Type*} [TopologicalSpace X] {C D : Set X} [RelCWComplex C D] (E : Subcomplex C)

#check Quotient.rec

instance instQuotient [Nonempty E] :
    CWComplex (X := X ⧸ (E : Set X)) (Set.Quotient.mk_collapse '' C) where
  cell n := match n with
    | 0 => ((univ : Set (cell C 0)) \ (E.I 0) : Set (cell C 0)) ⊕ Unit
    | (n + 1) => ((univ : Set (cell C (n + 1))) \ (E.I (n + 1)) : Set (cell C (n + 1)))
  map n i := match n with
    | 0 => match i with
      | .inl ⟨i, hi⟩ => sorry --map (C := C) 0 i
      | .inr j => PartialEquiv.single ![] ⟦Classical.choice (α := E) inferInstance⟧
    | (n + 1) => sorry
  source_eq := sorry
  continuousOn := sorry
  continuousOn_symm := sorry
  pairwiseDisjoint' := sorry
  mapsTo' := sorry
  closed' := sorry
  union' := sorry


-- this does not seem to work. Simply define custom notation?
/-
instance instHasQuotient: HasQuotient (RelCWComplex C D) (Subcomplex C) where
  quotient' E := X ⧸ (E : Set X)
-/

end Topology.RelCWComplex

#check  t2Setoid
