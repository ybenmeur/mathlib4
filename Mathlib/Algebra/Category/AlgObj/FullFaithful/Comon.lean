/-
Copyright (c) 2026 Yacine Benmeuraiem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yacine Benmeuraiem
-/
module

public import Mathlib.CategoryTheory.Monoidal.Comon_

/-! A fully faithful monoidal functor can lift comonoid objects -/

@[expose] public section

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
  [MonoidalCategory D] (F : C ⥤ D) [F.Full] [F.Faithful]
    [F.LaxMonoidal] (X : C)

/-! If `F` is a fully faithful monoidal functor, and `F.obj X` admits a comonoid object
structure, then there is a natural comonoid object structure on `X`. -/
@[implicit_reducible]
noncomputable def comonobj_of_comonobj_obj [ComonObj (F.obj X)] : ComonObj X where
  counit := F.preimage (ComonObj.counit ≫ Functor.LaxMonoidal.ε F)
  comul := F.preimage (ComonObj.comul ≫ Functor.LaxMonoidal.μ F X X)
  counit_comul := by
    apply F.map_injective
    simp [← LaxMonoidal.μ_natural_left]
  comul_counit := by
    apply F.map_injective
    simp [← LaxMonoidal.μ_natural_right]
  comul_assoc := by
    apply F.map_injective
    simp [← LaxMonoidal.μ_natural_left_assoc, ← LaxMonoidal.μ_natural_right]

lemma comonobj_of_comonobj_obj_counit_def [ComonObj (F.obj X)] :
    letI := F.comonobj_of_comonobj_obj X;
    ComonObj.counit (X:=X) = F.preimage (ComonObj.counit ≫ Functor.LaxMonoidal.ε F) := rfl

@[simp]
lemma comonobj_of_comonobj_obj_map_counit [ComonObj (F.obj X)] :
    letI := F.comonobj_of_comonobj_obj X;
    F.map (ComonObj.counit (X:=X)) = ComonObj.counit ≫ Functor.LaxMonoidal.ε F :=
  F.map_preimage _

lemma comonobj_of_comonobj_obj_comul_def [ComonObj (F.obj X)] :
    letI := F.comonobj_of_comonobj_obj X;
    ComonObj.comul (X:=X) = F.preimage (ComonObj.comul ≫ Functor.LaxMonoidal.μ F X X) := rfl

@[simp]
lemma comonobj_of_comonobj_obj_map_comul [ComonObj (F.obj X)] :
    letI := F.comonobj_of_comonobj_obj X;
    F.map (ComonObj.comul (X:=X)) = ComonObj.comul ≫ Functor.LaxMonoidal.μ F X X :=
  F.map_preimage _

section FullyFaithful

variable {F}

/-- Pullback a comonoid object along a fully faithful lax monoidal functor. -/
@[simps]
abbrev FullyFaithful.comonObj (hF : F.FullyFaithful) (X : C) [ComonObj (F.obj X)] : ComonObj X where
  counit := hF.preimage (ComonObj.counit ≫ Functor.LaxMonoidal.ε F)
  comul := hF.preimage (ComonObj.comul ≫ Functor.LaxMonoidal.μ F X X)
  counit_comul := by
    apply F.map_injective
    simp [← LaxMonoidal.μ_natural_left]
  comul_counit := by
    apply F.map_injective
    simp [← LaxMonoidal.μ_natural_right]
  comul_assoc := by
    apply F.map_injective
    simp [← LaxMonoidal.μ_natural_left_assoc, ← LaxMonoidal.μ_natural_right]

end FullyFaithful

end CategoryTheory.Functor

-- #min_imports
