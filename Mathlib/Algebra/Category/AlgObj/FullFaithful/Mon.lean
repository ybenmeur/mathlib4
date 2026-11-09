/-
Copyright (c) 2026 Yacine Benmeuraiem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yacine Benmeuraiem
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon

/-! A fully faithful monoidal functor can lift monoid objects -/

@[expose] public section

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
  [MonoidalCategory D] {F : C ⥤ D}

section OplaxMonoidal

variable
    [F.OplaxMonoidal] (X : C)

/-- Pullback a monoid object along a fully faithful oplax monoidal functor as a bundled object. -/
@[to_additive (attr := implicit_reducible) FullyFaithful.addMon
/-- Pullback an additive monoid object along a fully faithful oplax monoidal functor as a bundled
object. -/]
def FullyFaithful.mon (hF : F.FullyFaithful) (X : C) [MonObj (F.obj X)] :
    Mon C where
  X := X
  mon := hF.monObj X

end OplaxMonoidal

section Monoidal
variable [F.Monoidal]

lemma FullyFaithful.isMonHom (hF : F.FullyFaithful) (X Y : C) [MonObj (F.obj X)]
    [MonObj (F.obj Y)] (f : F.obj X ⟶ F.obj Y) [IsMonHom f] :
    letI := hF.monObj X; letI := hF.monObj Y;
    IsMonHom (hF.preimage f) := by
  let := hF.monObj X; let := hF.monObj Y;
  refine IsMonHom.mk ?_ ?_
  · apply hF.map_injective
    simp
  · apply hF.map_injective
    simp [Monoidal.map_tensor]

/-- Pullback a morphism between monoid objects along a fully faithful monoidal functor. -/
@[simps!]
def FullyFaithful.monMap (hF : F.FullyFaithful) (X Y : C) [MonObj (F.obj X)]
    [MonObj (F.obj Y)] (f : F.obj X ⟶ F.obj Y) [IsMonHom f] : hF.mon X ⟶ hF.mon Y :=
  letI := hF.isMonHom X Y f; .mk (hF.preimage f)

end Monoidal
end CategoryTheory.Functor

-- #min_imports
