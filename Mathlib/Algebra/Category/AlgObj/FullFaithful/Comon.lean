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
  [MonoidalCategory D] (F : C ⥤ D) (X : C)

section FullyFaithful

variable {F} (hF : F.FullyFaithful)

/-- Pullback a comonoid object along a fully faithful lax monoidal functor. -/
@[simps]
abbrev FullyFaithful.comonObj [F.LaxMonoidal] (X : C) [ComonObj (F.obj X)] : ComonObj X where
  counit := hF.preimage (ComonObj.counit ≫ Functor.LaxMonoidal.ε F)
  comul := hF.preimage (ComonObj.comul ≫ Functor.LaxMonoidal.μ F X X)
  counit_comul := by
    apply hF.map_injective
    simp [← LaxMonoidal.μ_natural_left]
  comul_counit := by
    apply hF.map_injective
    simp [← LaxMonoidal.μ_natural_right]
  comul_assoc := by
    apply hF.map_injective
    simp [← LaxMonoidal.μ_natural_left_assoc, ← LaxMonoidal.μ_natural_right]

lemma FullyFaithful.isComonHom [F.Monoidal] (X Y : C) [ComonObj (F.obj X)]
    [ComonObj (F.obj Y)] (f : F.obj X ⟶ F.obj Y) [IsComonHom f] :
    letI := hF.comonObj X; letI := hF.comonObj Y;
    IsComonHom (hF.preimage f) := by
  let := hF.comonObj X; let := hF.comonObj Y;
  refine IsComonHom.mk ?_ ?_
  · apply hF.map_injective
    simp
  · apply hF.map_injective
    simp [Monoidal.map_tensor]

/-- Pullback a comonoid object along a fully faithful lax monoidal functor as a bundled object. -/
@[implicit_reducible]
def FullyFaithful.comon [F.LaxMonoidal] (hF : F.FullyFaithful) (X : C) [ComonObj (F.obj X)] :
    Comon C where
  X := X
  comon := hF.comonObj X

/-- Pullback a morphism between comonoid objects along a fully faithful monoidal functor. -/
@[simps!]
def FullyFaithful.comonMap [F.Monoidal] (hF : F.FullyFaithful) (X Y : C) [ComonObj (F.obj X)]
    [ComonObj (F.obj Y)] (f : F.obj X ⟶ F.obj Y) [IsComonHom f] : hF.comon X ⟶ hF.comon Y :=
  letI := hF.isComonHom X Y f; .mk (hF.preimage f)

end FullyFaithful

end CategoryTheory.Functor

-- #min_imports
