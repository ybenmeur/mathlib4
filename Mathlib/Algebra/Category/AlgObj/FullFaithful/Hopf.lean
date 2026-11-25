/-
Copyright (c) 2026 Yacine Benmeuraiem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yacine Benmeuraiem
-/
module

public import Mathlib.Algebra.Category.AlgObj.FullFaithful.Bimon
public import Mathlib.CategoryTheory.Monoidal.Hopf_

/-! A fully faithful braided functor can lift Hopf objects -/

@[expose] public section

namespace CategoryTheory.Functor

open HopfObj

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalCategory D] [BraidedCategory D] (F : C ⥤ D) [F.Braided] (X : C)

section FullyFaithful

variable {F}

/-- Pullback a Hopf object along a fully faithful braided functor. -/
@[simps]
abbrev FullyFaithful.hopfObj (hF : F.FullyFaithful) (X : C) [h : HopfObj (F.obj X)] :
    HopfObj X where
  __ := hF.bimonObj X
  antipode := hF.preimage antipode
  antipode_left := by
    apply hF.map_injective
    simp [Monoidal.map_whiskerRight F]
  antipode_right := by
    apply hF.map_injective
    simp [Monoidal.map_whiskerLeft F]


/-- Pullback a Hopf monoid along a fully faithful braided functor as a bundled object. -/
@[implicit_reducible]
def FullyFaithful.hopf (hF : F.FullyFaithful) (X : C) (h : HopfObj (F.obj X) := by infer_instance) :
    Hopf C where
  X := X
  hopf := hF.hopfObj X

/-- Pullback a morphism between Hopf monoids along a fully faithful braided functor. -/
@[simps!]
def FullyFaithful.hopfMap (hF : F.FullyFaithful) (X Y : C) [HopfObj (F.obj X)]
    [HopfObj (F.obj Y)] (f : F.obj X ⟶ F.obj Y) [IsBimonHom f] : hF.hopf X ⟶ hF.hopf Y :=
  letI := hF.isBimonHom X Y f; Hopf.homMk (hF.preimage f)

end FullyFaithful

end CategoryTheory.Functor

-- #min_imports
