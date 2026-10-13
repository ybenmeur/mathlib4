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
  [MonoidalCategory D] [BraidedCategory D] (F : C ⥤ D) [F.Full] [F.Faithful]
    [F.Braided] (X : C)

/-! If `F` is a fully faithful braided functor, and `F.obj X` admits a Hopf object
structure, then there is a natural Hopf object structure on `X`. -/
@[implicit_reducible]
noncomputable def hopfobj_of_hopfobj_obj [h : HopfObj (F.obj X)] : HopfObj X where
  __ := F.bimonobj_of_bimonobj_obj X
  antipode := F.preimage antipode
  antipode_left := by
    apply F.map_injective
    simp [Monoidal.map_whiskerRight F]
  antipode_right := by
    apply F.map_injective
    simp [Monoidal.map_whiskerLeft F]

section FullyFaithful

variable {F}

/-- Pullback a Hopf object along a fully faithful braided functor. -/
@[simps]
abbrev FullyFaithful.hopfObj (hF : F.FullyFaithful) (X : C) [h : HopfObj (F.obj X)] :
    HopfObj X where
  __ := hF.bimonObj X
  antipode := hF.preimage antipode
  antipode_left := by
    apply F.map_injective
    simp [Monoidal.map_whiskerRight F]
  antipode_right := by
    apply F.map_injective
    simp [Monoidal.map_whiskerLeft F]

end FullyFaithful

end CategoryTheory.Functor

-- #min_imports
