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
  [MonoidalCategory D] (F : C ⥤ D) [F.Full] [F.Faithful]
    [F.OplaxMonoidal] (X : C)

/-! If `F` is a fully faithful monoidal functor, and `F.obj X` admits a monoid object
structure, then there is a natural monoid object structure on `X`. -/
@[implicit_reducible]
noncomputable def monobj_of_monobj_obj [MonObj (F.obj X)] : MonObj X := by
  have : F.FullyFaithful := by exact FullyFaithful.ofFullyFaithful F
  exact this.monObj X

lemma monobj_of_monobj_obj_one_def [MonObj (F.obj X)] :
    letI := F.monobj_of_monobj_obj X;
    MonObj.one (X:=X) =
      F.preimage (Functor.OplaxMonoidal.η F ≫ MonObj.one) := rfl

@[simp]
lemma monobj_of_monobj_obj_map_one [MonObj (F.obj X)] :
    letI := F.monobj_of_monobj_obj X;
    F.map (MonObj.one (X:=X)) = Functor.OplaxMonoidal.η F ≫ MonObj.one :=
  F.map_preimage _

lemma monobj_of_monobj_obj_mul_def [MonObj (F.obj X)] :
    letI := F.monobj_of_monobj_obj X;
    MonObj.mul (X:=X) =
      F.preimage (Functor.OplaxMonoidal.δ F X X ≫ MonObj.mul) := rfl

@[simp]
lemma monobj_of_monobj_obj_map_mul [MonObj (F.obj X)] :
    letI := F.monobj_of_monobj_obj X;
    F.map (MonObj.mul (X:=X)) = Functor.OplaxMonoidal.δ F X X ≫ MonObj.mul :=
  F.map_preimage _

end CategoryTheory.Functor

-- #min_imports
