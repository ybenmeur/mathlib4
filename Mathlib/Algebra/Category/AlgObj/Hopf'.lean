/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.AlgObj.Bimon'
public import Mathlib.CategoryTheory.Monoidal.Hopf_

/-!
# The category of Hopf monoids in a braided monoidal category.


## TODO

* Show that in a Cartesian monoidal category Hopf monoids are exactly group objects.
* Show that `Hopf (ModuleCat R) ≌ HopfAlgCat R`.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory C]

open scoped MonObj ComonObj

namespace Hopf

/-- A morphism of Hopf objects. -/
@[ext]
structure Hom (M N : Hopf C) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  [isBimonHom_hom : IsBimonHom hom]

attribute [instance] Hopf.Hom.isBimonHom_hom

/-- Construct a morphism `M ⟶ N` of `Hopf C` from a map `f : M ⟶ N` and
a `IsBimonHom f` instance. -/
abbrev Hom.mk' {M N : Hopf C} (f : M.X ⟶ N.X)
    (one_f : η ≫ f = η := by cat_disch)
    (mul_f : μ ≫ f = (f ⊗ₘ f) ≫ μ := by cat_disch)
    (f_counit : f ≫ ε[N.X] = ε[M.X] := by cat_disch)
    (f_comul : f ≫ Δ[N.X] = Δ[M.X] ≫ (f ⊗ₘ f) := by cat_disch) : Hom M N :=
  have : IsMonHom f := ⟨one_f, mul_f⟩
  have : IsComonHom f := ⟨f_counit, f_comul⟩
  have : IsBimonHom f := ⟨⟩
  .mk f

-- instance (X : C) [HopfObj X] : IsBimonHom (𝟙 X) := ⟨⟩
-- instance (X Y Z : C) [HopfObj X] [HopfObj Y] [HopfObj Z] (f : X ⟶ Y) (g : Y ⟶ Z)
--     [IsBimonHom f] [IsBimonHom g] : IsBimonHom (f ≫ g) := ⟨⟩

/-- The identity morphism on a Hopf object. -/
@[simps]
def id (M : Hopf C) : Hom M M := ⟨𝟙 M.X⟩

instance homInhabited (M : Hopf C) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of Hopf objects. -/
@[simps]
def comp {M N O : Hopf C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom


attribute [-instance] instCategory
-- #synth Category (Hopf C)

instance : Category (Hopf C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

instance {M N : Bimon' C} (f : M ⟶ N) : IsBimonHom f.hom := inferInstanceAs (IsBimonHom f.hom)

@[ext] lemma ext {X Y : Hopf C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g := Hom.ext w

@[simp] theorem id_hom' (M : Hopf C) : (𝟙 M : Hom M M).hom = 𝟙 M.X := rfl

@[simp]
theorem comp_hom' {M N K : Hopf C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

@[simps]
abbrev toBimon' : Hopf C ⥤ Bimon' C where
  obj X := ⟨X.X⟩
  map f := ⟨f.hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev ofBimonHom {X Y : Hopf C} (f : toBimon'.obj X ⟶ toBimon'.obj Y) : X ⟶ Y where
  hom := f.hom
  isBimonHom_hom := f.isBimonHom_hom

-- /-- A Hopf monoid is a bimonoid. -/
-- abbrev toBimon (A : Hopf C) : Bimon C := .mk A.X

-- /--
-- Morphisms of Hopf monoids are just morphisms of the underlying bimonoids.
-- In fact they automatically intertwine the antipodes, proved below.
-- -/
-- instance : Category (Hopf C) :=
--   inferInstanceAs <| Category (InducedCategory (Bimon C) Hopf.toBimon)

-- def homMk {A B : Hopf C} (f : A.X ⟶ B.X) [IsBimonHom f] : A ⟶ B := ⟨Bimon.Hom.mk f⟩

-- @[ext]
-- lemma Hom.ext {A B : Hopf C} (f g : A ⟶ B) (h : f.hom = g.hom) : f = g :=
--   InducedCategory.hom_ext h

-- @[simp]
-- lemma homMk_hom {A B : Hopf C} (f : A.X ⟶ B.X) [IsBimonHom f] :
--     (homMk f).hom = Bimon.Hom.mk f := rfl

end Hopf

namespace Functor

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D] [BraidedCategory D]

open OplaxMonoidal HopfObj

/-- The image of a Hopf object under an braided functor is a Hopf object. -/
abbrev obj.instHopfObj (A : C) [HopfObj A] (F : C ⥤ D) [F.Braided] : HopfObj (F.obj A) where
  __ := obj.instBimonObj A F
  antipode := F.map antipode
  antipode_left := by simp [← map_comp]
  antipode_right := by simp [← map_comp]

attribute [local instance] obj.instHopfObj

-- @[reassoc, simp] lemma obj.antipode_def (F : C ⥤ D) [F.Braided] (X : C) [HopfObj X] :
--     𝒮[F.obj X] = F.map 𝒮 := rfl

-- instance map.instIsBimon_Hom (F : C ⥤ D) [F.Braided] {X Y : C} [HopfObj X] [HopfObj Y]
--     (f : X ⟶ Y) [IsBimonHom f] : IsBimonHom (F.map f) := ⟨⟩

/-- A braided functor takes Hopf objects to Hopf objects.

That is, a braided functor `F : C ⥤ D` induces a functor `Hopf C ⥤ Hopf D`.
-/
@[implicit_reducible, simps]
def mapHopf (F : C ⥤ D) [F.Braided] : Hopf C ⥤ Hopf D where
  obj A := .mk (F.obj A.X)
  map f := .mk (F.map f.hom)
  map_id A := by ext; simp
  map_comp f g := by ext; simp

example (F : C ⥤ D) [F.Braided] (X : Hopf C) : μ[(F.mapHopf.obj X).X] =
  LaxMonoidal.μ F _ _ ≫ F.map μ[X.X] := by simp

-- TODO We haven't yet set up the category structure on `OplaxMonoidalFunctor C D`
-- and so can't state `mapComonFunctor : OplaxMonoidalFunctor C D ⥤ Hopf C ⥤ Hopf D`.

end Functor

end CategoryTheory
