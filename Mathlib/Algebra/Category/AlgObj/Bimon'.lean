/-
Copyright (c) 2026 Yacine Benmeuraiem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yacine Benmeuraiem
-/
module

public import Mathlib.CategoryTheory.Monoidal.Bimon_


/-! alternative definition of the category of bimonoid objects -/

@[expose] public section

-- #check CoalgCat.comonEquivalence
-- #check ModuleCat.monModuleEquivalenceAlgebra

universe u v

open CategoryTheory MonoidalCategory ComonObj MonObj BimonObj

section Bimon'

variable (C : Type*) [Category C] [MonoidalCategory C] [BraidedCategory C]

structure Bimon' where
  X : C
  [bimon : BimonObj X]

variable (X Y : C) [BimonObj X] [BimonObj Y] (f : X ⟶ Y) [IsBimonHom f]
-- #synth IsMonHom f

attribute [instance] Bimon'.bimon

namespace Bimon'

variable {C}

/-- A morphism of monoid objects. -/
@[ext]
structure Hom (M N : Bimon' C) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  [isBimonHom_hom : IsBimonHom hom]

attribute [instance] Bimon'.Hom.isBimonHom_hom

/-- Construct a morphism `M ⟶ N` of `Mon C` from a map `f : M ⟶ N` and a `IsMonHom f` instance. -/
abbrev Hom.mk' {M N : Bimon' C} (f : M.X ⟶ N.X)
    (one_f : η ≫ f = η := by cat_disch)
    (mul_f : μ ≫ f = (f ⊗ₘ f) ≫ μ := by cat_disch)
    (f_counit : f ≫ ε[N.X] = ε[M.X] := by cat_disch)
    (f_comul : f ≫ Δ[N.X] = Δ[M.X] ≫ (f ⊗ₘ f) := by cat_disch) : Hom M N :=
  have : IsMonHom f := ⟨one_f, mul_f⟩
  have : IsComonHom f := ⟨f_counit, f_comul⟩
  have : IsBimonHom f := ⟨⟩
  .mk f

instance (X : C) [BimonObj X] : IsBimonHom (𝟙 X) := ⟨⟩
instance (X Y Z : C) [BimonObj X] [BimonObj Y] [BimonObj Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsBimonHom f] [IsBimonHom g] : IsBimonHom (f ≫ g) := ⟨⟩

/-- The identity morphism on a monoid object. -/
@[simps]
def id (M : Bimon' C) : Hom M M := ⟨𝟙 M.X⟩

instance homInhabited (M : Bimon' C) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def comp {M N O : Bimon' C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom

instance : Category (Bimon' C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

instance {M N : Bimon' C} (f : M ⟶ N) : IsBimonHom f.hom := inferInstanceAs (IsBimonHom f.hom)

@[ext] lemma ext {X Y : Bimon' C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g := Hom.ext w

@[simp] theorem id_hom' (M : Bimon' C) : (𝟙 M : Hom M M).hom = 𝟙 M.X := rfl

@[simp]
theorem comp_hom' {M N K : Bimon' C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

instance (X Y : Bimon C) (f : X ⟶ Y) : IsMonHom f.hom.hom := f.hom.isMonHom_hom
instance (X Y : Bimon C) (f : X ⟶ Y) : IsComonHom f.hom.hom where
  hom_counit := congr(($f.isComonHom_hom.hom_counit).hom)
  hom_comul := congr(($f.isComonHom_hom.hom_comul).hom)

@[simps]
def toprime : Bimon C ⥤ Bimon' C where
  obj M := ⟨M.X.X⟩
  map f := .mk' f.hom.hom
  map_id M := rfl
  map_comp f g := rfl

-- def _root_.Bimon.Hom.mk' {X Y : Bimon C} (f : X ⟶ Y) [h : IsBimonHom f.hom.hom] : X ⟶ Y where
--   hom := {
--     hom := f.hom.hom
--     isMonHom_hom := h.toIsMonHom
--   }
--   isComonHom_hom := {
--     hom_counit := Mon.Hom.ext' (IsComonHom.hom_counit f.hom.hom)
--     hom_comul := Mon.Hom.ext' (IsComonHom.hom_comul f.hom.hom)
--   }

set_option backward.isDefEq.respectTransparency false in
def _root_.Bimon.Hom.mk' {X Y : C} [BimonObj X] [BimonObj Y] (f : X ⟶ Y) [h : IsBimonHom f] :
    Bimon.mk' X ⟶ Bimon.mk' Y where
  hom := {
    hom := f
    isMonHom_hom := h.toIsMonHom
  }
  isComonHom_hom := {
    hom_counit := Mon.Hom.ext' (IsComonHom.hom_counit f)
    hom_comul := Mon.Hom.ext' (IsComonHom.hom_comul f)
  }

set_option backward.isDefEq.respectTransparency false in
@[simps]
def fromprime : Bimon' C ⥤ Bimon C where
  obj M := .mk' M.X
  map f := {
    hom := {
      hom := f.hom
      isMonHom_hom := f.isBimonHom_hom.toIsMonHom
    }
    isComonHom_hom := {
      hom_counit := Mon.Hom.ext' (IsComonHom.hom_counit f.hom)
      hom_comul := Mon.Hom.ext' (IsComonHom.hom_comul f.hom)
    }
  }
  map_id _ := rfl
  map_comp _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
def equiv : Bimon C ≌ Bimon' C where
  functor := toprime
  inverse := fromprime
  unitIso := NatIso.ofComponents Iso.refl (by intros; ext; simp)
  counitIso := NatIso.ofComponents Iso.refl (by intros; ext; simp)
  functor_unitIso_comp := by intros; ext; simp

end Bimon'

namespace CategoryTheory.Functor

variable {D : Type*} [Category D] [MonoidalCategory D] [BraidedCategory D]

open OplaxMonoidal ComonObj IsComonHom

variable {C}

/-- The image of a bimonoid object under an braided functor is a bimonoid object. -/
abbrev obj.instBimonObj (A : C) [BimonObj A] (F : C ⥤ D) [F.Braided] : BimonObj (F.obj A) where
  __ := obj.instComonObj A F
  __ := monObjObj A
  mul_comul := by
    simp only [μ_def, Δ_def, Category.assoc]
    simp only [← F.map_comp_assoc, mul_comul]
    simp only [map_comp, Category.assoc]
    simp only [Monoidal.map_tensor F, ← Category.assoc]
    rw [Monoidal.μ_δ F A A, Category.id_comp, ← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    congr 1
    simp only [Monoidal.μ_δ, Category.comp_id, δ_natural]
    rw [← tensorHom_comp_tensorHom]
    rw [Monoidal.map_tensor_assoc]
    rw [Monoidal.μ_δ, Category.comp_id]
    simp only [← Category.assoc]
    congr 1
    rw [← IsIso.eq_comp_inv]
    simp [tensorμ_comp_μ_tensorHom_μ_comp_μ]
  one_comul := by
    simp only [η_def, Δ_def, Category.assoc]
    simp only [← F.map_comp_assoc, one_comul]
    simp only [tensorObj.one_def, map_comp, Category.assoc, η_def]
    rw [Monoidal.map_tensor, Category.assoc, Category.assoc, Monoidal.μ_δ, Category.comp_id]
    rw [← tensorHom_comp_tensorHom]
    simp only [← Category.assoc]
    rw [@leftUnitor_inv_comp_tensorHom]
    simp only [Category.assoc, δ_natural, left_unitality F, Monoidal.whiskerRight_η_ε,
      Category.comp_id]
  mul_counit := by
    simp only [μ_def, ε_def, Category.assoc, Comon.tensorObj_counit]
    simp only [← F.map_comp_assoc, mul_counit]
    simp only [Comon.tensorObj_counit, map_comp, Category.assoc]
    rw [← tensorHom_comp_tensorHom, Monoidal.map_tensor]
    simp only [← Category.assoc, Monoidal.μ_δ, Category.id_comp]
    simp only [Category.assoc]
    rw [@Monoidal.map_leftUnitor_assoc]
    simp only [← Category.assoc, Monoidal.μ_δ, Category.id_comp]
    simp [tensorHom_def]
  one_counit := by
    simp only [η_def, ε_def, Category.assoc]
    simp only [← F.map_comp_assoc, one_counit]
    simp only [map_id, Category.id_comp, Monoidal.ε_η]

attribute [local instance] obj.instBimonObj

instance map.instIsBimon_Hom (F : C ⥤ D) [F.Braided] {X Y : C} [BimonObj X] [BimonObj Y]
    (f : X ⟶ Y) [IsBimonHom f] : IsBimonHom (F.map f) := ⟨⟩

/-- A monoidal functor takes bimonoid objects to bimonoid objects.

That is, a monoidal functor `F : C ⥤ D` induces a functor `Bimon' C ⥤ Bimon' D`.
-/
@[implicit_reducible, simps]
def mapBimon (F : C ⥤ D) [F.Braided] : Bimon' C ⥤ Bimon' D where
  obj A :=
    { X := F.obj A.X }
  map f :=
    { hom := F.map f.hom }
  map_id A := by ext; simp
  map_comp f g := by ext; simp

-- TODO We haven't yet set up the category structure on `OplaxMonoidalFunctor C D`
-- and so can't state `mapComonFunctor : OplaxMonoidalFunctor C D ⥤ Comon C ⥤ Comon D`.

example (F : C ⥤ D) [F.Braided] (X : Bimon' C) : μ[(F.mapBimon.obj X).X] =
  LaxMonoidal.μ F _ _ ≫ F.map μ[X.X] := by simp

end CategoryTheory.Functor

end Bimon'

-- #min_imports
