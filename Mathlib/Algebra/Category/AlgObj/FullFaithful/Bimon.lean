/-
Copyright (c) 2026 Yacine Benmeuraiem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yacine Benmeuraiem
-/
module

public import Mathlib.Algebra.Category.AlgObj.FullFaithful.Mon
public import Mathlib.Algebra.Category.AlgObj.FullFaithful.Comon
public import Mathlib.CategoryTheory.Monoidal.Bimon_

/-! A fully faithful braided functor can lift bimonoid objects -/

@[expose] public section

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalCategory D] [BraidedCategory D] (F : C ⥤ D) [F.Full] [F.Faithful]
    [F.Braided] (X : C)
-- #check CategoryTheory.MonoidalCategory.tensorμ_comp_μ_tensorHom_μ_comp_μ
/-! If `F` is a fully faithful braided functor, and `F.obj X` admits a bimonoid object
structure, then there is a natural bimonoid object structure on `X`. -/
@[implicit_reducible]
noncomputable def bimonobj_of_bimonobj_obj [BimonObj (F.obj X)] : BimonObj X where
  __ := F.monobj_of_monobj_obj X
  __ := F.comonobj_of_comonobj_obj X
  mul_comul := by
    apply F.map_injective
    simp only [map_comp, monobj_of_monobj_obj_map_mul, comonobj_of_comonobj_obj_map_comul,
      Category.assoc, BimonObj.mul_comul_assoc]
    rw [CategoryTheory.Functor.Monoidal.map_tensor]
    rw [CategoryTheory.Functor.Monoidal.map_tensor]
    simp only [comonobj_of_comonobj_obj_map_comul, monobj_of_monobj_obj_map_mul, Category.assoc]
    rw [← MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [← CategoryTheory.MonoidalCategory.tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc F X X X X]
    simp only [Monoidal.μ_δ_assoc, MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  one_comul := by
    apply F.map_injective
    simp only [map_comp, monobj_of_monobj_obj_map_one, comonobj_of_comonobj_obj_map_comul,
      Category.assoc, BimonObj.one_comul_assoc, Mon.one_def]
    rw [Monoidal.map_tensor, Monoidal.map_leftUnitor_inv]
    simp only [monobj_of_monobj_obj_map_one, Category.assoc, Monoidal.μ_δ_assoc]
    rw [← MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [MonoidalCategory.whiskerRight_comp_tensorHom_assoc]
    rw [Monoidal.ε_η]
    simp only [MonoidalCategory.id_tensorHom, MonoidalCategory.id_whiskerLeft,
      LaxMonoidal.left_unitality, Category.assoc, LaxMonoidal.left_unitality_inv_assoc,
      Iso.inv_hom_id_map_assoc]
  mul_counit := by
    apply F.map_injective
    simp only [map_comp, monobj_of_monobj_obj_map_mul, comonobj_of_comonobj_obj_map_counit,
      Category.assoc, BimonObj.mul_counit_assoc, Comon.tensorObj_counit]
    rw [Monoidal.map_tensor]
    simp only [comonobj_of_comonobj_obj_map_counit, Category.assoc]
    rw [Monoidal.map_leftUnitor]
    simp only [LaxMonoidal.left_unitality, Monoidal.whiskerRight_η_ε_assoc, Monoidal.δ_μ_assoc]
    rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
    congr 2
    rw [Monoidal.map_leftUnitor]
    rw [Monoidal.μ_δ_assoc]
    rw [MonoidalCategory.tensorHom_comp_whiskerRight_assoc]
    rw [Monoidal.ε_η]
    simp only [MonoidalCategory.id_tensorHom, MonoidalCategory.id_whiskerLeft,
      LaxMonoidal.left_unitality, Category.assoc, LaxMonoidal.left_unitality_inv_assoc,
      Iso.inv_hom_id_map, Category.comp_id]
  one_counit := by
    apply F.map_injective
    simp

section FullyFaithful

variable {F}

/-- Pullback a bimonoid object along a fully faithful braided functor. -/
@[simps]
abbrev FullyFaithful.bimonObj (hF : F.FullyFaithful) (X : C) [BimonObj (F.obj X)] : BimonObj X where
  __ := hF.monObj X
  __ := hF.comonObj X
  mul_comul := by
    apply F.map_injective
    simp only [map_comp, monObj_mul, comonObj_comul, map_preimage,
      Category.assoc, BimonObj.mul_comul_assoc]
    rw [CategoryTheory.Functor.Monoidal.map_tensor]
    rw [CategoryTheory.Functor.Monoidal.map_tensor]
    simp only [map_preimage, Category.assoc]
    rw [← MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [← CategoryTheory.MonoidalCategory.tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc F X X X X]
    simp only [Monoidal.μ_δ_assoc, MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  one_comul := by
    apply F.map_injective
    simp only [map_preimage, map_comp, monObj_one, comonObj_comul,
      Category.assoc, BimonObj.one_comul_assoc, Mon.one_def]
    rw [Monoidal.map_tensor, Monoidal.map_leftUnitor_inv]
    simp only [map_preimage, Category.assoc, Monoidal.μ_δ_assoc]
    rw [← MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [MonoidalCategory.whiskerRight_comp_tensorHom_assoc]
    rw [Monoidal.ε_η]
    simp only [MonoidalCategory.id_tensorHom, MonoidalCategory.id_whiskerLeft,
      LaxMonoidal.left_unitality, Category.assoc, LaxMonoidal.left_unitality_inv_assoc,
      Iso.inv_hom_id_map_assoc]
  mul_counit := by
    apply F.map_injective
    simp only [map_preimage, map_comp, monObj_mul, comonObj_counit,
      Category.assoc, BimonObj.mul_counit_assoc, Comon.tensorObj_counit]
    rw [Monoidal.map_tensor]
    simp only [map_preimage, Category.assoc]
    rw [Monoidal.map_leftUnitor]
    simp only [LaxMonoidal.left_unitality, Monoidal.whiskerRight_η_ε_assoc, Monoidal.δ_μ_assoc]
    rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
    congr 2
    rw [Monoidal.map_leftUnitor]
    rw [Monoidal.μ_δ_assoc]
    rw [MonoidalCategory.tensorHom_comp_whiskerRight_assoc]
    rw [Monoidal.ε_η]
    simp only [MonoidalCategory.id_tensorHom, MonoidalCategory.id_whiskerLeft,
      LaxMonoidal.left_unitality, Category.assoc, LaxMonoidal.left_unitality_inv_assoc,
      Iso.inv_hom_id_map, Category.comp_id]
  one_counit := by
    apply F.map_injective
    simp

end FullyFaithful

end CategoryTheory.Functor

-- #min_imports
