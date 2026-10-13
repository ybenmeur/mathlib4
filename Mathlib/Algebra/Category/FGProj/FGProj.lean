/-
Copyright (c) 2026 Yacine Benmeuraiem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yacine Benmeuraiem
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Subcategory

/-! The category of finite projective modules -/

@[expose] public section

universe v u

variable (R : Type u) [CommRing R]

open CategoryTheory

namespace FGModuleCat

abbrev isProjective : ObjectProperty (FGModuleCat.{v} R) := fun X ↦ Module.Projective R X

instance : (isProjective R).IsMonoidal where
  prop_unit := inferInstanceAs (Module.Projective R R)
  prop_tensor _ _ hM hN := Module.Projective.tensorProduct (hM:=hM) (hN:=hN)

abbrev FGProj := (isProjective.{v} R).FullSubcategory

namespace FGProj

variable (X : FGProj R)
-- #synth Module R X.obj
-- #synth Module.Finite R X.obj
instance : Module.Projective R X.obj := X.property
-- #synth Module.Projective R X.obj

abbrev of (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [h : Module.Projective R M] : FGProj R := ⟨FGModuleCat.of R M, h⟩

variable {R} in
/-- Lift a linear map between finitely generated modules to `FGModuleCat R`. -/
abbrev ofHom {V W : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [hpV : Module.Projective R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W] [hpW : Module.Projective R W]
    (f : V →ₗ[R] W) : of R V ⟶ of R W := ⟨FGModuleCat.ofHom f⟩

-- #check LinearEquiv.toFGModuleCatIso

-- variable {R} in
-- /-- Converts an isomorphism in the category `FGModuleCat R` to
-- a `LinearEquiv` between the underlying modules. -/
-- def isoToLinearEquiv {V W : FGProj.{v} R} (i : V ≅ W) : V ≃ₗ[R] W :=
--   ((forget₂ (FGProj.{v} R) (ModuleCat.{v} R)).mapIso i).toLinearEquiv

variable {R} in
/-- Converts a `LinearEquiv` to an isomorphism in the category `FGModuleCat R`. -/
@[simps]
def _root_.LinearEquiv.toFGProjIso
    {V W : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Projective R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Projective R W] (e : V ≃ₗ[R] W) :
    FGProj.of R V ≅ FGProj.of R W where
  hom := ConcreteCategory.ofHom e.toLinearMap
  inv := ConcreteCategory.ofHom e.symm.toLinearMap
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x

variable {R} in
@[simps -isSimp]
abbrev dual : (FGProj R)ᵒᵖ ⥤ FGProj R where
  obj X := of R (Module.Dual R X.unop.obj)
  -- ⟨FGModuleCat.of R (Module.Dual R X.unop.obj), Module.dual_projective⟩
  map f := ofHom f.unop.hom.hom.hom.dualMap
  map_id _ := rfl
  map_comp _ _ := rfl
      -- ObjectProperty.hom_ext (isProjective R)
      --   (hom_ext (LinearMap.dualMap_comp_dualMap _ _))

@[simp low]
lemma dual_obj {X : (FGProj R)ᵒᵖ} :
    (dual.obj X).obj = Module.Dual R X.unop.obj := rfl

@[simp]
lemma dual_map_hom_hom_hom {X Y : (FGProj R)ᵒᵖ} (f : X ⟶ Y) :
    (dual.map f).hom.hom.hom = f.unop.hom.hom.hom.dualMap := rfl

open TensorProduct
-- #check TensorProduct.dualDistrib
-- #check Module.Projective.tensorProduct

#check FGModuleCat.tensorObj_obj

variable {R} in
/-- Lift a linear map between finitely generated modules to `FGModuleCat R`. -/
@[simp]
lemma _root_.FGModuleCat.hom_ofHom {V W : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W]
    (f : V →ₗ[R] W) : (FGModuleCat.ofHom f).hom = ModuleCat.ofHom f := rfl

section dualDistrib
lemma dualDistrib_assoc_symm (R M N P : Type*) [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [AddCommMonoid P] [Module R P] :
    dualDistrib R _ _ ∘ₗ (dualDistrib R _ _).rTensor _ ∘ₗ
      (TensorProduct.assoc R _ _ _).symm.toLinearMap =
    (TensorProduct.assoc R M N P).toLinearMap.dualMap ∘ₗ dualDistrib R _ _ ∘ₗ
      (dualDistrib R _ _).lTensor _ := by
  ext
  simp [mul_assoc]

lemma dualDistrib_assoc (R M N P : Type*) [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [AddCommMonoid P] [Module R P] :
    dualDistrib R _ _ ∘ₗ (dualDistrib R _ _).rTensor _=
    (TensorProduct.assoc R M N P).toLinearMap.dualMap ∘ₗ dualDistrib R _ _ ∘ₗ
      (dualDistrib R _ _).lTensor _  ∘ₗ
      (TensorProduct.assoc R _ _ _).toLinearMap := by
  ext
  simp [mul_assoc]

lemma dualDistrib_assoc' (R M N P : Type*) [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [AddCommMonoid P] [Module R P] :
    (TensorProduct.assoc R M N P).symm.toLinearMap.dualMap ∘ₗ dualDistrib R _ _ ∘ₗ
      (dualDistrib R _ _).rTensor _ = dualDistrib R _ _ ∘ₗ (dualDistrib R _ _).lTensor _ ∘ₗ
        (TensorProduct.assoc R _ _ _).toLinearMap := by
  ext
  simp [mul_assoc]

open Module in
lemma dualDistrib_assoc'_apply {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [AddCommMonoid P] [Module R P] (f : Dual R M ⊗[R] Dual R N ⊗[R] Dual R P) :
    (TensorProduct.assoc R M N P).symm.dualMap (dualDistrib R _ _
      ((dualDistrib R _ _).rTensor _ f)) = dualDistrib R _ _ ((dualDistrib R _ _).lTensor _
        ((TensorProduct.assoc R _ _ _) f)) :=
  congr($(dualDistrib_assoc' R M N P) f)

open Module in
lemma dualDistrib_assoc_symm_apply {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [AddCommMonoid P] [Module R P] (x : Dual R M ⊗[R] (Dual R N ⊗[R] Dual R P)) :
  (dualDistrib R (M ⊗[R] N) P)
    ((LinearMap.rTensor (Dual R P) (dualDistrib R M N))
      ((TensorProduct.assoc R (Dual R M) (Dual R N) (Dual R P)).symm x)) =
  ((TensorProduct.assoc R M N P)).dualMap
    ((dualDistrib R M (N ⊗[R] P)) ((LinearMap.lTensor (Dual R M) (dualDistrib R N P)) x)) :=
  congr($(dualDistrib_assoc_symm R M N P) x)

open Module in
lemma dualDistrib_assoc_apply {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [AddCommMonoid P] [Module R P] (x : Dual R M ⊗[R] Dual R N ⊗[R] Dual R P) :
  (dualDistrib R (M ⊗[R] N) P)
    ((LinearMap.rTensor (Dual R P) (dualDistrib R M N)) x) =
  ((TensorProduct.assoc R M N P)).dualMap
    ((dualDistrib R M (N ⊗[R] P)) ((LinearMap.lTensor (Dual R M) (dualDistrib R N P))
      ((TensorProduct.assoc R (Dual R M) (Dual R N) (Dual R P)) x))) :=
  congr($(dualDistrib_assoc R M N P) x)
end dualDistrib

-- set_option backward.defeqAttrib.useBackward true in
-- set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance : (dual (R:=R)).LaxMonoidal where -- this is true in ModuleCat as well
  ε := ofHom ((LinearMap.ringLmapEquivSelf R R R).symm) -- unfortunately this is not good defeq
  μ X Y := ofHom (dualDistrib R X.unop.obj Y.unop.obj)
  μ_natural_left {X Y} f Z := by
    ext f : 3
    induction f using TensorProduct.inductionOn
    · apply TensorProduct.ext'
      intro x y
      rfl
    · simp_all only [map_add]
  μ_natural_right {X Y} f Z := by
    ext f : 3
    induction f using TensorProduct.inductionOn
    · apply TensorProduct.ext'
      intro x y
      rfl
    · simp_all only [map_add]
  associativity X Y Z := by
    ext f : 3
    exact dualDistrib_assoc'_apply f
  left_unitality X := by
    ext f : 3
    -- simp [ModuleCat.hom_hom_leftUnitor, ModuleCat.hom_inv_leftUnitor, ModuleCat.hom_whiskerRight]
    induction f using TensorProduct.inductionOn
    · apply LinearMap.ext
      intro x
      simp only [ObjectProperty.tensorObj_obj, ObjectProperty.tensorUnit_obj,
        ObjectProperty.leftUnitor_def, ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom,
        ModuleCat.hom_hom_leftUnitor, LinearEquiv.coe_coe, unop_tensorUnit,
        ObjectProperty.whiskerRight_def, hom_ofHom, unop_tensorObj, obj_carrier,
        unop_hom_leftUnitor, ObjectProperty.isoMk_inv, ModuleCat.hom_inv_leftUnitor,
        ObjectProperty.FullSubcategory.comp_hom, ModuleCat.hom_comp, ConcreteCategory.hom_ofHom,
        ModuleCat.hom_whiskerRight, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.dualMap_apply, lid_symm_apply]
      rw [TensorProduct.lid_tmul, LinearMap.rTensor_tmul, dualDistrib_apply]
      erw [LinearMap.lsmul_apply]
      simp only [smul_eq_mul, Module.End.one_apply, one_mul, LinearMap.smul_apply]
    · simp_all only [map_add]
  right_unitality X := by
    ext f : 3
    -- simp [ModuleCat.hom_hom_leftUnitor, ModuleCat.hom_inv_leftUnitor, ModuleCat.hom_whiskerRight]
    induction f using TensorProduct.inductionOn
    · apply LinearMap.ext
      intro x
      simp only [ObjectProperty.tensorObj_obj, ObjectProperty.tensorUnit_obj,
        ObjectProperty.rightUnitor_def, ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom,
        ModuleCat.hom_hom_rightUnitor, LinearEquiv.coe_coe, unop_tensorUnit,
        ObjectProperty.whiskerLeft_def, hom_ofHom, unop_tensorObj, obj_carrier,
        unop_hom_rightUnitor, ObjectProperty.isoMk_inv, ObjectProperty.FullSubcategory.comp_hom,
        ModuleCat.hom_comp, ConcreteCategory.hom_ofHom, ModuleCat.hom_whiskerLeft,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.dualMap_apply,
        ModuleCat.MonoidalCategory.rightUnitor_inv_apply]
      rw [TensorProduct.rid_tmul, LinearMap.lTensor_tmul, dualDistrib_apply]
      erw [LinearMap.lsmul_apply]
      simp only [smul_eq_mul, Module.End.one_apply, mul_one, LinearMap.smul_apply, mul_comm]
    · simp_all only [map_add]

@[simp]
lemma dual_μ_hom_hom_hom (X Y : (FGProj R)ᵒᵖ) :
    (Functor.LaxMonoidal.μ dual X Y).hom.hom.hom = dualDistrib R X.unop.obj Y.unop.obj := rfl

lemma _root_.CategoryTheory.ObjectProperty.braiding_def {C : Type u} [Category.{v, u} C]
    [MonoidalCategory C]
    (P : ObjectProperty C) [P.IsMonoidal] [BraidedCategory C] {X Y : P.FullSubcategory} :
    β_ X Y = P.isoMk (β_ X.1 Y.1) := rfl

-- set_option allowUnsafeReducibility true
-- attribute [local reducible] FGModuleCat.carrier

-- lemma ModuleCat.MonoidalCategory.β_hom_hom {R : Type u} [CommRing R] (X Y : ModuleCat R) :
--     (β_ X Y).hom.hom = (TensorProduct.comm R X Y).toLinearMap := rfl

-- lemma ModuleCat.MonoidalCategory.β_inv_hom {R : Type u} [CommRing R] (X Y : ModuleCat R) :
--     (β_ X Y).inv.hom = (TensorProduct.comm R X Y).symm.toLinearMap := rfl

@[simp]
lemma _root_.CategoryTheory.ObjectProperty.braiding_hom_hom {C : Type*} [Category C]
    [MonoidalCategory C] (P : ObjectProperty C) [P.IsMonoidal] [BraidedCategory C]
    (X Y : P.FullSubcategory) : (β_ X Y).hom.hom = (β_ X.obj Y.obj).hom := rfl

@[simp]
lemma _root_.CategoryTheory.ObjectProperty.braiding_inv_hom {C : Type*} [Category C]
    [MonoidalCategory C] (P : ObjectProperty C) [P.IsMonoidal] [BraidedCategory C]
    (X Y : P.FullSubcategory) : (β_ X Y).inv.hom = (β_ X.obj Y.obj).inv := rfl

lemma dualDistrib_bijective (M N : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
  [Module.Projective R M] [AddCommGroup N] [Module R N] [Module.Finite R N]
  [Module.Projective R N] : Function.Bijective (dualDistrib R M N) := sorry

@[simp]
noncomputable def dualDistribEquiv' (M N : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.Projective R N] :
    Module.Dual R M ⊗[R] Module.Dual R N ≃ₗ[R] Module.Dual R (M ⊗[R] N) :=
  .ofBijective (dualDistrib R M N) (dualDistrib_bijective R M N)

-- set_option backward.isDefEq.respectTransparency false in
instance : (dual (R:=R)).LaxBraided where -- this is true in ModuleCat as well
  braided X Y := by
    ext1
    ext1
    apply TensorProduct.ext'
    intro f g
    apply TensorProduct.ext'
    intro x y
    simp only [obj_carrier, unop_tensorObj, ObjectProperty.tensorObj_obj, unop_hom_braiding,
      ObjectProperty.FullSubcategory.comp_hom, hom_ofHom, ModuleCat.hom_comp,
      ConcreteCategory.hom_ofHom, dual_μ_hom_hom_hom, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.dualMap_apply]
    simp only [_root_.CategoryTheory.ObjectProperty.braiding_hom_hom]
    rw [ModuleCat.MonoidalCategory.braiding_hom_apply]
    rw [ModuleCat.MonoidalCategory.braiding_hom_apply]
    rw [dualDistrib_apply, dualDistrib_apply, mul_comm]

noncomputable def coreMonoidal : (dual (R:=R)).CoreMonoidal where
  εIso := (LinearMap.ringLmapEquivSelf R R R).symm.toFGProjIso
  μIso X Y := (dualDistribEquiv' R X.unop.obj Y.unop.obj).toFGProjIso
  μIso_hom_natural_left := (instLaxMonoidalOppositeDual R).μ_natural_left
  μIso_hom_natural_right := (instLaxMonoidalOppositeDual R).μ_natural_right
  associativity := (instLaxMonoidalOppositeDual R).associativity
  left_unitality := (instLaxMonoidalOppositeDual R).left_unitality
  right_unitality := (instLaxMonoidalOppositeDual R).right_unitality

noncomputable instance : (dual (R:=R)).OplaxMonoidal := (coreMonoidal R).toOplaxMonoidal
noncomputable instance : (dual (R:=R)).Monoidal := (coreMonoidal R).toMonoidal
noncomputable instance : (dual (R:=R)).Braided where

end FGProj

end FGModuleCat
