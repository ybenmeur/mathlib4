/-
Copyright (c) 2026 Yacine Benmeuraiem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yacine Benmeuraiem
-/
module

public import Mathlib.Algebra.Category.AlgObj.Duality.Hopf_
public import Mathlib.Algebra.Category.AlgObj.FullFaithful.Hopf
public import Mathlib.Algebra.Category.AlgObj.HopfEquivalence
public import Mathlib.Algebra.Category.FGProj.FGProj

/-!
# Cartier duality for finite projective Hopf algebras

## Main definitions

* `CartierDual`

## Tags

Cartier duality, Hopf algebras

## Implementation details

We use a categorical point of view: Hopf algebras are Hopf monoids in the category of modules.
The duality functor on the subcategory of finite projective modules is monoidal braided
(i.e. the dual of a tensor product is isomorphic to the tensor product of the duals) and thus sends
Hopf monoids to Hopf monoids.

-/

@[expose] public section

universe v u

variable (R A : Type v) [CommRing R] [Ring A] [HopfAlgebra R A]
  [Module.Finite R A] [Module.Projective R A]


open FGModuleCat CategoryTheory Hopf

open TensorProduct Coalgebra MonObj ComonObj HopfObj BimonObj RingTheory.LinearMap HopfAlgCat

@[simps! -isSimp]
noncomputable abbrev toHopfFGProj : Hopf (FGProj R) :=
  letI : HopfObj (((isProjective R).ι ⋙ (ModuleCat.isFG R).ι).obj (FGProj.of R A)) :=
    (hopfEquivalence.functor.obj (HopfAlgCat.of R A)).hopf
  ((isProjective R).fullyFaithfulι.comp (ModuleCat.isFG R).fullyFaithfulι).hopf (FGProj.of R A)
  -- X := .of R A
  -- hopf :=
  --   ((isProjective R).fullyFaithfulι.comp (ModuleCat.isFG R).fullyFaithfulι).hopfObj _
  --     (h:=(hopfEquivalence.functor.obj (HopfAlgCat.of R A)).hopf)

noncomputable def toHopfFGProjMap (B : Type v) [Ring B] [HopfAlgebra R B] [Module.Finite R B]
  [Module.Projective R B] (f : A →ₐc[R] B) : toHopfFGProj R A ⟶ toHopfFGProj R B :=
  let : HopfObj (((isProjective R).ι ⋙ (ModuleCat.isFG R).ι).obj (FGProj.of R A)) :=
    (hopfEquivalence.functor.obj (HopfAlgCat.of R A)).hopf
  let : HopfObj (((isProjective R).ι ⋙ (ModuleCat.isFG R).ι).obj (FGProj.of R B)) :=
    (hopfEquivalence.functor.obj (HopfAlgCat.of R B)).hopf
  (((isProjective R).fullyFaithfulι.comp (ModuleCat.isFG R).fullyFaithfulι).hopfMap
    (FGProj.of R A) (FGProj.of R B)
    (hopfEquivalence.functor.map (HopfAlgCat.ofHom f)).hom.hom)

@[instance_reducible]
noncomputable def hopfFGProjDual : Hopf (FGProj R) ⥤ (Hopf (FGProj R))ᵒᵖ :=
  FGProj.dual.rightOp.mapHopf ⋙ hopf_equiv_opposite.inverse.rightOp

@[implicit_reducible]
noncomputable def ofFGProj : Hopf (FGProj R) ⥤ HopfAlgCat R :=
  ((isProjective R).ι ⋙ (ModuleCat.isFG R).ι).mapHopf ⋙ hopfEquivalence.inverse

def CartierDual : Type _ := Module.Dual R A

namespace CartierDual

noncomputable instance : Ring (CartierDual R A) :=
  ((((hopfFGProjDual R) ⋙ (ofFGProj R).op).obj (toHopfFGProj R A)).unop).instRing

noncomputable instance : HopfAlgebra R (CartierDual R A) :=
  ((ofFGProj R).obj (((hopfFGProjDual R).obj (toHopfFGProj R A))).unop).instHopfAlgebra

noncomputable def linearEquiv : CartierDual R A ≃ₗ[R] Module.Dual R A :=
  LinearEquiv.refl R (CartierDual R A)

variable {R A} in
/-- The identity as a type helper. -/
noncomputable abbrev toDual : CartierDual R A →ₗ[R] Module.Dual R A :=
  linearEquiv R A

noncomputable def linearEquivTensor :
  CartierDual R A ⊗[R] CartierDual R A ≃ₗ[R] Module.Dual R A ⊗[R] Module.Dual R A :=
 LinearEquiv.refl R _

variable {R A} in
/-- The identity as a type helper. -/
noncomputable abbrev toDualTensor :
  CartierDual R A ⊗[R] CartierDual R A →ₗ[R] Module.Dual R A ⊗[R] Module.Dual R A :=
 linearEquivTensor R A

open RingTheory.LinearMap in
lemma toDualTensor_eq_tensorHom : toDualTensor (R:=R) (A:=A) = toDual ⊗ₘ toDual := by
  ext
  rfl

section operations

/-!
### Describing the operations on the Cartier dual of `A` using the operations of `A`
-/

@[simp]
lemma mul_def {f g : CartierDual R A} (x : A) :
    (f * g).toDual x = ((dualDistrib R A A) (f.toDual ⊗ₜ[R] g.toDual)) (δ x) := rfl

section onelemmas
private lemma mon_one_def : η[((hopfFGProjDual R).obj (toHopfFGProj R A)).unop.X] =
    (Functor.OplaxMonoidal.η _).unop ≫
    (FGProj.dual.rightOp.map ε[(toHopfFGProj R A).X]).unop := rfl

private lemma one_eq_mon_one : (1 : CartierDual R A).toDual =
    η[((hopfFGProjDual R).obj (toHopfFGProj R A)).unop.X].hom.hom.hom 1 := rfl
end onelemmas

-- attribute [local implicit_reducible] ModuleCat.isFG

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
lemma one_def : (1 : CartierDual R A).toDual = (ε : A →ₗ[R] R) := by
  rw [one_eq_mon_one]
  rw [mon_one_def]
  simp only [ObjectProperty.tensorUnit_obj, ModuleCat.MonoidalCategory.tensorUnit_carrier,
    ← obj_carrier, Functor.rightOp.η_def,
    Quiver.Hom.unop_op, Functor.FullyFaithful.comonObj_counit, Functor.comp_obj,
    ObjectProperty.ι_obj, Functor.LaxMonoidal.comp_ε, ObjectProperty.ι_ε, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.id_hom, Category.comp_id, Functor.FullyFaithful.comp_preimage,
    Functor.rightOp_map, ObjectProperty.homMk_hom, ObjectProperty.FullSubcategory.comp_hom,
    FGProj.ε_hom, hom_ofHom, ModuleCat.hom_comp, ConcreteCategory.hom_ofHom, LinearMap.coe_comp,
    Function.comp_apply]
  -- rw [FGModuleCat.hom_ofHom] -- mysterious erw
  ext
  rw [LinearMap.dualMap_apply]
  simp [hopfEquivalence.hom_counit_eq_counit]
  rfl

section comullemmas
private lemma dualDistrib_δ (x : Module.Dual R (A ⊗[R] A)) : dualDistrib R A A
    ((Functor.OplaxMonoidal.δ ((FGProj.dual (R := R)))
    (Opposite.op (toHopfFGProj R A).X) (Opposite.op (toHopfFGProj R A).X)).hom.hom.hom x) = x := by
  have := IsIso.inv_hom_id (Functor.LaxMonoidal.μ ((FGProj.dual (R := R)))
    (Opposite.op (.of R A)) (Opposite.op (.of R A)))
  exact congr(($this).hom.hom.hom x)

private lemma comul_eq_dual_mul : Δ[((hopfFGProjDual R).obj (toHopfFGProj R A)).unop.X] =
  (FGProj.dual.rightOp.map μ[(toHopfFGProj R A).X]).unop ≫
  (Functor.LaxMonoidal.μ ((FGProj.dual (R := R)).rightOp) _ _).unop := by
  rfl

private lemma coalgebra_comul_eq_comon_comul (f : CartierDual R A) :
    toDualTensor (Coalgebra.comul (R:=R) f) =
  Δ[((hopfFGProjDual R).obj (toHopfFGProj R A)).unop.X].hom.hom.hom f.toDual :=
  rfl
end comullemmas

@[simp]
lemma comul_def (f : CartierDual R A) (x y : A) :
    (dualDistrib R A A) (toDualTensor (δ f)) (x ⊗ₜ y) = f.toDual (x * y) := by
  rw [coalgebra_comul_eq_comon_comul]
  rw [comul_eq_dual_mul]
  simp only [Functor.FullyFaithful.monObj_mul, Functor.FullyFaithful.comp_preimage,
    Functor.rightOp_map, Quiver.Hom.unop_op, ObjectProperty.homMk_hom, ModuleCat.hom_comp,
    Functor.rightOp.μ_def, ObjectProperty.FullSubcategory.comp_hom, hom_ofHom,
    ConcreteCategory.hom_ofHom, LinearMap.coe_comp, Function.comp_apply]
  rw [dualDistrib_δ]
  rw [LinearMap.dualMap_apply]
  rw [hopfEquivalence.hom_mul_eq_mul']
  simp

section coonelemmas
private lemma asIso_ε_eq : asIso (Functor.LaxMonoidal.ε (FGProj.dual (R:=R))) =
    (LinearMap.ringLmapEquivSelf R R R).symm.toFGProjIso := by
  ext
  rfl
private lemma η_def : (Functor.OplaxMonoidal.η (FGProj.dual (R:=R))).hom.hom =
    (LinearMap.ringLmapEquivSelf R R R).toModuleIso.hom := by
  rw [← Functor.Monoidal.inv_ε]
  rw [← asIso_inv, asIso_ε_eq]
  rfl

private lemma comon_counit_def : ε[((hopfFGProjDual R).obj (toHopfFGProj R A)).unop.X] =
  (FGProj.dual.rightOp.map η[(toHopfFGProj R A).X]).unop ≫
  (Functor.LaxMonoidal.ε (FGProj.dual (R:=R)).rightOp).unop := by
  rfl

private lemma counit_eq_comon_counit (f : CartierDual R A) : ε f =
    ε[((hopfFGProjDual R).obj (toHopfFGProj R A)).unop.X].hom.hom.hom f.toDual := rfl
end coonelemmas

@[simp]
lemma counit_def (f : CartierDual R A) :
    ε f = f.toDual 1 := by
  rw [counit_eq_comon_counit]
  rw [comon_counit_def]
  rw [Functor.rightOp.ε_def]
  simp only [Quiver.Hom.unop_op, ObjectProperty.FullSubcategory.comp_hom]
  rw [η_def]
  simp only [Functor.rightOp_obj, Functor.FullyFaithful.monObj_one,
    Functor.FullyFaithful.comp_preimage, Functor.rightOp_map, Quiver.Hom.unop_op,
    ObjectProperty.homMk_hom, ModuleCat.hom_comp, FGProj.hom_ofHom, hom_ofHom,
    LinearEquiv.toModuleIso_hom, ConcreteCategory.hom_ofHom, LinearEquiv.coe_coe,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.ringLmapEquivSelf_apply]
  rw [hopfEquivalence.hom_one_eq_algebra_linearMap]
  rw [LinearMap.dualMap_apply]
  simp

open HopfAlgebra in
@[simp]
lemma antipode_def (f : CartierDual R A) (x : A) :
    (antipode R f).toDual x = f.toDual (antipode R x):= rfl

end operations

noncomputable def map (B : Type v) [Ring B] [HopfAlgebra R B] [Module.Finite R B]
    [Module.Projective R B] (f : A →ₐc[R] B) : CartierDual R B →ₐc[R] CartierDual R A :=
  (((hopfFGProjDual R) ⋙ (ofFGProj R).op).map (toHopfFGProjMap R A B f)).unop.toBialgHom

instance : Module.Finite R (CartierDual R A) :=
  inferInstanceAs <| Module.Finite R (Module.Dual R A)

instance : Module.Projective R (CartierDual R A) :=
  inferInstanceAs <| Module.Projective R (Module.Dual R A)

section nattransbraided

#check Functor.Braided
#check NatTrans.IsMonoidal

variable {C D : Type*} [Category* C] [MonoidalCategory C] [Category* D] [MonoidalCategory D]
    {F G : C ⥤ D} (n : F ⟶ G) (X : C)

attribute [local instance] Functor.monObjObj in
instance isMonHom_monoidalNatTrans_app [F.LaxMonoidal] [G.LaxMonoidal] [n.IsMonoidal] [MonObj X] :
    IsMonHom (n.app X) where
  one_hom := by simp
  mul_hom := by simp only [Functor.obj.μ_def, Category.assoc, NatTrans.naturality,
    NatTrans.IsMonoidal.tensor_assoc]

def NatTrans.mapMon [F.LaxMonoidal] [G.LaxMonoidal] [n.IsMonoidal] : F.mapMon ⟶ G.mapMon where
  app _ := .mk (n.app _)

-- maybe there could be `NatTrans.IsLaxMonoidal` (current def or add `counit` and `cotensor`)
-- and `NatTrans.IsOplaxMonoidal`?
open MonoidalCategory in
@[reassoc (attr := simp)]
lemma NatTrans.IsMonoidal.counit [F.Monoidal] [G.Monoidal] [n.IsMonoidal] : n.app (𝟙_ C) ≫
  Functor.OplaxMonoidal.η G = Functor.OplaxMonoidal.η F := by simp [← Functor.Monoidal.inv_ε]

open MonoidalCategory in
@[reassoc (attr := simp)]
lemma NatTrans.IsMonoidal.cotensor [F.Monoidal] [G.Monoidal] [n.IsMonoidal] (X Y) :
    n.app (X ⊗ Y) ≫ Functor.OplaxMonoidal.δ G _ _ =
    Functor.OplaxMonoidal.δ F _ _ ≫ (n.app X ⊗ₘ n.app Y) := by simp [← Functor.Monoidal.inv_μ]

attribute [local instance] Functor.obj.instComonObj in
instance isComonHom_monoidalNatTrans_app [F.Monoidal] [G.Monoidal] [n.IsMonoidal] [ComonObj X] :
    IsComonHom (n.app X) where
  hom_counit := by simp [← NatTrans.naturality_assoc]
  hom_comul := by simp [← NatTrans.naturality_assoc]

def NatTrans.mapComon [F.Monoidal] [G.Monoidal] [n.IsMonoidal] : F.mapComon ⟶ G.mapComon where
  app _ := .mk (n.app _)

attribute [local instance] Functor.obj.instBimonObj in
instance isBimonHom_monoidalNatTrans_app [BraidedCategory C] [BraidedCategory D] [F.Braided]
    [G.Braided] [n.IsMonoidal] [BimonObj X] : IsBimonHom (n.app X) where

def NatTrans.mapBimon [BraidedCategory C] [BraidedCategory D] [F.Braided] [G.Braided]
    [n.IsMonoidal] : F.mapBimon ⟶ G.mapBimon where
  app _ := .mk (n.app _)

def NatTrans.mapHopf [BraidedCategory C] [BraidedCategory D] [F.Braided] [G.Braided]
    [n.IsMonoidal] : F.mapHopf ⟶ G.mapHopf where
  app _ := Hopf.homMk (n.app _)

end nattransbraided

@[simp]
noncomputable def nattrans : unopUnop (FGProj R) ≅ FGProj.dual.op ⋙ FGProj.dual :=
  NatIso.ofComponents (fun A ↦ (Module.evalEquiv R A.unop.unop.obj).toFGProjIso)

instance : (nattrans R).hom.IsMonoidal where
  unit := by
    ext
    simp
    sorry
  tensor _ _ := by
    ext
    simp
    sorry

noncomputable def bidualLinearEquiv : A ≃ₗ[R] CartierDual R (CartierDual R A) :=
  Module.evalEquiv R A

-- a monoidal natural iso between braided functors gives a natural iso on the Hopf categories
noncomputable def bidualBialgEquiv : A ≃ₐc[R] CartierDual R (CartierDual R A) where
  __ := bidualLinearEquiv R A
  counit_comp := sorry
  map_comp_comul := sorry
  map_mul' := sorry

end CartierDual

-- #min_imports
