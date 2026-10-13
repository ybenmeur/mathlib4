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

/-! Cartier duality for finite projective Hopf algebras -/

@[expose] public section

universe v u

variable (R A : Type v) [CommRing R] [Ring A] [HopfAlgebra R A]
  [Module.Finite R A] [Module.Projective R A]


open FGModuleCat CategoryTheory Hopf

open TensorProduct Coalgebra MonObj ComonObj HopfObj BimonObj

-- #synth HasForget₂ (FGProj R) (ModuleCat R)
@[simp]
def toFGProj : FGProj R := .of R A

@[simp]
noncomputable def toHopfModuleCat : Hopf (ModuleCat R) :=
  hopfEquivalence.functor.obj (HopfAlgCat.of R A)

@[simps]
noncomputable def toHopfFGProj : Hopf (FGProj R) where
  X := toFGProj R A
  hopf :=
    ((isProjective R).fullyFaithfulι.comp (ModuleCat.isFG R).fullyFaithfulι).hopfObj _
      (h:=(toHopfModuleCat R A).hopf)


@[simp]
noncomputable def hopfFGProjDual : Hopf (FGProj R) ⥤ (Hopf (FGProj R))ᵒᵖ :=
  FGProj.dual.rightOp.mapHopf ⋙ hopf_equiv_opposite.inverse.rightOp

@[simp]
noncomputable def hopfFGProjDual' : Hopf (FGProj R) ⥤ (HopfAlgCat R)ᵒᵖ :=
  hopfFGProjDual R ⋙
  (((isProjective R).ι ⋙ (ModuleCat.isFG R).ι).mapHopf ⋙ hopfEquivalence.inverse).op

@[simp]
def CartierDual : Type _ := Module.Dual R A

namespace CartierDual

@[simp]
noncomputable instance : Ring (CartierDual R A) :=
  (((hopfFGProjDual' R).obj (toHopfFGProj R A))).unop.instRing

@[simp]
noncomputable instance : HopfAlgebra R (CartierDual R A) :=
  ((hopfFGProjDual' R).obj (toHopfFGProj R A)).unop.instHopfAlgebra

-- @[simp]
noncomputable def linearEquiv : CartierDual R A ≃ₗ[R] Module.Dual R A :=
  LinearEquiv.refl R (CartierDual R A)

variable {R A} in
-- @[simp]
noncomputable abbrev toDual : CartierDual R A →ₗ[R] Module.Dual R A :=
  linearEquiv R A

open TensorProduct Coalgebra RingTheory.LinearMap in
@[simp]
lemma mul_def {f g : CartierDual R A} (x : A) :
    (f * g).toDual x = ((dualDistrib R A A) (f.toDual ⊗ₜ[R] g.toDual)) (δ x) := rfl


open TensorProduct Coalgebra RingTheory.LinearMap in
@[simp]
lemma one_def : (1 : CartierDual R A).toDual = (ε : _ →ₗ[R] _) := by
  have : (counit : A →ₗ[R] R).dualMap
    ((LinearMap.ringLmapEquivSelf R R R).symm 1) = (counit : A →ₗ[R] R) := by
    ext
    simp
  rw [← this]
  rfl

open TensorProduct RingTheory.LinearMap Coalgebra in
@[simp]
example (f : CartierDual R A) : Coalgebra.comul (R:=R) f =
  Δ[((hopfFGProjDual R).obj (toHopfFGProj R A)).unop.X].hom.hom.hom f :=
  rfl

open TensorProduct Coalgebra RingTheory.LinearMap in
@[simp]
lemma comul_def' (f : CartierDual R A) :
    (toDual ⊗ₘ toDual) (δ f) =
    (FGProj.dualDistribEquiv' R _ _).symm ((LinearMap.mul' R A).dualMap f.toDual) := by
  have : (toDual (R:=R) (A:=A)) ⊗ₘ (toDual (R:=R) (A:=A)) = LinearMap.id := by
    ext
    rfl
  rw [this]
  rfl

open TensorProduct Coalgebra RingTheory.LinearMap in
@[simp]
lemma comul_def (f : CartierDual R A) (x y : A) :
  (dualDistrib R A A) ((toDual ⊗ₘ toDual) (δ f)) (x ⊗ₜ y) =
  f.toDual (x * y) := by
  rw [comul_def']
  simp

open TensorProduct Coalgebra RingTheory.LinearMap in
@[simp]
lemma counit_def (f : CartierDual R A) :
    ε f = f.toDual 1 := by
  rw [← map_one (algebraMap R A)]
  rfl

open HopfAlgebra in
@[simp]
lemma antipode_def (f : CartierDual R A) (x : A) :
  (antipode R f).toDual x = f.toDual (antipode R x):= rfl

instance : Module.Finite R (CartierDual R A) :=
  inferInstanceAs <| Module.Finite R (Module.Dual R A)

instance : Module.Projective R (CartierDual R A) :=
  inferInstanceAs <| Module.Projective R (Module.Dual R A)

noncomputable def bidualLinearEquiv : A ≃ₗ[R] CartierDual R (CartierDual R A) :=
  Module.evalEquiv R A

-- a (braided?) natural iso between braided functors gives a natural iso on the Hopf categories
noncomputable def bidualBialgEquiv : A ≃ₐc[R] CartierDual R (CartierDual R A) where
  __ := bidualLinearEquiv R A
  counit_comp := sorry
  map_comp_comul := sorry
  map_mul' := sorry

variable (B : Type v) [Ring B] [HopfAlgebra R B] [Module.Finite R B] [Module.Projective R B]

-- everything is functorial (the only part missing is FullyFaithful)
def map (f : A →ₐc[R] B) : CartierDual R B →ₐc[R] CartierDual R A := sorry

end CartierDual

-- #min_imports
