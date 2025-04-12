/- modified from CommAlg from Toric varieties -/

/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.AlgHom.Basic

/-!
# Category of local commutative algebras over a commutative ring

We introduce the bundled category `LocalAlg` of algebras over a fixed commutative ring `R` along
with the forgetful functors to `RingCat` and `ModuleCat`. We furthermore show that the functor
associating to a type the free `R`-algebra on that type is left adjoint to the forgetful functor.
-/

open CategoryTheory Limits

universe v u

variable {R : Type u} [CommRing R]

variable (R) in
/-- The category of R-algebras and their morphisms. -/
structure LocalAlg where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [isRing : CommRing carrier]
  [isAlgebra : Algebra R carrier]
  [isLocalRing : IsLocalRing carrier]

attribute [instance] LocalAlg.isRing LocalAlg.isAlgebra LocalAlg.isLocalRing

initialize_simps_projections LocalAlg (-isRing, -isAlgebra)

namespace LocalAlg
variable {A B C : LocalAlg.{v} R}

instance : CoeSort (LocalAlg R) (Type v) := ⟨LocalAlg.carrier⟩

attribute [coe] LocalAlg.carrier

variable (R) in
/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `LocalAlg R`. -/
abbrev of (X : Type v) [CommRing X] [Algebra R X] [IsLocalRing X] : LocalAlg.{v} R := ⟨X⟩

variable (R) in
lemma coe_of (X : Type v) [CommRing X] [Algebra R X] [IsLocalRing X] : (of R X : Type v) = X := rfl

/-- The type of morphisms in `LocalAlg R`. -/
@[ext]
structure Hom (A B : LocalAlg.{v} R) where
  private mk ::
  /-- The underlying algebra map. -/
  hom' : A →ₐ[R] B
  [isLocalHom : IsLocalHom hom']

attribute [instance] Hom.isLocalHom

instance : Category (LocalAlg.{v} R) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

variable (R) in
@[ext]
structure LocalHom (A B : Type*) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [IsLocalRing A] [IsLocalRing B] where
  hom' : A →ₐ[R] B
  [isLocalHom : IsLocalHom hom']

attribute [instance] LocalHom.isLocalHom

instance (A B : Type*) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [IsLocalRing A] [IsLocalRing B] : FunLike (LocalHom R A B) A B where
  coe f := f.hom'
  coe_injective' := by
    intro a b c
    simp only [DFunLike.coe_fn_eq] at c
    exact LocalHom.ext c

instance : ConcreteCategory (LocalAlg.{v} R) (LocalHom R · ·) where
  hom f := ⟨f.hom'⟩
  ofHom f := Hom.mk f.hom'

/-- Turn a morphism in `LocalAlg` back into an `AlgHom`. -/
abbrev Hom.hom {A B : LocalAlg.{v} R} (f : Hom A B) := f.hom'

/-- Typecheck an `AlgHom` as a morphism in `LocalAlg`. -/
abbrev ofHom {A B : Type v} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [IsLocalRing A]
    [IsLocalRing B] (f : A →ₐ[R] B) [IsLocalHom f] : of R A ⟶ of R B := ⟨f⟩

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : LocalAlg.{v} R) (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp] lemma hom_id {A : LocalAlg.{v} R} : (𝟙 A : A ⟶ A).hom = AlgHom.id R A := rfl

/- Provided for rewriting. -/
lemma id_apply (A : LocalAlg.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a := by simp

@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf

@[simp]
lemma hom_ofHom {X Y : Type v} [CommRing X] [Algebra R X] [IsLocalRing X] [CommRing Y]
    [Algebra R Y] [IsLocalRing Y] (f : X →ₐ[R] Y) [IsLocalHom f]
    : (ofHom f).hom = f := rfl

@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type v} [CommRing X] [Algebra R X] [IsLocalRing X] :
    ofHom (AlgHom.id R X) = 𝟙 (of R X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type v} [CommRing X] [CommRing Y] [CommRing Z] [Algebra R X] [Algebra R Y]
    [Algebra R Z] [IsLocalRing X] [IsLocalRing Y] [IsLocalRing Z] (f : X →ₐ[R] Y) (g : Y →ₐ[R] Z)
    [IsLocalHom f] [IsLocalHom g] :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

lemma ofHom_apply {X Y : Type v} [CommRing X] [Algebra R X] [IsLocalRing X] [CommRing Y]
    [Algebra R Y] [IsLocalRing Y]
    (f : X →ₐ[R] Y) [IsLocalHom f] (x : X) : ofHom f x = f x := rfl

lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by simp [← comp_apply]

lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by simp [← comp_apply]

-- instance : Inhabited (LocalAlg R) := ⟨of R R⟩

lemma forget_obj (A : LocalAlg.{v} R) : (forget (LocalAlg.{v} R)).obj A = A := rfl

lemma forget_map (f : A ⟶ B) : (forget (LocalAlg.{v} R)).map f = f := rfl

instance {S : LocalAlg.{v} R} : Ring ((forget (LocalAlg R)).obj S) :=
  inferInstanceAs <| Ring S.carrier

instance {S : LocalAlg.{v} R} : Algebra R ((forget (LocalAlg R)).obj S) :=
  inferInstanceAs <| Algebra R S.carrier

instance hasForgetToCommRing : HasForget₂ (LocalAlg.{v} R) CommRingCat.{v} where
  forget₂.obj A := CommRingCat.of A
  forget₂.map f := CommRingCat.ofHom f.hom.toRingHom

instance hasForgetToModule : HasForget₂ (LocalAlg.{v} R) (ModuleCat.{v} R) where
  forget₂.obj M := ModuleCat.of R M
  forget₂.map f := ModuleCat.ofHom f.hom.toLinearMap

@[simp]
lemma forget₂_module_obj (X : LocalAlg.{v} R) :
    (forget₂ (LocalAlg.{v} R) (ModuleCat.{v} R)).obj X = ModuleCat.of R X := rfl

@[simp]
lemma forget₂_module_map {X Y : LocalAlg.{v} R} (f : X ⟶ Y) :
    (forget₂ (LocalAlg.{v} R) (ModuleCat.{v} R)).map f = ModuleCat.ofHom f.hom.toLinearMap := rfl

/-- Forgetting to the underlying type and then building the bundled object returns the original
algebra. -/
@[simps]
def ofSelfIso (M : LocalAlg.{v} R) : LocalAlg.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

end LocalAlg
