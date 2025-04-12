/- based on RingHom version -/

/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/

import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!

# Local algebra homomorphisms

We prove basic properties of local algebra homomorphisms.

-/

variable {R A B C : Type*}
section

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

-- not sure about the instance
@[instance 100]
theorem isLocalAlgHomof_isLocalHom_toRingHom
    (f : A →ₐ[R] B) [IsLocalHom f.toRingHom] : IsLocalHom f :=
  ⟨IsLocalHom.map_nonunit (f:= f.toRingHom)⟩

-- this might be bad
@[instance 100]
theorem isLocalHomof_isLocalAlgHom
    (f : A →ₐ[R] B) [IsLocalHom f] : IsLocalHom f.toRingHom :=
  ⟨IsLocalHom.map_nonunit (f:= f)⟩

@[instance]
theorem isLocalAlgHomid (X : Type*) [Semiring X] [Algebra R X] : IsLocalHom (AlgHom.id R X) where
  map_nonunit _ := id

-- see note [lower instance priority]
@[instance 100]
theorem isLocalAlgHomtoAlgHom {F : Type*} [FunLike F A B]
    [AlgHomClass F R A B] (f : F) [IsLocalHom f] : IsLocalHom (f : A →ₐ[R] B) :=
  ⟨IsLocalHom.map_nonunit (f := f)⟩

@[instance]
theorem AlgHom.isLocalHomcomp (g : B →ₐ[R] C) (f : A →ₐ[R] B) [IsLocalHom g]
    [IsLocalHom f] : IsLocalHom (g.comp f) where
  map_nonunit a := IsLocalHom.map_nonunit a ∘ IsLocalHom.map_nonunit (f := g) (f a)

theorem isLocalAlgHomof_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) [IsLocalHom (g.comp f)] :
    IsLocalHom f :=
  ⟨fun _ ha => (isUnit_map_iff (g.comp f) _).mp (g.isUnit_map ha)⟩

end
