/-
Copyright (c) 2026 Yacine Benmeuraiem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yacine Benmeuraiem
-/
module

public import Mathlib.CategoryTheory.Monoidal.Bimon_
public import Mathlib.Algebra.Category.AlgObj.Bimon'

/-! # Monoid, comonoid, and bimonoid objects in opposite category -/

@[expose] public section

open CategoryTheory MonObj ComonObj BimonObj Opposite

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]

namespace CategoryTheory

section to_op

variable (X : C)

-- there is `MonOpOpToComonObj` in mathlib but for `X : Mon C`
@[implicit_reducible, simps (isSimp := false)]
instance MonObj.comonObjOp [MonObj X] : ComonObj (op X) where
  counit := one.op
  comul := mul.op
  counit_comul := Quiver.Hom.unop_inj (one_mul X)
  comul_counit := Quiver.Hom.unop_inj (mul_one X)
  comul_assoc := by
    apply Quiver.Hom.unop_inj
    simp

@[implicit_reducible, simps (isSimp := false)]
instance ComonObj.monObjOp [ComonObj X] : MonObj (op X) where
  one := counit.op
  mul := comul.op
  one_mul := Quiver.Hom.unop_inj (counit_comul X)
  mul_one := Quiver.Hom.unop_inj (comul_counit X)
  mul_assoc := by
    apply Quiver.Hom.unop_inj
    simp

@[implicit_reducible, simps! (isSimp := false)]
instance BimonObj.bimonObjOp [BimonObj X] : BimonObj (op X) where
  mul_comul := by
    apply Quiver.Hom.unop_inj
    simp [ComonObj.monObjOp_mul, MonObj.comonObjOp_comul]
  one_comul := Quiver.Hom.unop_inj (mul_counit X)
  mul_counit := Quiver.Hom.unop_inj (one_comul X)
  one_counit := Quiver.Hom.unop_inj (one_counit X)

end to_op

section from_op

variable (X : Cᵒᵖ)

-- there is `MonOpOpToComonObj` in mathlib but for `X : Mon C`
@[implicit_reducible, simps (isSimp := false)]
instance MonObj.comonObjUnop [MonObj X] : ComonObj (unop X) where
  counit := one.unop
  comul := mul.unop
  counit_comul := Quiver.Hom.op_inj (one_mul X)
  comul_counit := Quiver.Hom.op_inj (mul_one X)
  comul_assoc := by
    apply Quiver.Hom.op_inj
    simp

@[implicit_reducible, simps (isSimp := false)]
instance ComonObj.monObjUnop [ComonObj X] : MonObj (unop X) where
  one := counit.unop
  mul := comul.unop
  one_mul := by exact Quiver.Hom.op_inj (counit_comul X)
  mul_one := by exact Quiver.Hom.op_inj (comul_counit X)
  mul_assoc := by
    apply Quiver.Hom.op_inj
    simp

@[implicit_reducible, simps! (isSimp := false)]
instance BimonObj.bimonObjUnop [BimonObj X] : BimonObj X.unop where
  mul_comul := by
    apply Quiver.Hom.op_inj
    simp [ComonObj.monObjUnop_mul, MonObj.comonObjUnop_comul]
  one_comul := Quiver.Hom.op_inj (mul_counit X)
  mul_counit := Quiver.Hom.op_inj (one_comul X)
  one_counit := Quiver.Hom.op_inj (one_counit X)

end from_op

namespace op_instances

variable (X : C)

@[implicit_reducible, simps (isSimp := false)]
scoped instance ComonObj.of_monObjOp [MonObj (op X)] : ComonObj X where
  counit := one.unop
  comul := mul.unop
  counit_comul := Quiver.Hom.op_inj (one_mul (op X))
  comul_counit := Quiver.Hom.op_inj (mul_one (op X))
  comul_assoc := by
    apply Quiver.Hom.op_inj
    simp

@[implicit_reducible, simps (isSimp := false)]
scoped instance MonObj.of_comonObjOp [ComonObj (op X)] : MonObj X where
  one := counit.unop
  mul := comul.unop
  one_mul := by -- Quiver.Hom.op_inj (counit_comul (op X))
    apply Quiver.Hom.op_inj
    simp
  mul_one := by -- Quiver.Hom.op_inj (comul_counit (op X))
    apply Quiver.Hom.op_inj
    simp
  mul_assoc := by
    apply Quiver.Hom.op_inj
    simp

@[implicit_reducible, simps! (isSimp := false)]
scoped instance BimonObj.of_bimonObjOp [BimonObj (op X)] : BimonObj X where
  __ := MonObj.of_comonObjOp X
  __ := ComonObj.of_monObjOp X
  mul_comul := by
    apply Quiver.Hom.op_inj
    simp [MonObj.of_comonObjOp_mul, ComonObj.of_monObjOp_comul]
  one_comul := Quiver.Hom.op_inj (mul_counit (op X))
  mul_counit := Quiver.Hom.op_inj (one_comul (op X))
  one_counit := Quiver.Hom.op_inj (one_counit (op X))

end op_instances

section homs

section to_op

variable {X Y : C} (f : X ⟶ Y)

instance [MonObj X] [MonObj Y] [IsMonHom f] : IsComonHom f.op where
  hom_counit := by
    apply Quiver.Hom.unop_inj
    simp [MonObj.comonObjOp_counit]
  hom_comul := by
    apply Quiver.Hom.unop_inj
    simp [MonObj.comonObjOp_comul]

instance [ComonObj X] [ComonObj Y] [IsComonHom f] : IsMonHom f.op where
  mul_hom := by
    apply Quiver.Hom.unop_inj
    simp [ComonObj.monObjOp_mul]
  one_hom := by
    apply Quiver.Hom.unop_inj
    simp [ComonObj.monObjOp_one]

instance [BimonObj X] [BimonObj Y] [IsBimonHom f] : IsBimonHom f.op := ⟨⟩

end to_op

section to_op

variable {X Y : Cᵒᵖ} (f : X ⟶ Y)

instance [MonObj X] [MonObj Y] [IsMonHom f] : IsComonHom f.unop where
  hom_counit := by
    apply Quiver.Hom.op_inj
    simp [MonObj.comonObjUnop_counit]
  hom_comul := by
    apply Quiver.Hom.op_inj
    simp [MonObj.comonObjUnop_comul]

instance [ComonObj X] [ComonObj Y] [IsComonHom f] : IsMonHom f.unop where
  mul_hom := by
    apply Quiver.Hom.op_inj
    simp [ComonObj.monObjUnop_mul]
  one_hom := by
    apply Quiver.Hom.op_inj
    simp [ComonObj.monObjUnop_one]

instance [BimonObj X] [BimonObj Y] [IsBimonHom f] : IsBimonHom f.unop := ⟨⟩

end to_op

namespace op_instances

variable {X Y : C} (f : X ⟶ Y)

open ComonObj in
scoped instance IsComonHom.of_isMonHom_op [MonObj (op X)] [MonObj (op Y)] [IsMonHom f.op] :
    IsComonHom f where
  hom_counit := by
    apply Quiver.Hom.op_inj
    simp [of_monObjOp_counit]
  hom_comul := by
    apply Quiver.Hom.op_inj
    simp [of_monObjOp_comul]

open MonObj in
scoped instance IsMonHom.of_isComonHom_op [ComonObj (op X)] [ComonObj (op Y)] [IsComonHom f.op] :
    IsMonHom f where
  mul_hom := by
    apply Quiver.Hom.op_inj
    simp [of_comonObjOp_mul]
  one_hom := by
    apply Quiver.Hom.op_inj
    simp [of_comonObjOp_one]


open MonObj ComonObj BimonObj IsComonHom IsMonHom in
scoped instance [BimonObj (op X)] [BimonObj (op Y)] [IsBimonHom f.op] : IsBimonHom f := sorry -- ⟨⟩

end op_instances

end homs

def bimon'_equiv_opposite : Bimon' C ≌ (Bimon' Cᵒᵖ)ᵒᵖ where
  functor := {
    obj X := op ⟨op X.X⟩
    map f := op ⟨f.hom.op⟩
    map_id _ := rfl
    map_comp _ _ := rfl
  }
  inverse := {
    obj X := ⟨X.unop.X.unop⟩
    map f := ⟨f.unop.hom.unop⟩
    map_id _ := rfl
    map_comp _ _ := rfl
  }
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := Category.comp_id _ -- not nice

end CategoryTheory
