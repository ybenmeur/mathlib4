/-
Copyright (c) 2026 Yacine Benmeuraiem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yacine Benmeuraiem
-/
module

public import Mathlib.Algebra.Category.AlgObj.Duality.Bimon_
public import Mathlib.Algebra.Category.AlgObj.Hopf'

/-! # Hopf objects in opposite category -/

@[expose] public section

open CategoryTheory MonObj ComonObj BimonObj HopfObj Opposite

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]

@[implicit_reducible, simps! (isSimp := false)]
instance CategoryTheory.Hopf.hopfObjOp (X : C) [HopfObj X] : HopfObj (op X) where
  __ := CategoryTheory.BimonObj.bimonObjOp X
  antipode := antipode.op
  antipode_left := by
    apply Quiver.Hom.unop_inj
    simp [monObjOp_mul, comonObjOp_comul, monObjOp_one, comonObjOp_counit]
  antipode_right := by
    apply Quiver.Hom.unop_inj
    simp [monObjOp_mul, comonObjOp_comul, monObjOp_one, comonObjOp_counit]

@[implicit_reducible, simps! (isSimp := false)]
instance CategoryTheory.Hopf.hopfObjUnop (X : Cᵒᵖ) [HopfObj X] : HopfObj X.unop where
  __ := CategoryTheory.BimonObj.bimonObjUnop X
  antipode := antipode.unop
  antipode_left := by
    apply Quiver.Hom.op_inj
    simp [monObjUnop_mul, comonObjUnop_comul, monObjUnop_one, comonObjUnop_counit]

  antipode_right := by
    apply Quiver.Hom.op_inj
    simp [monObjUnop_mul, comonObjUnop_comul, monObjUnop_one, comonObjUnop_counit]

@[implicit_reducible, simps! (isSimp := false)]
def CategoryTheory.Hopf.of_hopfObjOp (X : C) [HopfObj (Opposite.op X)] : HopfObj X where
  __ := CategoryTheory.op_instances.BimonObj.of_bimonObjOp X
  antipode := antipode.unop
  antipode_left := by
    apply Quiver.Hom.op_inj
    simp only [hopfObjUnop_comul, hopfObjUnop_mul, op_comp, op_tensorObj, Quiver.Hom.op_unop,
      op_whiskerRight, Category.assoc, antipode_left, hopfObjUnop_counit, hopfObjUnop_one,
      op_tensorUnit]
  antipode_right := by
    apply Quiver.Hom.op_inj
    simp only [hopfObjUnop_comul, hopfObjUnop_mul, op_comp, op_tensorObj, Quiver.Hom.op_unop,
      op_whiskerLeft, Category.assoc, antipode_right, hopfObjUnop_counit, hopfObjUnop_one,
      op_tensorUnit]

@[implicit_reducible, simps (isSimp := false)]
def hopf_equiv_opposite : Hopf C ≌ (Hopf Cᵒᵖ)ᵒᵖ where
  functor := {
    obj X := op ⟨op X.X⟩
    map f := op (Hopf.Hom.mk f.hom.op)
    map_id _ := rfl
    map_comp _ _ := rfl
  }
  inverse := {
    obj X := ⟨X.unop.X.unop⟩
    map f := Hopf.Hom.mk f.unop.hom.unop
    map_id _ := rfl
    map_comp _ _ := rfl
  }
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := Category.comp_id _ -- not nice
