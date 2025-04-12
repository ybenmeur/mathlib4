/- base from FLT -/

import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Inverse limit of modules, abelian groups, rings.

See Atiyah-Macdonald PP.32-33, Matsumura PP.269-270

## Main definitions

* `Module.InverseLimit obj f`
* `Ring.InverseLimit obj f`
* `Group.InverseLimit obj f`
* `Representation.InverseLimit obj f`
-/

variable {ι : Type*} [Preorder ι]
variable {obj : ι → Type*}

namespace Algebra

variable {R : Type*} [CommSemiring R]
variable [∀ i : ι, Semiring (obj i)] [∀ i : ι, Algebra R (obj i)]
variable (func : ∀ {i j}, i ≤ j → obj j →ₐ[R] obj i)

---- maybe can be defined with the InverseSystem that is in Mathlib
/-- The inverse limit of an inverse system is the Algebras glued together along the maps. -/
def InverseLimit := { a : Π i : ι, obj i | ∀ (i j : _) (h : i ≤ j), func h (a j) = a i }

def InverseLimit.subalgebra : Subalgebra R (Π i : ι, obj i) where
  carrier := InverseLimit func
  mul_mem' := by rw [InverseLimit]; aesop
  add_mem' := by rw [InverseLimit]; aesop
  algebraMap_mem' := by rw [InverseLimit]; aesop

instance : Semiring (InverseLimit func) :=
  (InverseLimit.subalgebra func).toSemiring

instance : Algebra R (InverseLimit func) :=
  (InverseLimit.subalgebra func).algebra

namespace InverseLimit

instance instCoeOutPi : CoeOut (InverseLimit func) ((i : ι) → obj i) where
  coe a := a.val

variable {func} in
@[simp]
lemma prop (a : InverseLimit func) :
  ∀ (i j : _) (h : i ≤ j), func h (a.val j) = a.val i := a.prop

variable {func} in
abbrev of (a : (i : ι) → obj i) (h :  ∀ i j (h : i ≤ j), func h (a j) = a i)
    : InverseLimit func := ⟨a, h⟩

@[simp]
lemma algebraMap_eq_piFun (r) :
    (algebraMap R (InverseLimit func) r).val = (fun _ ↦ algebraMap _ _ r) := rfl

-- instance : Inhabited (InverseLimit func) :=
  -- ⟨0⟩

def toComponent (i) : InverseLimit func →ₐ[R] obj i where
  toFun z := z.val i
  map_one' := by aesop
  map_mul' := by aesop
  map_zero' := by aesop
  map_add' := by aesop
  commutes' := by aesop

variable {R' : Type*} [Semiring R'] [Algebra R R']

def map_of_maps (maps : (i : ι) → R' →ₐ[R] obj i)
    (comm : ∀ r' i j (h : i ≤ j), (func h) ((maps j) r') = (maps i) r')
    : R' →ₐ[R] InverseLimit func where
      toFun r := ⟨fun i ↦ maps i r, by aesop⟩
      map_one' := by aesop
      map_mul' := by aesop
      map_zero' := by aesop
      map_add' := by aesop
      commutes' := by aesop

@[simp]
lemma map_of_maps_apply (maps : (i : ι) → R' →ₐ[R] obj i) (comm) (r i) :
    (map_of_maps func maps comm r).val i = maps i r := rfl

end InverseLimit

end Algebra
