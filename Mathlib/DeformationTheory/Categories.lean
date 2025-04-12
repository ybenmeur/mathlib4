import Mathlib.DeformationTheory.InverseLimit
import Mathlib.DeformationTheory.IsResidueAlgebra
import Mathlib.DeformationTheory.LocalAlgebras
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.HopkinsLevitzki

universe u v

open CategoryTheory IsLocalRing Deformation

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] [IsLocalRing Λ]
variable (A : LocalAlg Λ)

structure isArtinResidueAlg : Prop where
  [isArtinian : IsArtinianRing A]
  [isResidueAlgebra : IsResidueAlgebra Λ A]

variable (Λ) in
def ArtinLocalAlg := FullSubcategory (isArtinResidueAlg (Λ := Λ))

abbrev obj := fun n ↦ A ⧸ (maximalIdeal A) ^ n

instance (n) : Nontrivial (A ⧸ (maximalIdeal A) ^ (n + 1)) := by
  apply Ideal.Quotient.nontrivial
  refine ne_top_of_le_ne_top ?_ (Ideal.pow_le_pow_right (Nat.le_add_left 1 n))
  rw [pow_one]
  exact Ideal.IsPrime.ne_top'

def func {i j} (h : i ≤ j) : obj A j →ₐ[Λ] obj A i := by
  refine Ideal.Quotient.liftₐ _ (Ideal.Quotient.mkₐ _ _) ?_
  intro a ha
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact (Ideal.pow_le_pow_right (by linarith)) ha

abbrev proLimit := Algebra.InverseLimit (func A)

example (a : proLimit A) {i j} (h : i ≤ j) : (func A h) (a.val j) = a.val i := by
  simp [func, -Algebra.InverseLimit.prop]

omit [IsNoetherianRing Λ] [IsLocalRing Λ] in
@[simp]
lemma proLimit.prop (a : proLimit A) {i j} (h : i ≤ j) {thing} :
    Ideal.Quotient.lift _ (Ideal.Quotient.mkₐ Λ _).toRingHom thing (a.val j) = a.val i :=
  a.prop _ _ h

def inj : A →ₐ[Λ] proLimit A := by
  apply Algebra.InverseLimit.map_of_maps (func A) (fun _ ↦ Ideal.Quotient.mkₐ _ _)
  simp [func]

omit [IsNoetherianRing Λ] [IsLocalRing Λ] in
@[simp]
lemma inj_apply (a n) : (inj A a).val n = a := rfl

omit [IsNoetherianRing Λ] [IsLocalRing Λ] in
lemma inj_inj [IsNoetherianRing A] : Function.Injective (inj A) := by
  rw [@injective_iff_map_eq_zero]
  intro a ha
  rw [← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal A) Ideal.IsPrime.ne_top', Ideal.mem_iInf]
  intro n
  apply_fun fun x ↦ x.val n at ha
  simp at ha
  exact Ideal.Quotient.eq_zero_iff_mem.mp ha

def LocalAlg.isComplete := Function.Surjective (inj A)

lemma isComplete_of_artinian [IsArtinianRing A] : A.isComplete := by
  rw [LocalAlg.isComplete]
  obtain ⟨n, hn⟩ : ∃ n, maximalIdeal A ^ n = ⊥ := by
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
    use n
    rw [← jacobson_eq_maximalIdeal]
    · assumption
    · exact Ne.symm top_ne_bot
  intro y
  use Quotient.out (y.val n)
  ext i
  by_cases h : i ≤ n
  · sorry
  · sorry

structure isProArtinResidueAlg : Prop where
  [isNoetherian : IsNoetherianRing A]
  [isComplete : LocalAlg.isComplete A]
  [isProLimit : ∀ n, isArtinResidueAlg (.of Λ (obj A (n + 1)))]

variable (Λ) in
def ProArtinResidueAlg := FullSubcategory (isProArtinResidueAlg (Λ := Λ))

-- maybe bad defs?
lemma inclusion : isArtinResidueAlg A → isProArtinResidueAlg A := by
  rintro ⟨a, b⟩
  have : IsNoetherianRing A := inferInstance
  have : LocalAlg.isComplete A := sorry
  have : ∀ n, isArtinResidueAlg (.of Λ (obj A (n + 1))) := by
    intro n
    have : IsArtinianRing (obj A (n + 1)) := inferInstance
    have : IsResidueAlgebra Λ (obj A (n + 1)) := inferInstance
    tauto
  (expose_names; exact { isNoetherian := this_1, isComplete := this_2, isProLimit := this })
