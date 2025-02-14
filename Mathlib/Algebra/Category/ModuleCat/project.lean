import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.RepresentationTheory.FDRep

/-!
# Tannaka duality for finite groups

Given a field `k` and a finite group `G`, Tannaka duality expresses the fact that one can recover
`G` from the monoidal category `FDRep k G` of finite dimensional representations of `G` over `k`.

More specifically, we consider the monoidal forgetful functor `F k G : FDRep k G ⥤ ModuleCat k`
to the category of vector spaces over `k`, and `Aut (F k G)` its group of automorphisms, i.e. the
group of monoidal natural isomorphisms `(F k G) ⟹ (F k G)`. We further construct the group
homomorphism `T : G →* Aut (F k G)` defined by `T g ⟨V, ρ⟩ := ρ g`.

The theorem `tannaka_duality` states that `T` is an isomorphism.

The proof revolves around one particular representation `τᵣ` on `G → k` induced by multiplication
on the right in `G`.

## Mathematical notations

- `F` : monoidalforgetful functor `FDRep k G ⥤ Vect k`
- `T` : the morphism `G →* Aut (F k G)` given by `T g ⟨V, ρ⟩ = ρ g` that is shown to be bijective
- `e s` : indicator function of `s` on `G → k` (i.e. `e s t = 1 ↔ s = t`)
  (abbreviation for `Pi.single s (1 : k)` in mathlib)
- `τᵣ` : representation on `G → k` given by `τᵣ s f t = f (t * s)` (multiplication on the right)
- `α` : map sending a natural transformation `η : F ⟹ F` to its `τᵣ` component

## Reference

<https://math.leidenuniv.nl/scripties/1bachCommelin.pdf>
-/

noncomputable section

open CategoryTheory MonoidalCategory

universe u

variable (k G : Type u)

section forget

variable [CommRing k] [Monoid G] (X : FDRep k G)

instance : (forget₂ (FDRep k G) (FGModuleCat k)).Monoidal := by
  change (Action.forget _ _).Monoidal
  infer_instance

/-- The monoidal forgetful functor from `FDRep k G` to `FGModuleCat k` -/
def F := LaxMonoidalFunctor.of (forget₂ (FDRep k G) (FGModuleCat k))

lemma F_μ {X Y : FDRep k G} :
  Functor.LaxMonoidal.μ (F k G).toFunctor X Y = 𝟙 _ := rfl

end forget

variable [Field k]

section T

variable {k G} [Group G] (η : Aut (F k G))

@[simp]
theorem ρ_inv_self_apply {A : FDRep k G} (g : G) (x : A) :
    A.ρ g⁻¹ (A.ρ g x) = x :=
  show (A.ρ g⁻¹ * A.ρ g) x = x by rw [← map_mul, inv_mul_cancel, map_one, LinearMap.one_apply]

@[simp]
theorem ρ_self_inv_apply {A : FDRep k G} (g : G) (x : A) :
    A.ρ g (A.ρ g⁻¹ x) = x :=
  show (A.ρ g * A.ρ g⁻¹) x = x by rw [← map_mul, mul_inv_cancel, map_one, LinearMap.one_apply]

/-- Definition of `T g : Aut (F k G)` by its components -/
@[simps]
def T_app (g : G) (X : FDRep k G) : X.V ≅ X.V where
  hom := ModuleCat.ofHom (X.ρ g)
  inv := ModuleCat.ofHom (X.ρ g⁻¹)
  hom_inv_id := by
    ext x
    exact ρ_inv_self_apply g x
  inv_hom_id := by
    ext x
    exact ρ_self_inv_apply g x

/-- The function defining `T` -/
def T_fun : G → Aut (F k G) := by
  intro g
  apply LaxMonoidalFunctor.isoOfComponents (T_app g) ?_ rfl (by intros; rfl)
  intro _ _ f
  exact (f.comm g).symm

lemma T_apply (g : G) (X : FDRep k G) :
    ((T_fun g).hom.hom.app X).hom = X.ρ g := rfl

variable (k G) in
/-- The group homomorphism `G →* Aut (F k G)` involved in the main theorem -/
def T : G →* Aut (F k G) where
  toFun := T_fun
  map_one' := by
    ext
    simp only [T_apply, map_one]
    exact rfl
  map_mul' := by
    intros
    ext
    simp only [T_apply, map_mul]
    exact rfl

end T

section Indicator

variable {k} {G : Type u} [DecidableEq G]

/-- Indicator function of `s : G` -/
abbrev e (s : G) : G → k := Pi.single s (1 : k)

lemma e_eq_same (s : G) : e s s = (1 : k) := Pi.single_eq_same s 1

lemma e_eq_of_ne {s t : G} (h : s ≠ t) : e s t = (0 : k) := Pi.single_eq_of_ne' h 1

lemma eq_of_e_eq_one {s t : G} (h : e s t = (1 : k)) : s = t := by
  by_contra
  simp_all only [ne_eq, not_false_eq_true, Pi.single_eq_of_ne', zero_ne_one]

lemma mul_e (s : G) (f : G → k) : (e s) * f = f s • (e s) := by
    ext t
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h : s = t
    · rw [h]
      exact mul_comm _ _
    · rwa [e_eq_of_ne, zero_mul, mul_zero]

lemma e_mul_self (s : G) : (e s) * (e s) = ((e s) : G → k) := by
  ext
  rw [mul_e, e_eq_same, one_smul]

lemma e_eq_iff (s t u v : G) : (e s t = (e u v : k)) ↔ (s = t ↔ u = v) := by
  have e_eq {s t u v : G} (h : e s t = (e u v : k)) : s = t → u = v := by
    intro
    simp_all only [Pi.single_eq_same]
    exact eq_of_e_eq_one h.symm
  constructor
  · intro h
    exact ⟨e_eq h, e_eq h.symm⟩
  · intro h
    by_cases h' : s = t
    · rw [h', e_eq_same, h.mp h', e_eq_same]
    · rw [e_eq_of_ne h', e_eq_of_ne (h' ∘ h.mpr)]

lemma e_right_mul [Group G] (s t u : G) :
    e t (u * s) = (e (t * s⁻¹) u : k) := by
  simp only [e_eq_iff]
  exact mul_inv_eq_iff_eq_mul.symm

end Indicator

variable {k G} [Group G]

section fdRepτᵣ

/-- The representation on `G → k` induced by multiplication on the right in `G` -/
def τᵣ : Representation k G (G → k) where
  toFun s := {
    toFun f := fun t ↦ f (t * s)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  }
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp [mul_assoc]

lemma τᵣ_apply (s : G) (f : G → k) (t : G) : τᵣ s f t = f (t * s) := rfl

/-- The representation on `G → k` induced by multiplication on the left in `G` -/
def τₗ : Representation k G (G → k) where
  toFun s := {
    toFun f := fun t ↦ f (s⁻¹ * t)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  }
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp [mul_assoc]

lemma τₗ_apply (s : G) (f : G → k) (t : G) : τₗ s f t = f (s⁻¹ * t) := rfl

variable [Fintype G]

variable (k G) in
/-- The representation `⟨G → k, τᵣ⟩` induced by multiplication on
the right in `G` as a `FDRep k G` -/
def fdRepτᵣ : FDRep k G := FDRep.of τᵣ

variable (k G) in
/-- The representation `⟨G → k, τₗ⟩` induced by multiplication on
  the left in `G` as a `FDRep k G` -/
def fdRepτₗ : FDRep k G := FDRep.of τₗ

/-- Map sending `η : Aut (F k G)` to its component at `fdRepτᵣ k G` as a linear map -/
def α (η : Aut (F k G)) : (G → k) →ₗ[k] (G → k) := (η.hom.hom.app (fdRepτᵣ k G)).hom

end fdRepτᵣ

variable [DecidableEq G] [Fintype G]

section lemma4

-- *lemma 4.4*
lemma T_inj : Function.Injective (T k G) := by
  rw [injective_iff_map_eq_one]
  intro s h
  apply_fun α at h
  replace h : (e 1) (1 * s) = e 1 1 := congrFun (congrFun (congrArg DFunLike.coe h) (e 1)) 1
  rw [e_eq_same, one_mul] at h
  exact (eq_of_e_eq_one h).symm

end lemma4

section lemma5

-- *lemma 4.5*
/-- An algebra morphism `φ : (G → k) →ₐ[k] k` is an evaluation map. -/
lemma eval_of_alghom {G : Type u} [DecidableEq G] [Fintype G] (φ : (G → k) →ₐ[k] k) :
    ∃ (s : G), φ = Pi.evalAlgHom _ _ s := by
  have h1 := map_one φ
  obtain ⟨s, hs⟩ : ∃ (s : G), φ (e s) ≠ 0 := by
    rw [← Finset.univ_sum_single (1 : G → k)] at h1
    by_contra
    simp_all
  have h2 : φ (1 - (e s)) = 0 := by
    apply eq_zero_of_ne_zero_of_mul_right_eq_zero hs
    rw [← map_mul]
    convert map_zero φ
    rw [mul_sub_right_distrib, one_mul, e_mul_self, sub_self]
  have h3 : φ (e s) = 1 := by
    rw [map_sub, h1, sub_eq_zero] at h2
    exact h2.symm
  use s
  ext f
  conv_lhs => rw [← one_mul (φ f), ← h3, ← map_mul]
  rw [Pi.evalAlgHom_apply, mul_e, map_smul, smul_eq_mul, h3, mul_one]

end lemma5

section lemma6

/-- The `FDRep k G` morphism induced by multiplication on `G → k`. -/
def μ : fdRepτᵣ k G ⊗ fdRepτᵣ k G ⟶ fdRepτᵣ k G where
  hom := ModuleCat.ofHom (LinearMap.mul' k (G → k))
  comm := by
    intro (_ : G)
    ext (u : TensorProduct k (G → k) (G → k))
    refine TensorProduct.induction_on u rfl (fun _ _ ↦ rfl) ?_
    intro _ _ hx hy
    simp only [map_add, hx, hy]

/-- For `η : Aut (F k G)`, `α η` preserves multiplication -/
def map_mul_α (η : Aut (F k G)) :
    ∀ (x y : G → k), (α η) (x * y) = ((α η) x) * ((α η) y) := by
  intro f g
  have a := η.hom.hom.naturality μ
  have b := η.hom.isMonoidal.tensor
  simp only [F_μ, Category.id_comp, Category.comp_id] at b
  rw [b] at a
  apply_fun ModuleCat.Hom.hom at a
  exact (congrFun (congrArg DFunLike.coe a) (f ⊗ₜ[k] g))

-- *lemma 4.6*
/-- `α η` is an algebra morphism, for `η : Aut (F k G)` -/
def algHomOfα (η : Aut (F k G)) : ((G → k)) →ₐ[k] ((G → k)) := by
  refine AlgHom.ofLinearMap (α η) ?_ (map_mul_α η)
  let α_inv : (G → k) → (G → k) := (η.inv.hom.app (fdRepτᵣ k G)).hom
  have := η.inv_hom_id
  apply_fun LaxMonoidalFunctor.Hom.hom at this
  apply_fun NatTrans.app at this
  replace := congrFun this (fdRepτᵣ k G)
  apply_fun ModuleCat.Hom.hom at this
  have : (α η) (α_inv 1) = (1 : G → k) := congrFun (congrArg DFunLike.coe this) (1 : G → k)
  have h := this
  rwa [← one_mul (α_inv 1), map_mul_α, h, mul_one] at this

end lemma6

section lemma7

/-- `τₗ` commutes with `τᵣ`, so it is a representation morphism of `fdRepτᵣ` -/
def τₗfdRepHom (s : G) : (fdRepτᵣ k G) ⟶ (fdRepτᵣ k G) where
  hom := ModuleCat.ofHom (τₗ s)
  comm := by
    intro (t : G)
    ext (f : G → k)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, Rep.ρ_hom, LinearMap.coe_comp,
      Function.comp_apply]
    rw [funext_iff]
    intro u
    change (τₗ s) ((τᵣ t) f) u = (τᵣ t) ((τₗ s) f) u
    simp only [τₗ_apply, τᵣ_apply, mul_assoc]

-- *lemma 4.7*
lemma image_α_in_image_τᵣ (η : Aut (F k G)) : ∃ (s : G), α η = τᵣ s := by
  have hnat (t : G) := η.hom.hom.naturality (τₗfdRepHom t)
  let α_hom := algHomOfα η
  obtain ⟨s, hs⟩ := eval_of_alghom ((Pi.evalAlgHom _ _ (1 : G)).comp α_hom)
  use s
  have (u t : G) : α_hom (e u) t = e (t⁻¹ * u) s := by
    specialize hnat t⁻¹
    apply_fun ModuleCat.Hom.hom at hnat
    calc
      _ = α_hom (e u) ((t⁻¹)⁻¹ * 1) := by
        rw [mul_one, inv_inv]
      _ = τₗ t⁻¹ (α_hom (e u)) 1 := rfl
      _ = α_hom (τₗ t⁻¹ (e u)) 1 :=
        congrFun (congrFun (congrArg DFunLike.coe hnat) (e u)).symm 1
      _ = (Pi.evalAlgHom _ _ 1).comp α_hom (τₗ t⁻¹ (e u)) := rfl
      _ = Pi.evalAlgHom _ _ s (τₗ t⁻¹ (e u)) :=
        congrFun (congrArg DFunLike.coe hs) _
      _ = _ := by
        rw [Pi.evalAlgHom_apply, τₗ_apply, e_eq_iff]
        exact eq_inv_mul_iff_mul_eq
  apply Basis.ext (Pi.basisFun k G)
  intro u
  simp only [Pi.basisFun_apply, funext_iff]
  intro t
  change α_hom _ _ = _
  rw [τᵣ_apply, this, e_eq_iff]
  exact inv_mul_eq_iff_eq_mul

end lemma7

section lemma8

/-- Auxiliary map for the proof of `α_inj` -/
def φ {X : FDRep k G} (v : X) : (G → k) →ₗ[k] X where
  toFun := fun f ↦ ∑ s : G, (f s) • (X.ρ s⁻¹ v)
  map_add' := by
    intros
    simp only [Pi.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' := by
    intros
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

lemma φ_apply {k G : Type u} [Field k] [Group G] [Fintype G] {X : FDRep k G} (v : X) (f : G → k) :
  (φ v) f = ∑ s : G, f s • (X.ρ s⁻¹) v := rfl

lemma φ_e_one_eq_id {X : FDRep k G} (v : X) : (φ v) (e 1) = v := by
  rw [φ_apply]
  let a (s : G) : X.V := (e (1 : G) s : k) • (X.ρ s⁻¹) v
  calc
    _ = (∑ s ∈ {1}ᶜ, a s) + a 1 :=
      Fintype.sum_eq_sum_compl_add _ _
    _ = a 1 := by
      apply add_left_eq_self.mpr
      apply Finset.sum_eq_zero
      simp_all only [Finset.mem_compl, Finset.mem_singleton, ne_eq, not_false_eq_true,
        Pi.single_eq_of_ne, zero_smul, implies_true, a]
    _ = _ := by
      simp only [Pi.single_eq_same, inv_one, map_one, LinearMap.one_apply, one_smul, a]

/-- Auxiliary representation morphism for the proof of `α_inj` -/
@[simps]
def φRepMor (X : FDRep k G) (v : X) : (fdRepτᵣ k G) ⟶ X where
  hom := ModuleCat.ofHom (φ v)
  comm := by
    intro (t : G)
    ext (f : G → k)
    change (φ v) (τᵣ t f) = X.ρ t (φ v f)
    simp only [φ_apply, map_sum]
    set φ_term := fun (X : FDRep k G) (f : G → k) (v s) ↦ (f s) • (X.ρ s⁻¹ v)
    have := Finset.sum_map Finset.univ (mulRightEmbedding t⁻¹) (φ_term X (τᵣ t f) v)
    simp only [φ_term, Finset.univ_map_embedding] at this
    rw [this]
    apply Finset.sum_congr rfl
    simp [τᵣ_apply, mul_assoc]

-- *lemma 4.8*
/-- If `η₁ η₂ : Aut (F k G)` agree on `fdRepτᵣ` then they are equal -/
lemma α_inj (η₁ η₂ : Aut (F k G))
    (h : η₁.hom.hom.app (fdRepτᵣ k G) = η₂.hom.hom.app (fdRepτᵣ k G)) : η₁ = η₂ := by
  ext X v
  have h1 := congrArg ModuleCat.Hom.hom (η₁.hom.hom.naturality (φRepMor X v))
  have h2 := η₂.hom.hom.naturality (φRepMor X v)
  rw [h, ← h2] at h1
  apply_fun (· (e 1)) at h1
  change (η₁.hom.hom.app X).hom ((φ v) (e 1)) = (η₂.hom.hom.app X).hom ((φ v) (e 1)) at h1
  simp [φ_e_one_eq_id] at h1
  exact h1

end lemma8

section prop11

-- *proposition 4.11*
lemma T_surj : Function.Surjective (T k G) := by
  intro η
  obtain ⟨s, h⟩ := image_α_in_image_τᵣ η
  use s
  apply α_inj
  apply ModuleCat.hom_ext
  exact h.symm

end prop11

section thm

-- *theorem 4.3*
theorem tannaka_duality : Function.Bijective (T k G) :=
  ⟨T_inj, T_surj⟩

example : G ≃* Aut (F k G) :=
  MulEquiv.ofBijective (T k G) tannaka_duality

end thm
