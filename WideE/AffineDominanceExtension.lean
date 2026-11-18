import WideE.JacobianDominance
import WideE.GenericFreeness
import WideE.BigCellCentralizer
import AlgebraicPointAvoidance
import Mathlib.RingTheory.Localization.InvSubmonoid
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.TensorProduct.Finite

/-! A principal open over the ground field on which all geometric
points lift, uniformly in the algebraically closed coefficient field. -/

noncomputable section

open scoped TensorProduct

namespace WideE

universe uΩ

section Morphisms

variable {k R S : Type*} [Field k] [CommRing R] [IsDomain R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra.FiniteType k S]

set_option maxHeartbeats 1200000 in
/-- An injective morphism from an affine domain has a ground-field principal
open above which all points with algebraically closed coefficients lift. -/
theorem exists_principal_open_lift_to_algClosed (f : R →ₐ[k] S) (hf : Function.Injective f) :
    ∃ d : R, d ≠ 0 ∧ ∀ (Ω : Type uΩ) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
      (p : R →ₐ[k] Ω), p d ≠ 0 → ∃ q : S →ₐ[k] Ω, q.comp f = p := by
  letI : Algebra R S := f.toRingHom.toAlgebra
  letI : IsScalarTower k R S := IsScalarTower.of_algHom f
  letI : Algebra.FiniteType R S := Algebra.FiniteType.of_restrictScalars_finiteType k R S
  obtain ⟨d, hd, hFree⟩ := exists_free_localizationAway (A := R) (B := S)
  refine ⟨d, hd, ?_⟩
  intro Ω _ _ _ p hp
  let R' := Localization.Away d
  let S' := Localization.Away (f d)
  let e : R' →ₐ[k] S' := IsLocalization.Away.mapₐ R' S' f d
  letI : Algebra R' S' := e.toRingHom.toAlgebra
  letI : IsScalarTower k R' S' := IsScalarTower.of_algHom e
  letI : Module.Free R' S' := hFree
  letI : Nontrivial S' := by
    apply nontrivial_of_ne (0 : S') 1
    intro h
    have hOne : algebraMap S S' (1 : S) = 0 := (map_one _).trans h.symm
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f d)) S' 1).mp hOne
    obtain ⟨n, hn⟩ := m.prop
    rw [← hn, mul_one] at hm
    change f d ^ n = 0 at hm
    rw [← map_pow] at hm
    exact pow_ne_zero n hd (hf (hm.trans (map_zero f).symm))
  letI : Module.FaithfullyFlat R' S' := inferInstance
  letI : Algebra.FiniteType S S' := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (f d)) S'
  letI : Algebra.FiniteType k S' := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType k S) (inferInstance : Algebra.FiniteType S S')
  letI : Algebra.FiniteType R' S' := Algebra.FiniteType.of_restrictScalars_finiteType k R' S'
  let p' := localizationAwayUnitEval p d (isUnit_iff_ne_zero.mpr hp)
  letI : Algebra R' Ω := p'.toRingHom.toAlgebra
  letI : IsScalarTower k R' Ω := IsScalarTower.of_algHom p'
  let B := Ω ⊗[R'] S'
  letI : Nontrivial B := Module.FaithfullyFlat.rTensor_nontrivial R' S' Ω
  letI : Algebra.FiniteType Ω B := Algebra.FiniteType.baseChange (R := R') Ω
  obtain ⟨q₀⟩ := StrictEUnit.nonempty_algebraic_point (k := Ω) (S := B)
  let l : S' →ₐ[k] B := (Algebra.TensorProduct.includeRight : S' →ₐ[R'] B).restrictScalars k
  let j : S →ₐ[k] S' := IsScalarTower.toAlgHom k S S'
  let q : S →ₐ[k] Ω := (q₀.restrictScalars k).comp (l.comp j)
  refine ⟨q, AlgHom.ext fun a => ?_⟩
  have he (a : R) : algebraMap R' S' (algebraMap R R' a) = algebraMap S S' (f a) := by
    change IsLocalization.Away.map R' S' f.toRingHom d (algebraMap R R' a) = _
    exact IsLocalization.map_eq _ _
  change q₀ ((1 : Ω) ⊗ₜ[R'] algebraMap S S' (f a)) = p a
  rw [← he, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  change q₀ (algebraMap Ω B (p' (algebraMap R R' a))) = _
  rw [q₀.commutes, Algebra.id.map_eq_id, RingHom.id_apply, localizationAwayUnitEval_algebraMap]

omit [Algebra.FiniteType k S] in
/-- Lifts of all rational points of a nonempty principal open detect
injectivity on the domain of coordinate functions. -/
theorem injective_of_principal_open_lifts [IsAlgClosed k] [Algebra.FiniteType k R]
    (f : R →ₐ[k] S) (d₀ : R) (hd₀ : d₀ ≠ 0)
    (hLift : ∀ p : R →ₐ[k] k, p d₀ ≠ 0 → ∃ q : S →ₐ[k] k, q.comp f = p) :
    Function.Injective f := by
  apply (injective_iff_map_eq_zero f).mpr
  intro a ha
  by_contra h
  obtain ⟨p, hp, hp₀⟩ := StrictEUnit.exists_algebraic_point_avoiding_pair (k := k) a d₀ h hd₀
  obtain ⟨q, hq⟩ := hLift p hp₀
  apply hp
  rw [← DFunLike.congr_fun hq a, AlgHom.comp_apply, ha, map_zero]

/-- A relation admitting points over a nonempty open of ground-field points
admits lifts over one refined open for all algebraically closed extensions. -/
theorem exists_refined_principal_open_lift_to_algClosed [IsAlgClosed k] [Algebra.FiniteType k R]
    (f : R →ₐ[k] S) (d₀ : R) (hd₀ : d₀ ≠ 0)
    (hLift : ∀ p : R →ₐ[k] k, p d₀ ≠ 0 → ∃ q : S →ₐ[k] k, q.comp f = p) :
    ∃ d : R, d ≠ 0 ∧ d₀ ∣ d ∧ ∀ (Ω : Type uΩ) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
      (p : R →ₐ[k] Ω), p d ≠ 0 → ∃ q : S →ₐ[k] Ω, q.comp f = p := by
  obtain ⟨d, hd, hD⟩ := exists_principal_open_lift_to_algClosed f
    (injective_of_principal_open_lifts f d₀ hd₀ hLift)
  refine ⟨d₀ * d, mul_ne_zero hd₀ hd, dvd_mul_right _ _, ?_⟩
  intro Ω _ _ _ p hp
  rw [map_mul] at hp
  exact hD Ω p (right_ne_zero_of_mul hp)

end Morphisms

section Coordinates

variable {k S ι : Type*} [Field k] [CommRing S] [Algebra k S]
  [Algebra.FiniteType k S]

/-- The principal open attained by algebraically independent coordinates is
defined over the ground field and works over all algebraically closed extensions. -/
theorem exists_affine_image_principal_open_to_algClosed
    (x : ι → S) (hx : AlgebraicIndependent k x) :
    ∃ d : MvPolynomial ι k, d ≠ 0 ∧ ∀ (Ω : Type uΩ) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
      (y : ι → Ω), MvPolynomial.aeval y d ≠ 0 → ∃ q : S →ₐ[k] Ω, ∀ i, q (x i) = y i := by
  obtain ⟨d, hd, hLift⟩ := exists_principal_open_lift_to_algClosed (MvPolynomial.aeval x) hx
  refine ⟨d, hd, ?_⟩
  intro Ω _ _ _ y hy
  obtain ⟨q, hq⟩ := hLift Ω (MvPolynomial.aeval y) hy
  exact ⟨q, fun i => by
    simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using DFunLike.congr_fun hq (MvPolynomial.X i)⟩

/-- A nonzero function on the source can be kept nonzero in the lifts
above a uniform principal open. -/
theorem exists_affine_image_principal_open_avoiding_to_algClosed [IsDomain S]
    (x : ι → S) (hx : AlgebraicIndependent k x) (a : S) (ha : a ≠ 0) :
    ∃ d : MvPolynomial ι k, d ≠ 0 ∧ ∀ (Ω : Type uΩ) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
      (y : ι → Ω), MvPolynomial.aeval y d ≠ 0 →
      ∃ q : S →ₐ[k] Ω, (∀ i, q (x i) = y i) ∧ q a ≠ 0 := by
  let L := Localization.Away a
  letI : IsDomain L := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  letI : Algebra.FiniteType S L := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers a) L
  letI : Algebra.FiniteType k L := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType k S) (inferInstance : Algebra.FiniteType S L)
  let g := IsScalarTower.toAlgHom k S L
  have hg : Function.Injective g :=
    IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  have hComp : MvPolynomial.aeval (g ∘ x) = g.comp (MvPolynomial.aeval x) :=
    MvPolynomial.algHom_ext fun i => by
      rw [MvPolynomial.aeval_X, AlgHom.comp_apply, MvPolynomial.aeval_X]
      rfl
  have hInd : AlgebraicIndependent k (g ∘ x) := by
    rw [algebraicIndependent_iff_injective_aeval, hComp]
    exact hg.comp hx
  obtain ⟨d, hd, hLift⟩ := exists_affine_image_principal_open_to_algClosed (g ∘ x) hInd
  refine ⟨d, hd, ?_⟩
  intro Ω _ _ _ y hy
  obtain ⟨q, hq⟩ := hLift Ω y hy
  exact ⟨q.comp g, hq, ((IsLocalization.Away.algebraMap_isUnit (S := L) a).map q).ne_zero⟩

end Coordinates

end WideE
