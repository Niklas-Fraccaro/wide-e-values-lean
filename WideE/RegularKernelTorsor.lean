import WideE.HopfAntipode
import WideE.ScalarKernelTorsor

/-! The regular action and the actual relative torsor for the kernel of a scalar group map. -/

noncomputable section

open scoped TensorProduct
open StrictEUnit TensorProduct

namespace WideE

section Regular

variable (k H : Type*) [Field k] [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]

/-- The group acting on itself by right translation. -/
def regularAffineHopfTorsor : AffineHopfTorsor k k H H where
  coaction := Bialgebra.comulAlgHom k H
  coassociative := fun a => Coalgebra.coassoc_apply (R := k) a
  counital := by
    have h : (coactionCounit : H ⊗[k] H →ₐ[k] H) =
        (Algebra.TensorProduct.rid k k H).toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id k H) (Bialgebra.counitAlgHom k H)) := by
      apply Algebra.TensorProduct.ext'
      intro x y
      simp only [coactionCounit, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply,
        Algebra.ofId_apply, AlgEquiv.coe_algHom, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_comm]
    intro a
    rw [h]
    change Algebra.TensorProduct.rid k k H
      ((Coalgebra.counit (R := k) (A := H)).lTensor H (Coalgebra.comul (R := k) a)) = a
    rw [Coalgebra.lTensor_counit_comul, Algebra.TensorProduct.rid_tmul, one_smul]
  canonical_bijective := by
    change Function.Bijective (hopfTranslationChart k H)
    exact (hopfTranslationChart k H).bijective
  faithfullyFlat := by
    letI : Nontrivial H := (Bialgebra.counitAlgHom k H).toRingHom.domain_nontrivial
    infer_instance
  group_finiteType := inferInstance

end Regular

section Relative

variable {k H J A : Type*} [Field k] [CommRing H] [CommRing J] [CommRing A]
  [HopfAlgebra k H] [HopfAlgebra k J] [Bialgebra k A] [Algebra.FiniteType k H]

private def regularPrincipalKernelTorsor (j : A →ₐc[k] H) (π : H →ₐc[k] J)
    (hπ : Function.Surjective π) (x : H)
    (hker : RingHom.ker (π : H →ₐ[k] J).toRingHom = Ideal.span {x})
    (hj : letI : Algebra A H := (j : A →ₐ[k] H).toRingHom.toAlgebra; Module.FaithfullyFlat A H)
    (hfix : ∀ a : A, Algebra.TensorProduct.map (AlgHom.id k H) (π : H →ₐ[k] J)
      (Bialgebra.comulAlgHom k H (j a)) = j a ⊗ₜ[k] (1 : J))
    (a : A) (u : Hˣ) (hcoord : Bialgebra.comulAlgHom k H (j a) - j a ⊗ₜ[k] (1 : H) =
        (u : H) ⊗ₜ[k] x) :
    letI : Algebra A H := (j : A →ₐ[k] H).toRingHom.toAlgebra
    letI : IsScalarTower k A H := IsScalarTower.of_algHom (j : A →ₐ[k] H)
    AffineHopfTorsor k A H J := by
  letI : Algebra A H := (j : A →ₐ[k] H).toRingHom.toAlgebra
  letI : IsScalarTower k A H := IsScalarTower.of_algHom (j : A →ₐ[k] H)
  let T := regularAffineHopfTorsor k H
  have hfix' : ∀ z : A, T.kernelAction π (algebraMap A H z) = algebraMap A H z ⊗ₜ[k] (1 : J) := hfix
  have hcoord' : T.chart.symm ((1 : H) ⊗ₜ[k] algebraMap A H a - algebraMap A H a ⊗ₜ[k] (1 : H)) =
      (u : H) ⊗ₜ[k] x := by
    rw [map_sub, T.chart_symm_apply, T.chart_symm_apply]
    change ((1 : H) ⊗ₜ[k] (1 : H)) * Bialgebra.comulAlgHom k H (j a) -
      (j a ⊗ₜ[k] (1 : H)) * Bialgebra.comulAlgHom k H 1 = _
    rw [map_one, mul_one, ← Algebra.TensorProduct.one_def, one_mul]
    exact hcoord
  refine ⟨T.restrictCoactionOver π hfix', T.kernelAction_coassociative π, T.kernelAction_counital π,
    T.principalKernel_canonical_bijective π hπ x hker hfix' a u hcoord', hj, ?_⟩
  exact Algebra.FiniteType.of_surjective inferInstance (π : H →ₐ[k] J) hπ

end Relative

section ScalarQuotients

variable {k H J : Type*} [Field k] [CommRing H] [CommRing J] [HopfAlgebra k H]
  [HopfAlgebra k J] [Algebra.FiniteType k H]

attribute [local instance] additivePolynomialHopf

/-- The total group is a torsor under the additive kernel over its actual
polynomial coordinate algebra. -/
def additiveRelativeKernelTorsor (j : Polynomial k →ₐc[k] H) (π : H →ₐc[k] J)
    (hπ : Function.Surjective π)
    (hker : RingHom.ker (π : H →ₐ[k] J).toRingHom = Ideal.span {j Polynomial.X})
    (hj : letI : Algebra (Polynomial k) H := (j : Polynomial k →ₐ[k] H).toRingHom.toAlgebra
      Module.FaithfullyFlat (Polynomial k) H) :
    letI : Algebra (Polynomial k) H := (j : Polynomial k →ₐ[k] H).toRingHom.toAlgebra
    letI : IsScalarTower k (Polynomial k) H := IsScalarTower.of_algHom (j : Polynomial k →ₐ[k] H)
    AffineHopfTorsor k (Polynomial k) H J := by
  let f : Polynomial k →ₐ[k] H := j
  let p : H →ₐ[k] J := π
  let x := j Polynomial.X
  have hx : Bialgebra.comulAlgHom k H x = (1 : H) ⊗ₜ[k] x + x ⊗ₜ[k] (1 : H) := by
    have h := DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom j) Polynomial.X
    change Algebra.TensorProduct.map f f (Bialgebra.comulAlgHom k (Polynomial k) Polynomial.X) =
      Bialgebra.comulAlgHom k H x at h
    rw [additivePolynomialHopf_comul_X, map_add, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul, map_one] at h
    exact h.symm
  have hp : p x = 0 := by
    change x ∈ RingHom.ker p.toRingHom
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton x)
  have hfix : (Algebra.TensorProduct.map (AlgHom.id k H) p).comp
        ((Bialgebra.comulAlgHom k H).comp f) =
      (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] J).comp f := by
    apply Polynomial.algHom_ext
    change Algebra.TensorProduct.map (AlgHom.id k H) p (Bialgebra.comulAlgHom k H x) =
      x ⊗ₜ[k] (1 : J)
    simp only [hx, map_add, Algebra.TensorProduct.map_tmul,
      hp, AlgHom.id_apply, map_one, tmul_zero, zero_add]
  refine regularPrincipalKernelTorsor j π hπ x hker hj
    (fun a => DFunLike.congr_fun hfix a) Polynomial.X 1 ?_
  change Bialgebra.comulAlgHom k H x - x ⊗ₜ[k] (1 : H) = (1 : H) ⊗ₜ[k] x
  rw [hx, add_sub_cancel_right]

/-- The total group is a torsor under the multiplicative kernel over its
actual Laurent coordinate algebra. -/
def multiplicativeRelativeKernelTorsor (j : LaurentPolynomial k →ₐc[k] H) (π : H →ₐc[k] J)
    (hπ : Function.Surjective π)
    (hker : RingHom.ker (π : H →ₐ[k] J).toRingHom = Ideal.span {j (LaurentPolynomial.T 1) - 1})
    (hj : letI : Algebra (LaurentPolynomial k) H := (j : LaurentPolynomial k →ₐ[k] H).toRingHom.toAlgebra
      Module.FaithfullyFlat (LaurentPolynomial k) H) :
    letI : Algebra (LaurentPolynomial k) H := (j : LaurentPolynomial k →ₐ[k] H).toRingHom.toAlgebra
    letI : IsScalarTower k (LaurentPolynomial k) H := IsScalarTower.of_algHom (j : LaurentPolynomial k →ₐ[k] H)
    AffineHopfTorsor k (LaurentPolynomial k) H J := by
  let f : LaurentPolynomial k →ₐ[k] H := j
  let p : H →ₐ[k] J := π
  let x := j (LaurentPolynomial.T 1)
  let t := (LaurentPolynomial.isUnit_T (R := k) 1).unit
  let u := Units.map f.toMonoidHom t
  have hu : (u : H) = x := congrArg f (LaurentPolynomial.isUnit_T (R := k) 1).unit_spec
  have hx : Bialgebra.comulAlgHom k H x = x ⊗ₜ[k] x := by
    have h := DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom j) (LaurentPolynomial.T 1)
    change Algebra.TensorProduct.map f f (Coalgebra.comul (R := k) (LaurentPolynomial.T 1)) =
      Bialgebra.comulAlgHom k H x at h
    rw [LaurentPolynomial.comul_T, Algebra.TensorProduct.map_tmul] at h
    exact h.symm
  have hp : p x = 1 := by
    have ht : x - 1 ∈ RingHom.ker p.toRingHom := by
      rw [hker]
      exact Ideal.subset_span (Set.mem_singleton (x - 1))
    change p (x - 1) = 0 at ht
    rwa [map_sub, map_one, sub_eq_zero] at ht
  have hfix : (Algebra.TensorProduct.map (AlgHom.id k H) p).comp
        ((Bialgebra.comulAlgHom k H).comp f) =
      (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] J).comp f := by
    apply laurentAlgHom_ext
    change Algebra.TensorProduct.map (AlgHom.id k H) p (Bialgebra.comulAlgHom k H x) =
      x ⊗ₜ[k] (1 : J)
    rw [hx, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hp]
  refine regularPrincipalKernelTorsor j π hπ (x - 1) hker hj
    (fun a => DFunLike.congr_fun hfix a) (LaurentPolynomial.T 1) u ?_
  change Bialgebra.comulAlgHom k H x - x ⊗ₜ[k] (1 : H) = (u : H) ⊗ₜ[k] (x - 1)
  rw [hx, hu, tmul_sub]

end ScalarQuotients

end WideE
