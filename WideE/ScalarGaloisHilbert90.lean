import WideE.AdditivePolynomialHopf
import WideE.GaloisInflation
import WideE.GaloisRootsOfUnity
import WideE.KummerCoordinates
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-! Hilbert 90 for the actual additive and multiplicative Hopf points. -/

noncomputable section

open scoped BigOperators TensorProduct

namespace WideE

section AdditiveHilbert90

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

/-- An additive Galois cocycle is the difference of an element and its Galois translate. -/
theorem additiveHilbert90 [CharZero E] (a : (E ≃ₐ[F] E) → E)
    (ha : ∀ σ τ, a (σ * τ) = a σ + σ (a τ)) :
    ∃ b : E, ∀ σ, a σ + σ b = b := by
  classical
  let Γ := E ≃ₐ[F] E
  letI : Fintype Γ := Fintype.ofFinite Γ
  let N : E := (Fintype.card Γ : ℕ)
  have hN : N ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨(∑ τ : Γ, a τ) / N, fun σ => ?_⟩
  have hSum : (∑ τ : Γ, a (σ * τ)) = ∑ τ : Γ, a τ :=
    Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun _ => rfl
  simp_rw [ha, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hSum
  change a σ + σ ((∑ τ : Γ, a τ) / N) = (∑ τ : Γ, a τ) / N
  have hNfixed : σ N = N := map_natCast σ (Fintype.card Γ)
  rw [map_div₀, hNfixed, map_sum]
  calc
    _ = (N * a σ + ∑ τ : Γ, σ (a τ)) / N := by
      rw [add_div, mul_div_cancel_left₀ _ hN]
    _ = _ := congrArg (fun x : E => x / N) hSum

end AdditiveHilbert90

section ScalarCoordinates

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

attribute [local instance] additivePolynomialHopf

theorem additivePolynomialHopf_ker_counit :
    RingHom.ker (Bialgebra.counitAlgHom k (Polynomial k)).toRingHom =
      Ideal.span {(Polynomial.X : Polynomial k)} := by
  ext p
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
  change Polynomial.aeval (0 : k) p = 0 ↔ p.coeff 0 = 0
  simp [Polynomial.aeval_def, Polynomial.eval₂_at_zero]

theorem laurentPolynomial_ker_counit :
    RingHom.ker (Bialgebra.counitAlgHom k (LaurentPolynomial k)).toRingHom =
      Ideal.span {LaurentPolynomial.T (R := k) 1 - 1} := by
  let ε : LaurentPolynomial k →ₐ[k] k := { evalAtOne k with commutes' := evalAtOne_C k }
  have hε : Bialgebra.counitAlgHom k (LaurentPolynomial k) = ε := by
    apply laurentAlgHom_ext
    change Coalgebra.counit (R := k) (LaurentPolynomial.T (R := k) 1) = evalAtOne k (LaurentPolynomial.T 1)
    rw [LaurentPolynomial.counit_T, evalAtOne_T]
  rw [hε]
  exact ker_evalAtOne k

@[simp] theorem hopfPointMul_additivePolynomial_X (p q : Polynomial k →ₐ[k] A) :
    hopfPointMul p q Polynomial.X = p Polynomial.X + q Polynomial.X := by
  change tensorPoint p q (Bialgebra.comulAlgHom k (Polynomial k) Polynomial.X) = _
  rw [additivePolynomialHopf_comul_X, map_add, tensorPoint_tmul, tensorPoint_tmul, map_one, map_one,
    one_mul, mul_one, add_comm]

@[simp] theorem hopfPointMul_laurentPolynomial_T (p q : LaurentPolynomial k →ₐ[k] A) :
    hopfPointMul p q (LaurentPolynomial.T 1) =
      p (LaurentPolynomial.T 1) * q (LaurentPolynomial.T 1) := by
  change tensorPoint p q (Coalgebra.comul (R := k) (LaurentPolynomial.T 1)) = _
  rw [LaurentPolynomial.comul_T, tensorPoint_tmul]

end ScalarCoordinates

section ScalarCocycles

variable {k F E : Type*} [CommRing k] [Field F] [Field E] [Algebra F E]
  [Algebra k F] [Algebra k E] [IsScalarTower k F E] [FiniteDimensional F E]

attribute [local instance] additivePolynomialHopf

/-- Hilbert 90 in the existing cocycle convention, on points of the additive group. -/
theorem isHopfPointCoboundary_of_additivePolynomial [CharZero E]
    {c : (E ≃ₐ[F] E) → Polynomial k →ₐ[k] E} (hc : IsHopfPointCocycle c) :
    IsHopfPointCoboundary c := by
  let a (σ : E ≃ₐ[F] E) := c σ Polynomial.X
  have ha (σ τ : E ≃ₐ[F] E) : a (σ * τ) = a σ + σ (a τ) := by
    have h := DFunLike.congr_fun (hc.2 σ τ) Polynomial.X
    simpa only [hopfPointMul_additivePolynomial_X, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      AlgEquiv.coe_algHom] using h
  obtain ⟨b, hb⟩ := additiveHilbert90 a ha
  refine ⟨Polynomial.aeval b, fun σ => Polynomial.algHom_ext ?_⟩
  simpa only [hopfPointMul_additivePolynomial_X, AlgHom.comp_apply, Polynomial.aeval_X,
    AlgHom.restrictScalars_apply, AlgEquiv.coe_algHom] using hb σ

/-- Multiplicative Hilbert 90 transported to points of the Laurent coordinate Hopf algebra. -/
theorem isHopfPointCoboundary_of_laurentPolynomial
    {c : (E ≃ₐ[F] E) → LaurentPolynomial k →ₐ[k] E} (hc : IsHopfPointCocycle c) :
    IsHopfPointCoboundary c := by
  let t : (LaurentPolynomial k)ˣ := (LaurentPolynomial.isUnit_T (R := k) 1).unit
  have ht : (t : LaurentPolynomial k) = LaurentPolynomial.T 1 :=
    (LaurentPolynomial.isUnit_T (R := k) 1).unit_spec
  let f (σ : E ≃ₐ[F] E) := Units.map (c σ).toRingHom.toMonoidHom t
  have hf (σ τ : E ≃ₐ[F] E) : f (σ * τ) = f σ * (σ • f τ) := by
    apply Units.ext
    change c (σ * τ) (t : LaurentPolynomial k) = c σ (t : LaurentPolynomial k) * σ (c τ (t : LaurentPolynomial k))
    have h := DFunLike.congr_fun (hc.2 σ τ) (LaurentPolynomial.T 1)
    simpa only [ht, hopfPointMul_laurentPolynomial_T, AlgHom.comp_apply,
      AlgHom.restrictScalars_apply, AlgEquiv.coe_algHom] using h
  obtain ⟨a, ha⟩ := unitHilbert90 f hf
  let p : LaurentPolynomial k →ₐ[k] E :=
    { toRingHom := LaurentPolynomial.eval₂ (algebraMap k E) a⁻¹
      commutes' := LaurentPolynomial.eval₂_C _ _ }
  have hp : p (LaurentPolynomial.T 1) = (a⁻¹ : Eˣ) := by
    change LaurentPolynomial.eval₂ (algebraMap k E) a⁻¹ (LaurentPolynomial.T 1) = _
    rw [LaurentPolynomial.eval₂_T, zpow_one]
  refine ⟨p, fun σ => laurentAlgHom_ext ?_⟩
  have h : f σ * (σ • a⁻¹) = a⁻¹ := by
    rw [← ha, div_eq_mul_inv, smul_inv', mul_right_comm, mul_inv_cancel, one_mul]
  have he := congrArg Units.val h
  change c σ (t : LaurentPolynomial k) * σ (↑(a⁻¹) : E) = ↑(a⁻¹) at he
  simpa only [hopfPointMul_laurentPolynomial_T, AlgHom.comp_apply, hp,
    AlgHom.restrictScalars_apply, AlgEquiv.coe_algHom, ht] using he

end ScalarCocycles

end WideE
