import WideE.Basic
import Stage26StrictEFiniteCoefficientField

/-! Taylor realizations and finite coefficient fields for actual wide series. -/

noncomputable section

namespace WideE

open StrictEUnit
open scoped BigOperators

abbrev algebraicSubfield : Subfield ℂ := (algebraicClosure ℚ ℂ).toSubfield

theorem HasFactorialExpansion.cauchyCoefficient {f : ℂ → ℂ}
    {a : ℕ → AlgebraicComplex} (hs : HasFactorialExpansion f a)
    (hf : Differentiable ℂ f) (n : ℕ) :
    entireCauchyCoefficient f n = (a n : ℂ) / (n.factorial : ℂ) := by
  apply entireCauchyCoefficient_eq_of_hasSum hf
  intro z
  convert hs z using 1
  funext j
  ring

theorem HasFactorialExpansion.algebraic_coefficient {f : ℂ → ℂ}
    {a : ℕ → AlgebraicComplex} (hs : HasFactorialExpansion f a)
    (hf : Differentiable ℂ f) (n : ℕ) :
    entireCauchyCoefficient f n ∈ algebraicSubfield := by
  rw [hs.cauchyCoefficient hf n]
  exact algebraicSubfield.div_mem (a n).property (natCast_mem _ _)

theorem HasFactorialExpansion.unique {f : ℂ → ℂ}
    {a b : ℕ → AlgebraicComplex} (hs : HasFactorialExpansion f a)
    (ht : HasFactorialExpansion f b) (hf : Differentiable ℂ f) : a = b := by
  funext n
  apply Subtype.ext
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  exact (div_left_inj' hn).mp ((hs.cauchyCoefficient hf n).symm.trans (ht.cauchyCoefficient hf n))

/-- The entire function with its actual Taylor coefficients in the algebraic
numbers. This construction uses the expansion of the same function. -/
def taylorRealization (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    {a : ℕ → AlgebraicComplex} (hs : HasFactorialExpansion f a) :
    subfieldEntireFunctionAlgebra algebraicSubfield :=
  ⟨⟨f, hf⟩, (mem_subfieldEntireFunctionAlgebra _ _).mpr (hs.algebraic_coefficient hf)⟩

@[simp] theorem taylorRealization_apply (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    {a : ℕ → AlgebraicComplex} (hs : HasFactorialExpansion f a) (z : ℂ) :
    (taylorRealization f hf hs).val.val z = f z := rfl

theorem taylorRealization_coeff {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a : ℕ → AlgebraicComplex} (hs : HasFactorialExpansion f a) (n : ℕ) :
    PowerSeries.coeff AlgebraicComplex n
      (subfieldEntireTaylorAlgHom algebraicSubfield (taylorRealization f hf hs)) =
        a n / (n.factorial : AlgebraicComplex) := by
  apply Subtype.ext
  simpa [subfieldEntireTaylorAlgHom, subfieldEntireTaylorSeries] using hs.cauchyCoefficient hf n

/-- Apply the algebraic Taylor homomorphism to the same analytic polynomial
ODE, preserving all the coefficient polynomials. -/
theorem formal_polynomial_ode {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a : ℕ → AlgebraicComplex} (hs : HasFactorialExpansion f a)
    (hODE : HasAlgebraicPolynomialODE f) :
    ∃ m : ℕ, ∃ p : Fin (m + 1) → Polynomial AlgebraicComplex,
      (∃ i, p i ≠ 0) ∧
      ∑ i, (p i : PowerSeries AlgebraicComplex) *
        ((PowerSeries.derivative AlgebraicComplex)^[i.val]
          (subfieldEntireTaylorAlgHom algebraicSubfield (taylorRealization f hf hs))) = 0 := by
  obtain ⟨m, p, hp, heq⟩ := hODE
  refine ⟨m, p, hp, ?_⟩
  let F := taylorRealization f hf hs
  let A := subfieldEntireFunctionAlgebra algebraicSubfield
  letI : CommSemiring A := A.toCommSemiring
  letI : Algebra algebraicSubfield A := A.algebra
  letI : Semiring A := CommSemiring.toSemiring
  letI : AddCommMonoid A :=
    (inferInstance : Semiring A).toNonUnitalNonAssocSemiring.toAddCommMonoid
  have hactual : ∑ i, Polynomial.aeval (R := algebraicSubfield)
      (subfieldEntireCoordinate algebraicSubfield) (p i) *
      ((subfieldEntireFunctionDerivation algebraicSubfield)^[i.val]) F = 0 :=
    (stage14_actualPolynomialRelation_iff algebraicSubfield F m p).mpr heq
  have hmap := congrArg (subfieldEntireTaylorAlgHom algebraicSubfield) hactual
  simp only [map_sum, map_zero, map_mul, stage26_subfieldTaylor_iterate,
    stage26_subfieldTaylor_polynomial] at hmap
  exact hmap

/-- The ODE and the actual series already force one field containing every
factorial-normalized coefficient. The proof uses the generic recurrence from
Hatsuwr's Stage26, independently of any growth class. -/
theorem HasFactorialExpansion.fixedField {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a : ℕ → AlgebraicComplex} (hs : HasFactorialExpansion f a)
    (hODE : HasAlgebraicPolynomialODE f) : HasFixedCoefficientField a := by
  obtain ⟨m, p, hp, hformal⟩ := formal_polynomial_ode hf hs hODE
  obtain ⟨K, hK, hcoeff, _⟩ :=
    stage26_formal_ode_finite_coefficient_field m p _ hp hformal
  refine ⟨K, hK, fun n => (stage26_factorial_normalization_mem_iff K a n).mp ?_⟩
  rw [← taylorRealization_coeff hf hs n]
  exact hcoeff n

theorem wideEFunction_of_expansion {f : ℂ → ℂ} {a : ℕ → AlgebraicComplex}
    (hf : Differentiable ℂ f) (hs : HasFactorialExpansion f a)
    (hODE : HasAlgebraicPolynomialODE f) (ha : HasWideEArithmetic a) :
    IsWideEFunction f :=
  ⟨a, hf, hs, hODE, ha, hs.fixedField hf hODE⟩

end WideE
