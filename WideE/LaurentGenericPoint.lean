import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.TensorProduct.Basic

/-! The fraction algebra of the Laurent line and points over its generic point. -/

noncomputable section

open scoped TensorProduct

namespace WideE

section FractionRing

variable (K : Type*) [Field K]

private theorem ratFunc_algebraMap_X_isUnit :
    IsUnit (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) :=
  isUnit_iff_ne_zero.mpr RatFunc.X_ne_zero

/-- The Laurent coordinate maps to the indeterminate in the rational function field. -/
def laurentRatFuncAlgebra : Algebra (LaurentPolynomial K) (RatFunc K) :=
  (IsLocalization.Away.lift (S := LaurentPolynomial K) (g := algebraMap (Polynomial K) (RatFunc K))
    Polynomial.X (ratFunc_algebraMap_X_isUnit K)).toAlgebra

attribute [local instance] laurentRatFuncAlgebra

@[simp] theorem laurentRatFunc_algebraMap_toLaurent (p : Polynomial K) :
    algebraMap (LaurentPolynomial K) (RatFunc K) p.toLaurent = algebraMap (Polynomial K) (RatFunc K) p :=
  IsLocalization.Away.lift_eq Polynomial.X (ratFunc_algebraMap_X_isUnit K) p

@[simp] theorem laurentRatFunc_algebraMap_T_one :
    algebraMap (LaurentPolynomial K) (RatFunc K) (LaurentPolynomial.T 1) = RatFunc.X := by
  rw [← Polynomial.toLaurent_X, laurentRatFunc_algebraMap_toLaurent, RatFunc.algebraMap_X]

theorem laurentRatFunc_scalarTower : IsScalarTower K (LaurentPolynomial K) (RatFunc K) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap K (RatFunc K) a =
    algebraMap (LaurentPolynomial K) (RatFunc K) (LaurentPolynomial.C a)
  rw [← Polynomial.toLaurent_C, laurentRatFunc_algebraMap_toLaurent]
  exact IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K) a

/-- Inverting the Laurent coordinate leaves the fraction field of the polynomial ring unchanged. -/
theorem laurentRatFunc_isFractionRing : IsFractionRing (LaurentPolynomial K) (RatFunc K) := by
  letI : IsScalarTower (Polynomial K) (LaurentPolynomial K) (RatFunc K) :=
    IsScalarTower.of_algebraMap_eq fun p => (laurentRatFunc_algebraMap_toLaurent K p).symm
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (Polynomial.X : Polynomial K)) (LaurentPolynomial K) (RatFunc K)

end FractionRing

section BaseChange

variable {R F S : Type*} [CommRing R] [CommRing F] [CommRing S] [Algebra R F] [Algebra R S]

/-- Points over a scalar extension are the points of the scalar-extended algebra. -/
def baseChangePointEquiv : ((F ⊗[R] S) →ₐ[F] F) ≃ (S →ₐ[R] F) where
  toFun p := (p.restrictScalars R).comp Algebra.TensorProduct.includeRight
  invFun p := Algebra.TensorProduct.lift (AlgHom.id F F) p (fun _ _ => Commute.all _ _)
  left_inv p := by
    apply AlgHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a s =>
        change a * p ((1 : F) ⊗ₜ[R] s) = p (a ⊗ₜ[R] s)
        have ha : p (a ⊗ₜ[R] (1 : S)) = a := p.commutes a
        calc
          _ = p (a ⊗ₜ[R] (1 : S)) * p ((1 : F) ⊗ₜ[R] s) := by rw [ha]
          _ = _ := by rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  right_inv p := by
    apply AlgHom.ext
    intro s
    change (1 : F) * p s = p s
    exact one_mul _

@[simp] theorem baseChangePointEquiv_apply (p : (F ⊗[R] S) →ₐ[F] F) (s : S) :
    baseChangePointEquiv p s = p ((1 : F) ⊗ₜ[R] s) := rfl

end BaseChange

end WideE
