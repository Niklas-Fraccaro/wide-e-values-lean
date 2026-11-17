import WideE.Laurent
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.PowerSeries.Derivative

/-! The expansion of the Laurent coefficient ring at the ordinary point one. -/

noncomputable section

namespace WideE

open LaurentPolynomial

variable (K : Type*) [CommRing K]

/-- The formal Laurent coordinate at one has constant term one and is therefore a unit. -/
def formalUnitAtOne : (PowerSeries K)ˣ :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr (by simp) :
      IsUnit (PowerSeries.X + 1 : PowerSeries K)).unit

@[simp] theorem formalUnitAtOne_val :
    (formalUnitAtOne K : PowerSeries K) = PowerSeries.X + 1 :=
  IsUnit.unit_spec _

/-- Expand Laurent polynomials in the coordinate `X = T - 1`. -/
def formalAtOne : LaurentPolynomial K →ₐ[K] PowerSeries K where
  __ := LaurentPolynomial.eval₂ (PowerSeries.C K) (formalUnitAtOne K)
  commutes' a := by
    change LaurentPolynomial.eval₂ (PowerSeries.C K) (formalUnitAtOne K)
      (algebraMap K (LaurentPolynomial K) a) = _
    rw [← LaurentPolynomial.C_eq_algebraMap, LaurentPolynomial.eval₂_C,
      PowerSeries.algebraMap_apply]
    rfl

@[simp] theorem formalAtOne_C (a : K) :
    formalAtOne K (C a) = PowerSeries.C K a :=
  LaurentPolynomial.eval₂_C _ _ _

theorem formalAtOne_T (n : ℤ) :
    formalAtOne K (T n) = ↑(formalUnitAtOne K ^ n) :=
  LaurentPolynomial.eval₂_T _ _ _

@[simp] theorem formalAtOne_coordinate :
    formalAtOne K (T 1) = PowerSeries.X + 1 := by
  rw [formalAtOne_T, zpow_one, formalUnitAtOne_val]

/-- The constant coefficient of a Laurent polynomial expanded at one is its value at one. -/
@[simp] theorem formalAtOne_constantCoeff (p : LaurentPolynomial K) :
    PowerSeries.constantCoeff K (formalAtOne K p) = evalAtOne K p := by
  have hu : Units.map (PowerSeries.constantCoeff K).toMonoidHom (formalUnitAtOne K) = 1 := by
    apply Units.ext
    simp
  induction p using LaurentPolynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | C_mul_T n a =>
    rw [map_mul, map_mul, map_mul, formalAtOne_C, PowerSeries.constantCoeff_C,
      formalAtOne_T, evalAtOne_C, evalAtOne_T, mul_one]
    have h : PowerSeries.constantCoeff K ↑(formalUnitAtOne K ^ n) = 1 := by
      change ((Units.map (PowerSeries.constantCoeff K).toMonoidHom
        (formalUnitAtOne K ^ n) : Kˣ) : K) = 1
      rw [map_zpow, hu, one_zpow, Units.val_one]
    rw [h, mul_one]

@[simp] theorem formalAtOne_derivative (p : LaurentPolynomial K) :
    PowerSeries.derivative K (formalAtOne K p) = formalAtOne K (laurentDerivation p) := by
  rw [laurentDerivation_chain, formalAtOne_coordinate, map_add, PowerSeries.derivative_X,
    Derivation.map_one_eq_zero, add_zero, one_mul]

theorem formalAtOne_toLaurent (p : Polynomial K) :
    formalAtOne K p.toLaurent = ↑(Polynomial.algEquivAevalXAddC (1 : K) p) := by
  let shift : Polynomial K →ₐ[K] PowerSeries K :=
    (Polynomial.coeToPowerSeries.algHom K).comp (Polynomial.algEquivAevalXAddC (1 : K)).toAlgHom
  have h : (formalAtOne K).comp Polynomial.toLaurentAlg = shift := by
    apply Polynomial.algHom_ext
    simp [shift, Polynomial.algEquivAevalXAddC, Polynomial.coeToPowerSeries.algHom_apply]
  have h' := DFunLike.congr_fun h p
  simpa [shift, Polynomial.coeToPowerSeries.algHom_apply] using h'

theorem formalAtOne_injective : Function.Injective (formalAtOne K) := by
  apply (injective_iff_map_eq_zero (formalAtOne K)).mpr
  intro p hp
  obtain ⟨n, f, hf⟩ := LaurentPolynomial.exists_T_pow p
  have hf' : formalAtOne K f.toLaurent = 0 := by rw [hf, map_mul, hp, zero_mul]
  rw [formalAtOne_toLaurent] at hf'
  have hf0 : f = 0 := by
    apply (Polynomial.algEquivAevalXAddC (1 : K)).injective
    apply Polynomial.coe_injective K
    rw [map_zero]
    exact hf'.trans (Polynomial.coe_zero (R := K)).symm
  have hz := congrArg (fun g : LaurentPolynomial K => g * T (- (n : ℤ))) hf
  change f.toLaurent * T (- (n : ℤ)) = p * T (n : ℤ) * T (- (n : ℤ)) at hz
  rw [hf0, map_zero, zero_mul, mul_T_assoc, add_neg_cancel, T_zero, mul_one] at hz
  exact hz.symm

end WideE
