import WideE.ArithmeticLifting
import WideE.Conjugates
import CompanionArithmeticLocalRegularity
import SameCompanionScalarSelection
import SelectedScalarPowerSeriesTransport
import SelectedScalarFieldMapTransport
import OrdinaryReflectionValuation
import ValuedReciprocalFourier
import ActualFourierLeadingMonomial

/-! The local regularity and Fourier steps of wide Laurent-operator existence.
The denominator input concerns the divided connection polynomials of the
same companion selected from the ordinary Borel series. -/

noncomputable section

namespace WideE

open StrictEUnit Filter
open scoped BigOperators NumberField Matrix

/-- One positive integer clears all polynomial coefficients of the connection
matrices through each prefix, with a subfactorial bound. -/
def HasSubfactorialConnectionDenominators {K : Type*} [Field K] [CharZero K]
    {r : ℕ} (T : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℕ,
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ C * (s.factorial : ℝ) ^ ε ∧
      ∀ m, m ≤ s → ∀ i j : Fin r, ∀ l : ℕ,
        IsIntegral ℤ ((d : K) * (dividedPolynomialConnectionSequence T U m i j).coeff l)

/-- The factorial obstruction still applies when the integer clearing
sequence is bounded by a square root of the factorial. -/
theorem factorial_denominator_eventually_eq_zero_of_half
    {K : Type*} [Field K] [NumberField K]
    (C D : ℝ) (hC : 1 ≤ C) (hD : 1 ≤ D)
    (x : ℕ → K) (δ : ℕ → ℕ) (hδ : ∀ n, 0 < δ n)
    (hδbound : ∀ n, (δ n : ℝ) ≤ D * Real.sqrt (n.factorial : ℝ))
    (hxbound : ∀ n, NumberField.house (x n) ≤ C ^ (n + 1))
    (hint : ∀ n, IsIntegral ℤ ((δ n : K) * x n / (n.factorial : K))) :
    ∀ᶠ n : ℕ in atTop, x n = 0 := by
  filter_upwards [eventually_real_pow_succ_lt_factorial ((D * C) ^ 2) (by positivity)]
    with n hfact
  have hF : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hpowD : D ≤ D ^ (n + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hD (Nat.succ_le_succ (Nat.zero_le n))
  have hsmallProduct : D * C ^ (n + 1) < Real.sqrt (n.factorial : ℝ) := by
    calc
      D * C ^ (n + 1) ≤ D ^ (n + 1) * C ^ (n + 1) :=
        mul_le_mul_of_nonneg_right hpowD (by positivity)
      _ = (D * C) ^ (n + 1) := (mul_pow _ _ _).symm
      _ < Real.sqrt (n.factorial : ℝ) := by
        apply Real.lt_sqrt_of_sq_lt
        simpa only [← pow_mul, Nat.mul_comm 2] using hfact
  have hsmall : NumberField.house ((δ n : K) * x n / (n.factorial : K)) < 1 := by
    calc
      _ ≤ (δ n : ℝ) * NumberField.house (x n) / (n.factorial : ℝ) :=
        numberField_house_nat_mul_div_nat_le (x n) (δ n) n.factorial
      _ ≤ (D * Real.sqrt (n.factorial : ℝ) * C ^ (n + 1)) / (n.factorial : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul (hδbound n) (hxbound n) (NumberField.house_nonneg _) (by positivity)) hF.le
      _ < 1 := by
        apply (div_lt_one hF).mpr
        calc
          _ = (D * C ^ (n + 1)) * Real.sqrt (n.factorial : ℝ) := by ring
          _ < Real.sqrt (n.factorial : ℝ) * Real.sqrt (n.factorial : ℝ) :=
            mul_lt_mul_of_pos_right hsmallProduct (Real.sqrt_pos.2 hF)
          _ = (n.factorial : ℝ) := Real.mul_self_sqrt hF.le
  have hz := isIntegral_eq_zero_of_house_lt_one _ (hint n) hsmall
  have hδne : (δ n : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hδ n))
  have hFne : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  exact (mul_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right hFne)).resolve_left hδne

private theorem constantCompanion_last_row_zero_of_half
    {K : Type*} [Field K] [NumberField K]
    (n : ℕ) (t : K) (ht : t ≠ 0) (v : Fin (n + 1) → K)
    (D : ℝ) (hD : 1 ≤ D) (δ : ℕ → ℕ)
    (hδ : ∀ m, 0 < δ m) (hbound : ∀ m, (δ m : ℝ) ≤ D * Real.sqrt (m.factorial : ℝ))
    (hint : ∀ m j, IsIntegral ℤ ((δ m : K) *
      (Pi.single 0 1 ᵥ* (constantCompanion n t v) ^ m) j / (m.factorial : K))) :
    ∀ j, v j = 0 := by
  classical
  obtain ⟨B, hB, hhouse⟩ := matrix_first_row_orbit_house_bound n (constantCompanion n t v)
  have hz (j : Fin (n + 1)) : ∀ᶠ m : ℕ in atTop,
      (Pi.single 0 1 ᵥ* (constantCompanion n t v) ^ m) j = 0 := by
    apply factorial_denominator_eventually_eq_zero_of_half B D hB hD _ δ hδ hbound
    · intro m
      simpa only [constantCompanion_orbit_eq_power] using hhouse m j
    · intro m
      exact hint m j
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Filter.eventually_all.mpr hz)
  intro j
  by_contra hj
  apply constantCompanion_power_not_eventually_zero n t ht v ⟨j, hj⟩
  exact ⟨N, fun m hm => funext (hN m hm)⟩

private theorem companion_local_bounds_of_half
    {K : Type*} [Field K] [NumberField K]
    (n : ℕ) (c : Fin (n + 1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial K))
    (hT : T ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) T * minimalDerivativeCompanion (n + 1) c i j)
    (D : ℝ) (hD : 1 ≤ D)
    (hden : ∀ s : ℕ, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ D * Real.sqrt (s.factorial : ℝ) ∧
      ∀ i j : Fin (n + 1), ∀ l : ℕ,
        IsIntegral ℤ ((d : K) * (dividedPolynomialConnectionSequence T U s i j).coeff l)) :
    ∀ j, U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree + j.val ≤ (U (Fin.last n) j).natTrailingDegree + (n + 1) := by
  classical
  intro j hj
  by_contra hbad
  let S : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => U (Fin.last n) i ≠ 0)
  have hjs : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have hirr : (U (Fin.last n) j).natTrailingDegree + (n + 1 - j.val) < T.natTrailingDegree := by
    have hlt := j.isLt
    omega
  obtain ⟨j₀, hj₀, hh, hha, ha, hcross, heq⟩ := exists_attained_irregular_slope
    (n + 1) T.natTrailingDegree (Nat.succ_pos n)
    (fun i => (U (Fin.last n) i).natTrailingDegree) S ⟨j, hjs, hirr⟩
  let h := n + 1 - j₀.val
  let a := T.natTrailingDegree - (U (Fin.last n) j₀).natTrailingDegree
  have hV (i : Fin (n + 1)) (hi : U (Fin.last n) i ≠ 0) :
      h * T.natTrailingDegree ≤ h * (U (Fin.last n) i).natTrailingDegree + (n + 1 - i.val) * a := by
    simpa only [h, a, Nat.mul_comm] using hcross i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  let τ := T.coeff T.natTrailingDegree
  let β := polynomialCompanionFace n h a T U
  let u := polynomialConnectionFaceRow n h a T U
  have hτ : τ ≠ 0 := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT
  have hj₀ne : U (Fin.last n) j₀ ≠ 0 := (Finset.mem_filter.mp hj₀).2
  have hβ : β j₀ ≠ 0 := polynomialCompanionFace_ne_zero_of_attained n h a hh T U j₀ hj₀ne
    (by simpa only [h, a, Nat.mul_comm] using heq)
  have hrec := polynomialConnectionFaceRow_recurrence n c T U hclear h a hh hha ha hV
  have hu (m : ℕ) : u m = (fun x => x ᵥ* constantCompanion n τ β)^[m] (Pi.single 0 1) := by
    induction m with
    | zero => exact hrec.1
    | succ m ih =>
      rw [Function.iterate_succ_apply', ← ih]
      funext i
      have hc := constantCompanion_row_action n τ β (u m)
      cases i using Fin.cases with
      | zero => exact (hrec.2 m).1.trans hc.1.symm
      | succ i => exact ((hrec.2 m).2 i).trans (hc.2 i).symm
  choose δ hδ hδbound hint using hden
  have hOrbit (m : ℕ) (i : Fin (n + 1)) : IsIntegral ℤ ((δ m : K) *
      (Pi.single 0 1 ᵥ* (constantCompanion n τ β) ^ m) i / (m.factorial : K)) := by
    rw [← constantCompanion_orbit_eq_power, ← hu m]
    exact polynomialConnectionSequence_expanded_integral T U m (δ m) h hh 0 i
      (irregularPolynomialWeight h T.natTrailingDegree a m i.val) (hint m 0 i)
  exact hβ (constantCompanion_last_row_zero_of_half n τ hτ β D hD δ hδ hδbound hOrbit j₀)

/-- Wide common denominators imply the reciprocal regularity inequalities
for the scalar tuple from this very companion and clearing. -/
theorem HasSubfactorialConnectionDenominators.reciprocalRegularSingularBounds
    {K : Type*} [Field K] [NumberField K]
    (n : ℕ) (c : Fin (n + 1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial K))
    (hT : T ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) T * minimalDerivativeCompanion (n + 1) c i j)
    (hden : HasSubfactorialConnectionDenominators T U) :
    ReciprocalRegularSingularBounds (n + 1) (sameCompanionScalarTuple (n + 1) (Nat.succ_pos n) T U) := by
  obtain ⟨D, hD, hbd⟩ := hden (1 / 2) (by norm_num)
  have hHalf (s : ℕ) : ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ D * Real.sqrt (s.factorial : ℝ) ∧
      ∀ i j : Fin (n + 1), ∀ l : ℕ,
        IsIntegral ℤ ((d : K) * (dividedPolynomialConnectionSequence T U s i j).coeff l) := by
    obtain ⟨d, hd, hdb, hint⟩ := hbd s
    exact ⟨d, hd, by simpa only [Real.sqrt_eq_rpow] using hdb, hint s le_rfl⟩
  have hb := companion_local_bounds_of_half n c T U hT hclear D hD hHalf
  intro i hi
  cases i using Fin.lastCases with
  | last => simp [sameCompanionScalarTuple]
  | cast i =>
    have hidx : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := by
      apply Fin.ext
      simp
    have hne : U (Fin.last n) i ≠ 0 := by
      simpa only [sameCompanionScalarTuple, Fin.lastCases_castSucc, hidx, neg_ne_zero] using hi
    simpa only [sameCompanionScalarTuple, Fin.lastCases_last, Fin.lastCases_castSucc,
      hidx, Polynomial.natTrailingDegree_neg, Fin.coe_castSucc] using hb i hne

private theorem hasLaurentOperator_of_monomialLeading {f : ℂ → ℂ}
    (m : ℕ) (hm : 0 < m) (r : ℕ) (c : AlgebraicComplex) (hc : c ≠ 0)
    (p : Fin (m + 1) → Polynomial AlgebraicComplex)
    (hp : p (Fin.last m) = Polynomial.monomial r c)
    (heq : ∀ z : ℂ, ∑ i, (p i).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z *
      iteratedDeriv i.val f z = 0) : HasLaurentOperator f := by
  let scale : LaurentPolynomial AlgebraicComplex :=
    -LaurentPolynomial.C c⁻¹ * LaurentPolynomial.T (-(r : ℤ))
  let b (i : Fin m) : LaurentPolynomial AlgebraicComplex := scale * (p i.castSucc).toLaurent
  refine ⟨m, hm, b, fun z => ?_⟩
  let d : ℂ := (c : ℂ) * (z : ℂ) ^ r
  have hd : d ≠ 0 := mul_ne_zero ((algebraicClosure ℚ ℂ).val.injective.ne hc) (pow_ne_zero _ z.ne_zero)
  let E := LaurentPolynomial.eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z
  have hEvalScale : E scale = -(d⁻¹) := by
    simp only [E, scale, d, map_mul, map_neg, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T,
      map_inv₀, zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      mul_inv_rev, neg_mul, mul_comm]
    change ((z : ℂ) ^ r)⁻¹ * -((c : ℂ)⁻¹) = -((c : ℂ)⁻¹ * ((z : ℂ) ^ r)⁻¹)
    ring
  have hrel := heq (z : ℂ)
  rw [Fin.sum_univ_castSucc] at hrel
  simp only [Fin.val_last, Fin.coe_castSucc, hp, Polynomial.eval₂_monomial] at hrel
  have hsolve : d * iteratedDeriv m f (z : ℂ) =
      -(∑ i : Fin m, (p i.castSucc).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom (z : ℂ) *
        iteratedDeriv i.val f (z : ℂ)) := eq_neg_of_add_eq_zero_right hrel
  change iteratedDeriv m f (z : ℂ) = ∑ i, E (b i) * iteratedDeriv i.val f (z : ℂ)
  simp only [b, map_mul, E, LaurentPolynomial.eval₂_toLaurent, mul_assoc, ← Finset.mul_sum]
  rw [show LaurentPolynomial.eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z scale = -(d⁻¹) from hEvalScale,
    neg_mul, ← mul_neg, ← hsolve, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

/-- A reciprocal-regular ordinary Borel equation yields a monic Laurent
operator on the actual wide function with those factorial coefficients. -/
theorem hasLaurentOperator_of_borel_regular_tuple {f : ℂ → ℂ} (hf : IsWideEFunction f)
    {a : ℕ → AlgebraicComplex} (hs : HasFactorialExpansion f a) (m : ℕ)
    (q : Fin (m + 1) → Polynomial AlgebraicComplex) (hq : q (Fin.last m) ≠ 0)
    (hreg : ReciprocalRegularSingularBounds m q)
    (heq : ∑ i, (q i : PowerSeries AlgebraicComplex) *
      (PowerSeries.derivative AlgebraicComplex)^[i.val] (PowerSeries.mk a) = 0) :
    HasLaurentOperator f := by
  let q' := ordinaryReflectionTuple m q
  have hplus := (ordinaryReflectionTuple_last_and_valuation_iff m q).mpr ⟨hq, hreg⟩
  let d := reciprocalCommonDegree m q'
  let ν := reciprocalSourceDegree m d q'
  let A := reciprocalSourceArray m d q'
  have hdata : 0 < ν ∧ Stage56FiniteFuchs A ∧ A (Fin.last m) (Fin.last ν) ≠ 0 ∧
      signedLaplaceSourceAction A (HahnSeries.single (1 : ℤ) (1 : AlgebraicComplex) *
        HahnSeries.ofPowerSeries ℤ AlgebraicComplex
          (PowerSeries.mk (fun n => (-1 : AlgebraicComplex) ^ n * a n))) = 0 ∧
      (∑ l, (stage53_fourierCoeff A l : PowerSeries AlgebraicComplex) *
        (PowerSeries.derivative AlgebraicComplex)^[l.val] (stage41_strictFormalSeries a)) = 0 :=
    valued_signed_ordinary_original_factorial m q' hplus.1 hplus.2 a
      (ordinaryReflectionTuple_signed_mk a m q heq)
  obtain ⟨hν, hfuchs, hcorner, _, hFourier⟩ := hdata
  have ha := hf.arithmetic_of_expansion hs
  have hactual := factorialSeries_polynomial_relation_of_formal ha ν (stage53_fourierCoeff A) hFourier
  have hSource : factorialSeriesFunction a = f := funext (fun z => (ha.expansion z).unique (hs z))
  rw [hSource] at hactual
  exact hasLaurentOperator_of_monomialLeading ν hν m (stage61_fourierCorner A)
    (stage61_fourierCorner_ne_zero A hcorner) (stage53_fourierCoeff A)
    (actualFourier_leading_monomial A hfuchs) hactual

/-- The divided connection denominator bound already suffices for a Laurent
operator. The scalar tuple is extracted from the same minimal Borel data. -/
theorem hasLaurentOperator_of_subfactorial_borel_connection {f : ℂ → ℂ}
    (hf : IsWideEFunction f) {a : ℕ → AlgebraicComplex} (hs : HasFactorialExpansion f a)
    (F : IntermediateField ℚ AlgebraicComplex) [NumberField F] (hmem : ∀ k, a k ∈ F)
    (n : ℕ) (c : Fin (n + 1) → RatFunc F)
    (hdata : OrdinaryBorelMinimalCyclicData
      (HahnSeries.ofPowerSeries ℤ F (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem))) (n + 1) c)
    (T : Polynomial F) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial F)) (hT : T ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial F) (RatFunc F) (U i j) =
      algebraMap (Polynomial F) (RatFunc F) T * minimalDerivativeCompanion (n + 1) c i j)
    (hden : HasSubfactorialConnectionDenominators T U) :
    HasLaurentOperator f := by
  let G := PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)
  let q := sameCompanionScalarTuple (n + 1) (Nat.succ_pos n) T U
  obtain ⟨_, htop, hL, _⟩ := sameCompanionScalarTuple_spec (HahnSeries.ofPowerSeries ℤ F G)
    (n + 1) (Nat.succ_pos n) c hdata T U hT hclear
  have hreg := hden.reciprocalRegularSingularBounds n c T U hT hclear
  have hPower := powerSeries_equation_of_laurent_scalar_equation G (n + 1) q hL
  obtain ⟨hTop, hReg, hExact⟩ := ordinaryFieldTuple_map F a hmem (n + 1) q htop hreg hPower
  exact hasLaurentOperator_of_borel_regular_tuple hf hs (n + 1) _ hTop hReg hExact

end WideE
