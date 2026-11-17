import WideE.Arithmetic
import WideE.Taylor
import StrictEArithmeticSeries
import StrictEPolynomialCombination
import Stage15StrictEDerivativeClosure
import StrictEAlgebraicRescaling

/-! The analytic, differential and arithmetic clauses of wide E-function
closure are kept on the same actual functions and coefficient sequences. -/

noncomputable section

namespace WideE

open StrictEUnit
open scoped BigOperators

/-- The strict class is contained in the wide class. -/
theorem isWideEFunction_of_strict {f : ℂ → ℂ} (hf : IsStrictEFunction f) :
    IsWideEFunction f := by
  obtain ⟨a, hd, hs, hODE, ha⟩ := hf
  exact wideEFunction_of_expansion hd hs hODE (hasWideEArithmetic_of_strict ha)

theorem isWideEFunction_const (α : AlgebraicComplex) :
    IsWideEFunction (fun _ => (α : ℂ)) :=
  isWideEFunction_of_strict (algebraic_constant_isStrictEFunction α)

theorem isWideEFunction_coordinate : IsWideEFunction (fun z : ℂ => z) :=
  isWideEFunction_of_strict strictEFunction_coordinate

theorem HasWideEArithmetic.variation_summable {a : ℕ → AlgebraicComplex}
    (ha : HasWideEArithmetic a) (z : ℂ) :
    Summable (fun n => ‖(a n : ℂ) * z ^ n / (n.factorial : ℂ)‖) := by
  obtain ⟨C, hC, hbound⟩ := ha.chosen_bound (1 / 2) (by norm_num)
  exact half_factorial_egf_summable_norm (fun n => (a n : ℂ)) C
    (zero_le_one.trans hC) hbound z

theorem IsWideEFunction.quadratic_exp_bound {f : ℂ → ℂ} (hf : IsWideEFunction f) :
    ∃ C : ℝ, 0 < C ∧ ∀ z, ‖f z‖ ≤ C * Real.exp (‖z‖ ^ 2) := by
  obtain ⟨a, _, hs, _, ha, _⟩ := hf
  obtain ⟨C, hC, hbound⟩ := ha.chosen_bound (1 / 2) (by norm_num)
  have hroot : Real.sqrt (1 / 2) < 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  exact ⟨C * (1 - Real.sqrt (1 / 2))⁻¹,
    mul_pos (zero_lt_one.trans_le hC) (inv_pos.mpr (sub_pos.mpr hroot)),
    function_norm_le_of_half_factorial_egf _ C (zero_le_one.trans hC) hbound hs⟩

theorem IsWideEFunction.add {f g : ℂ → ℂ} (hf : IsWideEFunction f) (hg : IsWideEFunction g) :
    IsWideEFunction (fun z => f z + g z) := by
  obtain ⟨a, hdf, hsf, hof, haf, _⟩ := hf
  obtain ⟨b, hdg, hsg, hog, hag, _⟩ := hg
  have hODE : HasAlgebraicPolynomialODE (fun z => f z + g z) :=
    stage14_actualSubfieldODE_add algebraicSubfield
      (taylorRealization f hdf hsf) (taylorRealization g hdg hsg) hof hog
  exact wideEFunction_of_expansion (hdf.add hdg)
    (fun z => strictE_egf_hasSum_add (hsf z) (hsg z)) hODE (haf.add hag)

theorem IsWideEFunction.mul {f g : ℂ → ℂ} (hf : IsWideEFunction f) (hg : IsWideEFunction g) :
    IsWideEFunction (fun z => f z * g z) := by
  obtain ⟨a, hdf, hsf, hof, haf, _⟩ := hf
  obtain ⟨b, hdg, hsg, hog, hag, _⟩ := hg
  have hODE : HasAlgebraicPolynomialODE (fun z => f z * g z) :=
    stage14_actualSubfieldODE_mul algebraicSubfield
      (taylorRealization f hdf hsf) (taylorRealization g hdg hsg) hof hog
  apply wideEFunction_of_expansion (hdf.mul hdg) _ hODE (haf.binomialConvolution hag)
  intro z
  have h := hasSum_sum_range_mul_of_summable_norm
    (haf.variation_summable z) (hag.variation_summable z)
  rw [(hsf z).tsum_eq, (hsg z).tsum_eq] at h
  convert h using 1
  funext n
  change (algebraicClosure ℚ ℂ).val (strictEBinomialConvolution a b n) * z ^ n /
    (n.factorial : ℂ) = _
  simpa only [strictEBinomialConvolution, map_sum, map_mul, map_natCast] using
    strictE_binomial_egf_term (fun k => (a k : ℂ)) (fun k => (b k : ℂ)) z n

theorem IsWideEFunction.const_mul {f : ℂ → ℂ} (hf : IsWideEFunction f) (α : AlgebraicComplex) :
    IsWideEFunction (fun z => (α : ℂ) * f z) :=
  (isWideEFunction_const α).mul hf

theorem IsWideEFunction.neg {f : ℂ → ℂ} (hf : IsWideEFunction f) :
    IsWideEFunction (fun z => -f z) := by
  simpa only [IntermediateField.coe_neg, IntermediateField.coe_one, neg_one_mul] using
    hf.const_mul (-1)

theorem IsWideEFunction.sub {f g : ℂ → ℂ} (hf : IsWideEFunction f) (hg : IsWideEFunction g) :
    IsWideEFunction (fun z => f z - g z) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem IsWideEFunction.derivative {f : ℂ → ℂ} (hf : IsWideEFunction f) :
    IsWideEFunction (deriv f) := by
  obtain ⟨a, hd, hs, hODE, ha, _⟩ := hf
  have hderivODE : HasAlgebraicPolynomialODE (deriv f) :=
    stage15_actualSubfieldODE_derivative algebraicSubfield (taylorRealization f hd hs) hODE
  exact wideEFunction_of_expansion (differentiableOn_univ.mp (hd.differentiableOn.deriv isOpen_univ))
    (strictE_egf_hasSum_derivative hd hs) hderivODE ha.shift

theorem IsWideEFunction.iteratedDeriv {f : ℂ → ℂ} (hf : IsWideEFunction f) (r : ℕ) :
    IsWideEFunction (iteratedDeriv r f) := by
  induction r with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ r ih =>
    rw [iteratedDeriv_succ]
    exact ih.derivative

theorem IsWideEFunction.rescale {f : ℂ → ℂ} (hf : IsWideEFunction f) (α : AlgebraicComplex) :
    IsWideEFunction (fun z => f ((α : ℂ) * z)) := by
  by_cases hα : α = 0
  · let a : AlgebraicComplex := ⟨f 0, mem_algebraicClosure_iff.mpr hf.zero_isAlgebraic⟩
    simpa only [hα, IntermediateField.coe_zero, zero_mul] using isWideEFunction_const a
  · obtain ⟨a, hd, hs, hODE, ha, _⟩ := hf
    exact wideEFunction_of_expansion
      (hd.comp ((differentiable_const (α : ℂ)).mul differentiable_id))
      (strictE_series_rescale hs α) (algebraicPolynomialODE_rescale hd hODE hα) (ha.rescale α)

theorem isWideEFunction_polynomial (p : Polynomial AlgebraicComplex) :
    IsWideEFunction (fun z => p.eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z) :=
  isWideEFunction_of_strict (strictEFunction_polynomialEvaluation p)

end WideE
