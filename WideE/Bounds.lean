import Stage41GeometricEntireSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Subfactorial bounds and entire factorial series

These estimates use real powers of factorials and apply to any complex
coefficient sequence. A half-factorial coefficient bound gives absolute
convergence everywhere and quadratic exponential growth.
-/

open Filter
open scoped Topology

noncomputable section

namespace WideE

/-- Any positive factorial power absorbs an exponential sequence. -/
theorem exists_exp_pow_le_factorial_rpow (A ε : ℝ) (hA : 1 ≤ A) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, A ^ n ≤ C * (n.factorial : ℝ) ^ ε := by
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hB0 : 0 ≤ A ^ ε⁻¹ := Real.rpow_nonneg hA0 _
  obtain ⟨B, hB⟩ := exists_nat_ge (A ^ ε⁻¹)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Nat.eventually_pow_lt_factorial_sub B 0)
  refine ⟨A ^ N, one_le_pow₀ hA, fun n => ?_⟩
  have hC : 0 ≤ A ^ N := pow_nonneg hA0 _
  by_cases hn : N ≤ n
  · have hbound : (A ^ ε⁻¹) ^ n ≤ (n.factorial : ℝ) := by
      apply (pow_le_pow_left₀ hB0 hB n).trans
      exact_mod_cast (by simpa only [Nat.sub_zero] using (hN n hn).le)
    calc
      A ^ n = ((A ^ ε⁻¹) ^ ε) ^ n := by rw [Real.rpow_inv_rpow hA0 hε.ne']
      _ = ((A ^ ε⁻¹) ^ n) ^ ε := by
        rw [← Real.rpow_mul_natCast hB0, ← Real.rpow_natCast_mul hB0, mul_comm]
      _ ≤ (n.factorial : ℝ) ^ ε :=
        Real.rpow_le_rpow (pow_nonneg hB0 _) hbound hε.le
      _ ≤ A ^ N * (n.factorial : ℝ) ^ ε :=
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ hA)
  · have hF : (1 : ℝ) ≤ (n.factorial : ℝ) :=
      by exact_mod_cast Nat.factorial_pos n
    exact (pow_le_pow_right₀ hA (le_of_not_ge hn)).trans
      (le_mul_of_one_le_right hC (Real.one_le_rpow hF hε.le))

/-- A polynomial factor can be included in the same absorption estimate. -/
theorem exists_exp_pow_mul_succ_rpow_le_factorial_rpow (A b ε : ℝ)
    (hA : 1 ≤ A) (hb : 0 ≤ b) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ,
      A ^ n * ((n : ℝ) + 1) ^ b ≤ C * (n.factorial : ℝ) ^ ε := by
  have hB : 1 ≤ A * (2 : ℝ) ^ b :=
    one_le_mul_of_one_le_of_one_le hA (Real.one_le_rpow (by norm_num) hb)
  obtain ⟨C, hC, hCb⟩ := exists_exp_pow_le_factorial_rpow (A * (2 : ℝ) ^ b) ε hB hε
  refine ⟨C, hC, fun n => ?_⟩
  have hn : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
    exact_mod_cast Nat.lt_two_pow_self (n := n)
  calc
    A ^ n * ((n : ℝ) + 1) ^ b ≤ A ^ n * ((2 : ℝ) ^ n) ^ b :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hn hb) (by positivity)
    _ = (A * (2 : ℝ) ^ b) ^ n := by
      rw [mul_pow, ← Real.rpow_natCast_mul (by norm_num : 0 ≤ (2 : ℝ)),
        ← Real.rpow_mul_natCast (by norm_num : 0 ≤ (2 : ℝ)), mul_comm (n : ℝ)]
    _ ≤ C * (n.factorial : ℝ) ^ ε := hCb n

/-- Every negative real power of the factorial is summable. -/
theorem summable_factorial_rpow (ε : ℝ) (hε : ε < 0) :
    Summable (fun n : ℕ => (n.factorial : ℝ) ^ ε) := by
  obtain ⟨C, _, hC⟩ := exists_exp_pow_le_factorial_rpow 2 (-ε) (by norm_num)
    (neg_pos.mpr hε)
  apply Summable.of_nonneg_of_le (fun n => by positivity)
    (f := fun n : ℕ => C * (1 / 2 : ℝ) ^ n)
  · intro n
    have hF : 0 < (n.factorial : ℝ) ^ (-ε) := by positivity
    have hpow : 0 < (2 : ℝ) ^ n := by positivity
    calc
      (n.factorial : ℝ) ^ ε = 1 / (n.factorial : ℝ) ^ (-ε) := by
        rw [Real.rpow_neg (by positivity : 0 ≤ (n.factorial : ℝ)), one_div, inv_inv]
      _ ≤ C / (2 : ℝ) ^ n := by
        rw [div_le_div_iff₀ hF hpow, one_mul]
        exact hC n
      _ = C * (1 / 2 : ℝ) ^ n := by rw [div_pow, one_pow, div_eq_mul_inv, one_div]
  · exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left C

private theorem pow_div_sqrt_factorial_le (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    r ^ n / Real.sqrt (n.factorial : ℝ) ≤ Real.exp (r ^ 2) * (Real.sqrt (1 / 2)) ^ n := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  have hrpow : (2 * r ^ 2) ^ n / (n.factorial : ℝ) ≤ Real.exp (2 * r ^ 2) :=
    Real.pow_div_factorial_le_exp _ (by positivity) n
  have hmul : 2 * r ^ 2 * (1 / 2 : ℝ) = r ^ 2 := by ring
  have hexp : Real.exp (r ^ 2) ^ 2 = Real.exp (2 * r ^ 2) := by
    simpa using (Real.exp_nat_mul (r ^ 2) 2).symm
  calc
    (r ^ n / Real.sqrt (n.factorial : ℝ)) ^ 2 = (r ^ 2) ^ n / (n.factorial : ℝ) := by
      rw [div_pow, ← pow_mul, Nat.mul_comm n, pow_mul, Real.sq_sqrt (by positivity)]
    _ = (2 * r ^ 2) ^ n / (n.factorial : ℝ) * (1 / 2 : ℝ) ^ n := by
      rw [div_mul_eq_mul_div, ← mul_pow, hmul]
    _ ≤ Real.exp (2 * r ^ 2) * (1 / 2 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right hrpow (by positivity)
    _ = (Real.exp (r ^ 2) * (Real.sqrt (1 / 2)) ^ n) ^ 2 := by
      rw [mul_pow, hexp, ← pow_mul, Nat.mul_comm n, pow_mul, Real.sq_sqrt (by norm_num)]

private theorem half_factorial_majorant_hasSum (C r : ℝ) :
    HasSum (fun n : ℕ => (C * Real.exp (r ^ 2)) * (Real.sqrt (1 / 2)) ^ n)
      ((C * Real.exp (r ^ 2)) * (1 - Real.sqrt (1 / 2))⁻¹) := by
  have hq : Real.sqrt (1 / 2 : ℝ) < Real.sqrt 1 :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hn : ‖Real.sqrt (1 / 2 : ℝ)‖ < 1 := by
    simpa only [Real.sqrt_one, Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hq
  exact (hasSum_geometric_of_norm_lt_one hn).mul_left (C * Real.exp (r ^ 2))

private theorem half_factorial_egf_term_norm_le (a : ℕ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C * (n.factorial : ℝ) ^ (1 / 2 : ℝ))
    (z : ℂ) (n : ℕ) :
    ‖a n * z ^ n / (n.factorial : ℂ)‖ ≤
      (C * Real.exp (‖z‖ ^ 2)) * (Real.sqrt (1 / 2)) ^ n := by
  have hF : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hS : 0 < Real.sqrt (n.factorial : ℝ) := Real.sqrt_pos.2 hF
  have hab := ha n
  rw [← Real.sqrt_eq_rpow] at hab
  calc
    ‖a n * z ^ n / (n.factorial : ℂ)‖ = ‖a n‖ * ‖z‖ ^ n / (n.factorial : ℝ) := by
      rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast]
    _ ≤ C * Real.sqrt (n.factorial : ℝ) * ‖z‖ ^ n / (n.factorial : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hab (by positivity)) hF.le
    _ = C * (‖z‖ ^ n / Real.sqrt (n.factorial : ℝ)) := by
      field_simp [hF.ne', hS.ne']
      calc
        _ = C * ‖z‖ ^ n * (Real.sqrt (n.factorial : ℝ) * Real.sqrt (n.factorial : ℝ)) := by
          ring
        _ = _ := by rw [Real.mul_self_sqrt hF.le]
    _ ≤ (C * Real.exp (‖z‖ ^ 2)) * (Real.sqrt (1 / 2)) ^ n := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (pow_div_sqrt_factorial_le ‖z‖ (norm_nonneg _) n) hC

/-- A half-factorial coefficient bound gives absolute convergence at every complex point. -/
theorem half_factorial_egf_summable_norm (a : ℕ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C * (n.factorial : ℝ) ^ (1 / 2 : ℝ)) (z : ℂ) :
    Summable (fun n : ℕ => ‖a n * z ^ n / (n.factorial : ℂ)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (half_factorial_egf_term_norm_le a C hC ha z)
    (half_factorial_majorant_hasSum C ‖z‖).summable

/-- The actual exponential generating function has its factorial-normalized sum everywhere. -/
theorem half_factorial_egf_hasSum (a : ℕ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C * (n.factorial : ℝ) ^ (1 / 2 : ℝ)) (z : ℂ) :
    HasSum (fun n : ℕ => a n * z ^ n / (n.factorial : ℂ))
      (StrictEUnit.exponentialGeneratingFunction a z) :=
  (half_factorial_egf_summable_norm a C hC ha z).of_norm.hasSum

/-- A half-factorial coefficient bound gives quadratic exponential growth. -/
theorem function_norm_le_of_half_factorial_egf (a : ℕ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C * (n.factorial : ℝ) ^ (1 / 2 : ℝ)) {f : ℂ → ℂ}
    (hf : ∀ z, HasSum (fun n : ℕ => a n * z ^ n / (n.factorial : ℂ)) (f z)) (z : ℂ) :
    ‖f z‖ ≤ (C * (1 - Real.sqrt (1 / 2))⁻¹) * Real.exp (‖z‖ ^ 2) := by
  rw [mul_right_comm]
  exact (hf z).norm_le_of_bounded (half_factorial_majorant_hasSum C ‖z‖)
    (half_factorial_egf_term_norm_le a C hC ha z)

/-- A half-factorial coefficient bound gives the actual global analytic power series. -/
theorem half_factorial_egf_hasFPowerSeriesOnBall (a : ℕ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C * (n.factorial : ℝ) ^ (1 / 2 : ℝ)) :
    HasFPowerSeriesOnBall (StrictEUnit.exponentialGeneratingFunction a)
      (StrictEUnit.stage41_factorialMultilinearSeries a) 0 ⊤ := by
  have hr : (StrictEUnit.stage41_factorialMultilinearSeries a).radius = ⊤ := by
    apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
    intro r
    convert half_factorial_egf_summable_norm a C hC ha ((r : ℝ) : ℂ) using 1
    funext n
    simp only [StrictEUnit.stage41_factorialMultilinearSeries,
      ContinuousMultilinearMap.norm_mkPiRing, norm_div, norm_mul, norm_pow, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg]
    ring
  refine ⟨by rw [hr], by simp, ?_⟩
  intro z _
  convert half_factorial_egf_hasSum a C hC ha z using 1
  · funext n
    simp only [StrictEUnit.stage41_factorialMultilinearSeries,
      ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    ring
  · simp

/-- The sum of the factorial series is entire. -/
theorem half_factorial_egf_differentiable (a : ℕ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C * (n.factorial : ℝ) ^ (1 / 2 : ℝ)) :
    Differentiable ℂ (StrictEUnit.exponentialGeneratingFunction a) :=
  fun z => ((half_factorial_egf_hasFPowerSeriesOnBall a C hC ha).analyticAt_of_mem
    (y := z) (by simp)).differentiableAt

end WideE
