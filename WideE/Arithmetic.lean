import WideE.Basic
import WideE.Bounds
import StrictEArithmeticClosure

/-! Wide coefficient bounds and common denominators under the basic operations. -/

noncomputable section

namespace WideE

open StrictEUnit
open scoped BigOperators

private theorem factorial_pos_real (n : ℕ) : 0 < (n.factorial : ℝ) :=
  Nat.cast_pos.mpr (Nat.factorial_pos n)

private theorem factorial_one_le (n : ℕ) : 1 ≤ (n.factorial : ℝ) := by
  exact_mod_cast Nat.factorial_pos n

private theorem factorial_half_mul (ε : ℝ) (n : ℕ) :
    (n.factorial : ℝ) ^ (ε / 2) * (n.factorial : ℝ) ^ (ε / 2) =
      (n.factorial : ℝ) ^ ε := by
  rw [← Real.rpow_add (factorial_pos_real n), add_halves]

private theorem factorial_half_le {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    (n.factorial : ℝ) ^ (ε / 2) ≤ (n.factorial : ℝ) ^ ε :=
  Real.rpow_le_rpow_of_exponent_le (factorial_one_le n) (by linarith)

theorem hasWideEArithmetic_of_strict {a : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) : HasWideEArithmetic a := by
  intro ε hε
  obtain ⟨A, hA, hσ, d, hd, hbound, hi⟩ := ha
  obtain ⟨B, hB, hab⟩ := exists_exp_pow_le_factorial_rpow A ε hA hε
  have h (n : ℕ) : A ^ (n + 1) ≤ (A * B) * (n.factorial : ℝ) ^ ε := by
    rw [pow_succ, mul_comm (A ^ n) A, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hab n) (zero_le_one.trans hA)
  exact ⟨A * B, one_le_mul_of_one_le_of_one_le hA hB,
    fun σ n => (hσ σ n).trans (h n), d, hd, fun n => (hbound n).trans (h n), hi⟩

theorem HasWideEArithmetic.neg {a : ℕ → AlgebraicComplex}
    (ha : HasWideEArithmetic a) : HasWideEArithmetic (fun n => -a n) := by
  intro ε hε
  obtain ⟨A, hA, hσ, d, hd, hbound, hi⟩ := ha ε hε
  refine ⟨A, hA, ?_, d, hd, hbound, ?_⟩
  · intro σ n
    simpa only [map_neg, norm_neg] using hσ σ n
  · intro n j hj
    simpa only [IntermediateField.coe_neg, mul_neg] using (hi n j hj).neg

theorem HasWideEArithmetic.add {a b : ℕ → AlgebraicComplex}
    (ha : HasWideEArithmetic a) (hb : HasWideEArithmetic b) :
    HasWideEArithmetic (fun n => a n + b n) := by
  intro ε hε
  obtain ⟨A, hA, hσa, da, hda, hba, hia⟩ := ha (ε / 2) (by positivity)
  obtain ⟨B, hB, hσb, db, hdb, hbb, hib⟩ := hb (ε / 2) (by positivity)
  have hA0 := zero_le_one.trans hA
  have hB0 := zero_le_one.trans hB
  let C : ℝ := A + B + A * B
  have hsum : A + B ≤ C := le_add_of_nonneg_right (mul_nonneg hA0 hB0)
  have hprod : A * B ≤ C := le_add_of_nonneg_left (add_nonneg hA0 hB0)
  have hC : 1 ≤ C := hA.trans ((le_add_of_nonneg_right hB0).trans hsum)
  refine ⟨C, hC, ?_, (fun n => da n * db n),
    (fun n => Nat.mul_pos (hda n) (hdb n)), ?_, ?_⟩
  · intro σ n
    rw [map_add]
    calc
      ‖σ (a n) + σ (b n)‖ ≤ ‖σ (a n)‖ + ‖σ (b n)‖ := norm_add_le _ _
      _ ≤ A * (n.factorial : ℝ) ^ (ε / 2) + B * (n.factorial : ℝ) ^ (ε / 2) :=
        add_le_add (hσa σ n) (hσb σ n)
      _ = (A + B) * (n.factorial : ℝ) ^ (ε / 2) := (add_mul _ _ _).symm
      _ ≤ C * (n.factorial : ℝ) ^ ε :=
        mul_le_mul hsum (factorial_half_le hε.le n) (by positivity) (zero_le_one.trans hC)
  · intro n
    push_cast
    calc
      (da n : ℝ) * (db n : ℝ) ≤
          (A * (n.factorial : ℝ) ^ (ε / 2)) * (B * (n.factorial : ℝ) ^ (ε / 2)) :=
        mul_le_mul (hba n) (hbb n) (Nat.cast_nonneg _) (by positivity)
      _ = A * B * (n.factorial : ℝ) ^ ε := by
        rw [← factorial_half_mul ε n]
        ring
      _ ≤ C * (n.factorial : ℝ) ^ ε := mul_le_mul_of_nonneg_right hprod (by positivity)
  · intro n j hj
    have hi := ((strictE_natCast_isIntegral (db n)).mul (hia n j hj)).add
      ((strictE_natCast_isIntegral (da n)).mul (hib n j hj))
    convert hi using 1
    simp only [Nat.cast_mul, IntermediateField.coe_add]
    ring

theorem HasWideEArithmetic.sub {a b : ℕ → AlgebraicComplex}
    (ha : HasWideEArithmetic a) (hb : HasWideEArithmetic b) :
    HasWideEArithmetic (fun n => a n - b n) := by
  simpa only [sub_eq_add_neg] using ha.add hb.neg

theorem HasWideEArithmetic.mul_pointwise {a b : ℕ → AlgebraicComplex}
    (ha : HasWideEArithmetic a) (hb : HasWideEArithmetic b) :
    HasWideEArithmetic (fun n => a n * b n) := by
  intro ε hε
  obtain ⟨A, hA, hσa, da, hda, hba, hia⟩ := ha (ε / 2) (by positivity)
  obtain ⟨B, hB, hσb, db, hdb, hbb, hib⟩ := hb (ε / 2) (by positivity)
  have hA0 := zero_le_one.trans hA
  have h (n : ℕ) :
      (A * (n.factorial : ℝ) ^ (ε / 2)) * (B * (n.factorial : ℝ) ^ (ε / 2)) =
        A * B * (n.factorial : ℝ) ^ ε := by
    rw [← factorial_half_mul ε n]
    ring
  refine ⟨A * B, one_le_mul_of_one_le_of_one_le hA hB, ?_,
    (fun n => da n * db n), (fun n => Nat.mul_pos (hda n) (hdb n)), ?_, ?_⟩
  · intro σ n
    rw [map_mul, norm_mul, ← h n]
    exact mul_le_mul (hσa σ n) (hσb σ n) (norm_nonneg _) (by positivity)
  · intro n
    rw [Nat.cast_mul, ← h n]
    exact mul_le_mul (hba n) (hbb n) (Nat.cast_nonneg _) (by positivity)
  · intro n j hj
    convert (hia n j hj).mul (hib n j hj) using 1
    simp only [Nat.cast_mul, IntermediateField.coe_mul]
    ring

theorem HasWideEArithmetic.const_mul {a : ℕ → AlgebraicComplex}
    (ha : HasWideEArithmetic a) (α : AlgebraicComplex) :
    HasWideEArithmetic (fun n => α * a n) := by
  have hα : HasWideEArithmetic (fun _ : ℕ => α) := by
    simpa only [one_pow, mul_one] using
      hasWideEArithmetic_of_strict (algebraic_scalar_exp_arithmetic α 1)
  exact hα.mul_pointwise ha

theorem HasWideEArithmetic.rescale {a : ℕ → AlgebraicComplex}
    (ha : HasWideEArithmetic a) (α : AlgebraicComplex) :
    HasWideEArithmetic (fun n => a n * α ^ n) := by
  have hα : HasWideEArithmetic (fun n : ℕ => α ^ n) := by
    simpa only [one_mul] using
      hasWideEArithmetic_of_strict (algebraic_scalar_exp_arithmetic 1 α)
  exact ha.mul_pointwise hα

/-- Differentiation shifts the factorial-normalized sequence and its prefix
denominators by one index. -/
theorem HasWideEArithmetic.shift {a : ℕ → AlgebraicComplex}
    (ha : HasWideEArithmetic a) : HasWideEArithmetic (fun n => a (n + 1)) := by
  intro ε hε
  obtain ⟨A, hA, hσ, d, hd, hbd, hi⟩ := ha (ε / 2) (by positivity)
  obtain ⟨B, hB, hpoly⟩ :=
    exists_exp_pow_mul_succ_rpow_le_factorial_rpow 1 (ε / 2) (ε / 2)
      le_rfl (by positivity) (by positivity)
  have hbound (n : ℕ) :
      A * ((n + 1).factorial : ℝ) ^ (ε / 2) ≤ A * B * (n.factorial : ℝ) ^ ε := by
    have hpoly' : ((n : ℝ) + 1) ^ (ε / 2) ≤ B * (n.factorial : ℝ) ^ (ε / 2) := by
      simpa only [one_pow, one_mul] using hpoly n
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
      Real.mul_rpow (by positivity) (by positivity)]
    calc
      _ ≤ A * ((B * (n.factorial : ℝ) ^ (ε / 2)) *
          (n.factorial : ℝ) ^ (ε / 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpoly' (by positivity))
          (zero_le_one.trans hA)
      _ = _ := by
        rw [← factorial_half_mul ε n]
        ring
  exact ⟨A * B, one_le_mul_of_one_le_of_one_le hA hB,
    fun σ n => (hσ σ (n + 1)).trans (hbound n),
    fun n => d (n + 1), fun n => hd (n + 1),
    fun n => (hbd (n + 1)).trans (hbound n),
    fun n j hj => hi (n + 1) (j + 1) (Nat.succ_le_succ hj)⟩

private theorem factorial_pair_le (n k : ℕ) (hk : k ≤ n) :
    (k.factorial : ℝ) * ((n - k).factorial : ℝ) ≤ (n.factorial : ℝ) := by
  have hdiv := Nat.factorial_mul_factorial_dvd_factorial_add k (n - k)
  rw [Nat.add_sub_of_le hk] at hdiv
  exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos n) hdiv

private theorem binomial_bound (a b : ℕ → ℂ) (A B δ : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (ha : ∀ n, ‖a n‖ ≤ A * (n.factorial : ℝ) ^ δ)
    (hb : ∀ n, ‖b n‖ ≤ B * (n.factorial : ℝ) ^ δ) (n : ℕ) :
    ‖∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * a k * b (n - k)‖ ≤
      (A * B * (n.factorial : ℝ) ^ δ) * (2 : ℝ) ^ n := by
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), ‖(n.choose k : ℂ) * a k * b (n - k)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        (A * B * (n.factorial : ℝ) ^ δ) * (n.choose k : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      have hnorm : ‖a k‖ * ‖b (n - k)‖ ≤ A * B * (n.factorial : ℝ) ^ δ := by
        calc
          _ ≤ (A * (k.factorial : ℝ) ^ δ) * (B * ((n - k).factorial : ℝ) ^ δ) :=
            mul_le_mul (ha k) (hb _) (norm_nonneg _) (by positivity)
          _ = A * B * ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) ^ δ := by
            rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity) (factorial_pair_le n k hkn) hδ)
            (mul_nonneg hA hB)
      simpa only [mul_comm _ (n.choose k : ℝ), mul_assoc, mul_left_comm] using
        mul_le_mul_of_nonneg_right hnorm (Nat.cast_nonneg (n.choose k))
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact_mod_cast Nat.sum_range_choose n

/-- The binomial product formula preserves both wide arithmetic conditions. -/
theorem HasWideEArithmetic.binomialConvolution {a b : ℕ → AlgebraicComplex}
    (ha : HasWideEArithmetic a) (hb : HasWideEArithmetic b) :
    HasWideEArithmetic (strictEBinomialConvolution a b) := by
  intro ε hε
  obtain ⟨A, hA, hσa, da, hda, hba, hia⟩ := ha (ε / 2) (by positivity)
  obtain ⟨B, hB, hσb, db, hdb, hbb, hib⟩ := hb (ε / 2) (by positivity)
  obtain ⟨D, hD, hd⟩ := exists_exp_pow_le_factorial_rpow 2 (ε / 2) (by norm_num) (by positivity)
  have hA0 := zero_le_one.trans hA
  have hB0 := zero_le_one.trans hB
  have hAB := one_le_mul_of_one_le_of_one_le hA hB
  refine ⟨A * B * D, one_le_mul_of_one_le_of_one_le hAB hD, ?_,
    (fun n => da n * db n), (fun n => Nat.mul_pos (hda n) (hdb n)), ?_, ?_⟩
  · intro σ n
    simp only [strictEBinomialConvolution, map_sum, map_mul, map_natCast]
    calc
      _ ≤ (A * B * (n.factorial : ℝ) ^ (ε / 2)) * (2 : ℝ) ^ n :=
        binomial_bound _ _ A B (ε / 2) hA0 hB0 (by positivity) (hσa σ) (hσb σ) n
      _ ≤ (A * B * (n.factorial : ℝ) ^ (ε / 2)) * (D * (n.factorial : ℝ) ^ (ε / 2)) :=
        mul_le_mul_of_nonneg_left (hd n) (by positivity)
      _ = _ := by
        rw [← factorial_half_mul ε n]
        ring
  · intro n
    rw [Nat.cast_mul]
    calc
      (da n : ℝ) * (db n : ℝ) ≤
          (A * (n.factorial : ℝ) ^ (ε / 2)) * (B * (n.factorial : ℝ) ^ (ε / 2)) :=
        mul_le_mul (hba n) (hbb n) (Nat.cast_nonneg _) (by positivity)
      _ = A * B * (n.factorial : ℝ) ^ ε := by
        rw [← factorial_half_mul ε n]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hD) (by positivity)
  · intro n j hj
    change IsIntegral ℤ (((da n * db n : ℕ) : ℂ) *
      (algebraicClosure ℚ ℂ).val (strictEBinomialConvolution a b j))
    simp only [strictEBinomialConvolution, map_sum, map_mul, map_natCast,
      Nat.cast_mul, Finset.mul_sum]
    apply IsIntegral.sum
    intro k hk
    have hkj : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hi := (strictE_natCast_isIntegral (j.choose k)).mul
      ((hia n k (hkj.trans hj)).mul (hib n (j - k) ((Nat.sub_le j k).trans hj)))
    change IsIntegral ℤ ((da n : ℂ) * (db n : ℂ) *
      ((j.choose k : ℂ) * (a k : ℂ) * (b (j - k) : ℂ)))
    convert hi using 1
    ring

end WideE
