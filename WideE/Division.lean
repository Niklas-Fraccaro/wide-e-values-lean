import WideE.Bounds
import WideE.Taylor
import StrictEDivisionAtOne

/-! Division at one for wide factorial series, including the rational-coefficient case. -/

noncomputable section

namespace WideE

open StrictEUnit

private theorem divisionCoeff_tail_term_bound (a : ℕ → ℂ) (C δ : ℝ)
    (hC : 0 ≤ C) (hδ : δ ≤ 1) (ha : ∀ n, ‖a n‖ ≤ C * (n.factorial : ℝ) ^ δ)
    (n j : ℕ) :
    ‖(n.factorial : ℂ) * (a (j + (n + 1)) / ((j + (n + 1)).factorial : ℂ))‖ ≤
      (C * (n.factorial : ℝ) ^ δ) * (j.factorial : ℝ) ^ (δ - 1) := by
  have hfac : (n.factorial : ℝ) * (j.factorial : ℝ) ≤ ((j + (n + 1)).factorial : ℝ) := by
    exact_mod_cast (Nat.le_of_dvd (Nat.factorial_pos (n + j))
      (Nat.factorial_mul_factorial_dvd_factorial_add n j)).trans
      (Nat.factorial_le (by omega : n + j ≤ j + (n + 1)))
  have hn : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hj : 0 < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hm : 0 < ((j + (n + 1)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j + (n + 1))
  calc
    _ = (n.factorial : ℝ) * (‖a (j + (n + 1))‖ / ((j + (n + 1)).factorial : ℝ)) := by
      rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    _ ≤ (n.factorial : ℝ) *
        ((C * ((j + (n + 1)).factorial : ℝ) ^ δ) / ((j + (n + 1)).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (ha _) hm.le) hn.le
    _ = (C * (n.factorial : ℝ)) * ((j + (n + 1)).factorial : ℝ) ^ (δ - 1) := by
      rw [Real.rpow_sub hm, Real.rpow_one]
      ring
    _ ≤ (C * (n.factorial : ℝ)) *
        ((n.factorial : ℝ) * (j.factorial : ℝ)) ^ (δ - 1) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (mul_pos hn hj) hfac (sub_nonpos.mpr hδ))
        (mul_nonneg hC hn.le)
    _ = _ := by
      rw [Real.mul_rpow hn.le hj.le, Real.rpow_sub hn, Real.rpow_one]
      field_simp [hn.ne']
      ring

private theorem coe_divisionCoeff_succ (a : ℕ → AlgebraicComplex) (n : ℕ) :
    (strictEDivisionCoeff (K := AlgebraicComplex) a (n + 1) : ℂ) =
      (n + 1 : ℂ) * (strictEDivisionCoeff (K := AlgebraicComplex) a n : ℂ) - (a (n + 1) : ℂ) := by
  change (algebraicClosure ℚ ℂ).val.toRingHom (strictEDivisionCoeff a (n + 1)) = _
  simp only [strictEDivisionCoeff, map_sub, map_mul, map_add, map_natCast, map_one]
  rfl

private theorem divisionCoeff_integral {a : ℕ → AlgebraicComplex} (d n : ℕ)
    (ha : ∀ j : ℕ, j ≤ n → IsIntegral ℤ ((d : ℂ) * (a j : ℂ))) :
    ∀ j : ℕ, j ≤ n → IsIntegral ℤ ((d : ℂ) * (strictEDivisionCoeff (K := AlgebraicComplex) a j : ℂ)) := by
  intro j
  induction j with
  | zero =>
    intro hj
    simpa only [strictEDivisionCoeff, IntermediateField.coe_neg, mul_neg] using (ha 0 hj).neg
  | succ j ih =>
    intro hj
    have hmul := (strictE_natCast_isIntegral (j + 1)).mul (ih ((Nat.le_succ j).trans hj))
    rw [coe_divisionCoeff_succ]
    convert hmul.sub (ha (j + 1) hj) using 1
    push_cast
    ring

/-- The original prefix denominators suffice for division. Vanishing of the
factorial series at one in each embedding supplies the conjugate bounds. -/
theorem wideEArithmetic_divisionCoeff_of_conjugate_zeros {a : ℕ → AlgebraicComplex}
    (ha : HasWideEArithmetic a)
    (hzero : ∀ σ : AlgebraicComplex →ₐ[ℚ] ℂ,
      HasSum (fun n => σ (a n) / (n.factorial : ℂ)) 0) :
    HasWideEArithmetic (strictEDivisionCoeff a) := by
  intro ε hε
  let δ := min ε (1 / 2 : ℝ)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ1 : δ < 1 := (min_le_right ε _).trans_lt (by norm_num)
  obtain ⟨C, hC, hσ, d, hd, hdb, hint⟩ := ha δ hδ
  let S := ∑' j : ℕ, (j.factorial : ℝ) ^ (δ - 1)
  have hsum : HasSum (fun j : ℕ => (j.factorial : ℝ) ^ (δ - 1)) S :=
    (summable_factorial_rpow (δ - 1) (sub_neg.mpr hδ1)).hasSum
  let D := max C (C * S)
  have hCD : C ≤ D := le_max_left _ _
  have hD : 1 ≤ D := hC.trans hCD
  refine ⟨D, hD, ?_, d, hd, ?_, fun n => divisionCoeff_integral (d n) n (hint n)⟩
  · intro σ n
    change ‖σ.toRingHom (strictEDivisionCoeff a n)‖ ≤ D * (n.factorial : ℝ) ^ ε
    rw [map_strictEDivisionCoeff]
    have hnorm := (strictEDivisionCoeff_tail_hasSum (fun j => σ (a j)) (hzero σ) n)
      |>.norm_le_of_bounded (hsum.mul_left (C * (n.factorial : ℝ) ^ δ))
        (divisionCoeff_tail_term_bound (fun j => σ (a j)) C δ
          (zero_le_one.trans hC) hδ1.le (hσ σ) n)
    have hF : 1 ≤ (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    calc
      _ ≤ (C * (n.factorial : ℝ) ^ δ) * S := hnorm
      _ = (C * S) * (n.factorial : ℝ) ^ δ := by ring
      _ ≤ D * (n.factorial : ℝ) ^ δ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hF hδε) (zero_le_one.trans hD)
  · intro n
    have hF : 1 ≤ (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    exact (hdb n).trans (mul_le_mul hCD (Real.rpow_le_rpow_of_exponent_le hF hδε)
      (by positivity) (zero_le_one.trans hD))

private theorem divisionCoeff_mul_sub_one {f g : ℂ → ℂ} {a : ℕ → AlgebraicComplex}
    (hf : HasFactorialExpansion f a) (hg : HasFactorialExpansion g (strictEDivisionCoeff a))
    (z : ℂ) : (z - 1) * g z = f z := by
  let b : ℕ → AlgebraicComplex := strictEDivisionCoeff a
  let combined : ℕ → ℂ := fun n => ((a n : ℂ) + (b n : ℂ)) * z ^ n / (n.factorial : ℂ)
  have h0 : combined 0 = 0 := by
    simp [combined, b, strictEDivisionCoeff]
  have hs : HasSum combined (f z + g z) := by
    convert (hf z).add (hg z) using 1
    funext n
    dsimp [combined, b]
    ring
  have htail : HasSum (fun n => combined (n + 1)) (z * g z) := by
    convert (hg z).mul_left z using 1
    funext n
    change ((a (n + 1) : ℂ) + (b (n + 1) : ℂ)) * z ^ (n + 1) /
      ((n + 1).factorial : ℂ) = _
    have hnext : (a (n + 1) : ℂ) + (b (n + 1) : ℂ) = (n + 1 : ℂ) * (b n : ℂ) := by
      dsimp only [b]
      rw [coe_divisionCoeff_succ]
      ring
    rw [hnext]
    exact division_factorial_successor_term (fun j => (b j : ℂ)) z n
  have hfull : HasSum combined (z * g z) := by
    have h := (hasSum_nat_add_iff (f := combined) 1).mp htail
    simpa only [Finset.sum_range_one, h0, add_zero] using h
  have hzg := hs.unique hfull
  rw [sub_mul, one_mul, ← hzg, add_sub_cancel_right]

/-- Construct the entire quotient and its original divided coefficient sequence,
using the vanishing of the coefficient series in every embedding. -/
theorem wideEFunction_divAtOne_of_conjugate_zeros
    {f : ℂ → ℂ} {a : ℕ → AlgebraicComplex}
    (hf : Differentiable ℂ f) (hs : HasFactorialExpansion f a)
    (hODE : HasAlgebraicPolynomialODE f) (ha : HasWideEArithmetic a)
    (hzero : ∀ σ : AlgebraicComplex →ₐ[ℚ] ℂ,
      HasSum (fun n => σ (a n) / (n.factorial : ℂ)) 0) :
    ∃ g : ℂ → ℂ, IsWideEFunction g ∧
      HasFactorialExpansion g (strictEDivisionCoeff a) ∧ ∀ z : ℂ, (z - 1) * g z = f z := by
  let b : ℕ → AlgebraicComplex := strictEDivisionCoeff a
  have hb : HasWideEArithmetic b := wideEArithmetic_divisionCoeff_of_conjugate_zeros ha hzero
  obtain ⟨C, hC, hCb⟩ := hb.chosen_bound (1 / 2) (by norm_num)
  let g := exponentialGeneratingFunction (fun n => (b n : ℂ))
  have hdg : Differentiable ℂ g :=
    half_factorial_egf_differentiable _ C (zero_le_one.trans hC) hCb
  have hsg : HasFactorialExpansion g b :=
    half_factorial_egf_hasSum _ C (zero_le_one.trans hC) hCb
  have hmul := divisionCoeff_mul_sub_one hs hsg
  have hODEg : HasAlgebraicPolynomialODE g := by
    apply (stage14_algebraicPolynomialODE_iff_subfield g).mpr
    exact division_actualSubfieldODE_of_polynomial_mul algebraicSubfield
      (taylorRealization f hf hs) (taylorRealization g hdg hsg)
      (Polynomial.X - Polynomial.C 1) (Polynomial.X_sub_C_ne_zero 1)
      ((stage14_algebraicPolynomialODE_iff_subfield f).mp hODE)
      (by
        intro z
        change (Polynomial.X - Polynomial.C (1 : AlgebraicComplex)).eval₂
          (algebraicClosure ℚ ℂ).val.toRingHom z * g z = f z
        simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
          Polynomial.eval₂_one, map_one] using hmul z)
  exact ⟨g, wideEFunction_of_expansion hdg hsg hODEg hb, hsg, hmul⟩

/-- Rationality of the actual coefficients transports vanishing at one to every
embedding, giving division at one for a wide function with that representation. -/
theorem wideEFunction_divAtOne_of_rational_representation
    {f : ℂ → ℂ} (hf : IsWideEFunction f) (a : ℕ → AlgebraicComplex)
    (hrat : ∀ n, ∃ q : ℚ, a n = algebraMap ℚ AlgebraicComplex q)
    (hs : HasFactorialExpansion f a) (hz : f 1 = 0) :
    ∃ g : ℂ → ℂ, IsWideEFunction g ∧ ∀ z : ℂ, (z - 1) * g z = f z := by
  obtain ⟨b, hd, hsb, hODE, hb, _⟩ := hf
  have ha : HasWideEArithmetic a := (hs.unique hsb hd) ▸ hb
  obtain ⟨g, hg, _, hmul⟩ := wideEFunction_divAtOne_of_conjugate_zeros hd hs hODE ha
    (fun σ => by
      simpa only [strictE_rational_coeff_embedding a hrat σ, one_pow, mul_one, hz] using hs 1)
  exact ⟨g, hg, hmul⟩

end WideE
