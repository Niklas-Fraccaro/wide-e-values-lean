import WideE.ReciprocalRegularity
import TypeIIJointArithmeticAssembly
import UniformPolynomialDualAnnihilatorExistence
import OrdinaryDerivativePrefixArithmetic
import Mathlib.Data.Nat.Choose.Bounds

/-! Subfactorial denominators for the divided connection matrices of the
minimal ordinary Borel companion. -/

noncomputable section

set_option maxHeartbeats 1200000

namespace WideE

open StrictEUnit
open scoped BigOperators NumberField Matrix

private theorem factorial_add_bound (m n : ℕ) :
    (m + n).factorial ≤ 2 ^ (m + n) * (m.factorial * n.factorial) := by
  have hc : (m + n).choose n ≤ 2 ^ (m + n) := by
    rw [← Nat.sum_range_choose]
    exact Finset.single_le_sum (f := (m + n).choose)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  rw [← Nat.add_choose_mul_factorial_mul_factorial m n, Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ hc

private theorem factorial_mul_bound (a n : ℕ) :
    (a * n).factorial ≤ 2 ^ (a * a * n) * n.factorial ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hexp : a * n + n + a * a * n ≤ (a + 1) * (a + 1) * n := by
      rw [← Nat.succ_mul, ← add_mul]
      exact Nat.mul_le_mul_right _ (by nlinarith)
    calc
      _ = (a * n + n).factorial := by rw [Nat.succ_mul]
      _ ≤ 2 ^ (a * n + n) * ((a * n).factorial * n.factorial) := factorial_add_bound _ _
      _ ≤ 2 ^ (a * n + n) * ((2 ^ (a * a * n) * n.factorial ^ a) * n.factorial) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ih)
      _ = 2 ^ (a * n + n + a * a * n) * n.factorial ^ (a + 1) := by
        simp only [pow_add, pow_succ]
        ac_rfl
      _ ≤ _ := Nat.mul_le_mul_right _ (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hexp)

/-- Replacing the cutoff by a fixed affine multiple only multiplies the
factorial exponent by that fixed multiple, up to an exponential factor. -/
theorem exists_affine_factorial_rpow_bound (a : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ s : ℕ,
      (((a * (s + 1)).factorial : ℕ) : ℝ) ^ ε ≤
        B ^ (s + 1) * (s.factorial : ℝ) ^ ((a : ℝ) * ε) := by
  let B : ℝ := ((2 : ℝ) ^ (a * a + a)) ^ ε
  refine ⟨B, Real.one_le_rpow (one_le_pow₀ (by norm_num)) hε, fun s => ?_⟩
  have hs : s + 1 ≤ 2 ^ (s + 1) := Nat.lt_two_pow_self.le
  have hn : (a * (s + 1)).factorial ≤ 2 ^ ((a * a + a) * (s + 1)) * s.factorial ^ a := by
    calc
      _ ≤ 2 ^ (a * a * (s + 1)) * (s + 1).factorial ^ a := factorial_mul_bound _ _
      _ ≤ 2 ^ (a * a * (s + 1)) * ((2 ^ (s + 1)) ^ a * s.factorial ^ a) := by
        rw [Nat.factorial_succ, mul_pow]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hs _))
      _ = _ := by
        rw [show (2 : ℕ) ^ ((a * a + a) * (s + 1)) =
          2 ^ (a * a * (s + 1)) * (2 ^ (s + 1)) ^ a by
          rw [add_mul, pow_add, ← pow_mul, Nat.mul_comm (s + 1) a]]
        ac_rfl
  calc
    _ ≤ ((2 : ℝ) ^ ((a * a + a) * (s + 1)) * (s.factorial : ℝ) ^ a) ^ ε :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn) hε
    _ = B ^ (s + 1) * (s.factorial : ℝ) ^ ((a : ℝ) * ε) := by
      rw [Real.mul_rpow (by positivity) (by positivity), pow_mul (2 : ℝ),
        ← Real.rpow_natCast_mul (by positivity), ← Real.rpow_mul_natCast (by positivity),
        mul_comm ((s + 1 : ℕ) : ℝ) ε]
      rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ (s.factorial : ℝ))]

private theorem affine_prefix_height_le (A L s : ℕ) (η C B : ℝ)
    (hη : 0 ≤ η) (hC : 1 ≤ C)
    (hstretch : (((A * (s + 1)).factorial : ℕ) : ℝ) ^ η ≤
      B ^ (s + 1) * (s.factorial : ℝ) ^ ((A : ℝ) * η))
    (hB : 1 ≤ B) (hL : L ≤ A * (s + 1)) :
    C * (L.factorial : ℝ) ^ η ≤ (C * B) ^ (s + 1) * (s.factorial : ℝ) ^ ((A : ℝ) * η) := by
  have hFact : (L.factorial : ℝ) ^ η ≤ B ^ (s + 1) * (s.factorial : ℝ) ^ ((A : ℝ) * η) :=
    (Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.factorial_le hL) hη).trans hstretch
  have hCpow : C ≤ C ^ (s + 1) := le_self_pow₀ hC (by omega)
  calc
    _ ≤ C * (B ^ (s + 1) * (s.factorial : ℝ) ^ ((A : ℝ) * η)) :=
      mul_le_mul_of_nonneg_left hFact (by positivity)
    _ ≤ _ := by
      rw [mul_pow, mul_assoc]
      exact mul_le_mul_of_nonneg_right hCpow (by positivity)

private theorem subfactorial_norm_absorb (E D ε : ℝ) (hE : 0 ≤ E) (n : ℕ)
    (hAbsorb : E ^ n ≤ D * (n.factorial : ℝ) ^ (ε / 2)) :
    E ^ (n + 1) * (n.factorial : ℝ) ^ (ε / 2) ≤ E * D * (n.factorial : ℝ) ^ ε := by
  have hF : (n.factorial : ℝ) ^ (ε / 2) * (n.factorial : ℝ) ^ (ε / 2) =
      (n.factorial : ℝ) ^ ε := by rw [← Real.rpow_add (by positivity), add_halves]
  rw [pow_succ, mul_comm (E ^ n) E, mul_assoc, ← hF]
  calc
    _ ≤ E * ((D * (n.factorial : ℝ) ^ (ε / 2)) * (n.factorial : ℝ) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAbsorb (by positivity)) hE
    _ = _ := by ring

/-- Integral prefixes for a formal vector with a single subfactorial bound
on both its positive denominator and the house of its cleared coefficients. -/
def HasSubfactorialIntegralPrefixes {K : Type*} [Field K] [NumberField K]
    {r : ℕ} (f : Fin r → PowerSeries K) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧
    ∃ δ : ℕ → ℕ, (∀ L, 0 < δ L) ∧
      (∀ L, (δ L : ℝ) ≤ C * (L.factorial : ℝ) ^ ε) ∧
      ∃ b : ℕ → Fin r → ℕ → 𝓞 K,
        (∀ L i n, n ≤ L → (b L i n : K) = (δ L : K) * PowerSeries.coeff K n (f i)) ∧
        ∀ L i n, n ≤ L → NumberField.house (b L i n : K) ≤ C * (L.factorial : ℝ) ^ ε

private theorem descFactorial_prefix_bound (r L n : ℕ) (i : Fin r) (hn : n ≤ L) :
    (n + i.val).descFactorial i.val ≤ (((r + 1) * 2) ^ r) ^ (L + 1) := by
  have hsum : n + i.val ≤ (r + 1) * (L + 1) := by
    have hi := i.isLt
    nlinarith
  have hL : L + 1 ≤ 2 ^ (L + 1) := Nat.lt_two_pow_self.le
  have hbase : 1 ≤ (r + 1) * 2 ^ (L + 1) :=
    Nat.mul_pos (Nat.succ_pos r) (pow_pos (by decide : 0 < (2 : ℕ)) _)
  have hr : r + 1 ≤ (r + 1) ^ (L + 1) := le_self_pow₀ (Nat.succ_pos r) (by omega)
  calc
    _ ≤ (n + i.val) ^ i.val := Nat.descFactorial_le_pow _ _
    _ ≤ ((r + 1) * 2 ^ (L + 1)) ^ i.val :=
      Nat.pow_le_pow_left (hsum.trans (Nat.mul_le_mul_left _ hL)) _
    _ ≤ ((r + 1) * 2 ^ (L + 1)) ^ r := pow_le_pow_right₀ hbase i.isLt.le
    _ ≤ ((r + 1) ^ (L + 1) * 2 ^ (L + 1)) ^ r :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hr) _
    _ = _ := by rw [← mul_pow, ← pow_mul, Nat.mul_comm (L + 1), pow_mul]

/-- The derivative prefix of the actual ordinary Borel series has integral
prefixes with subfactorial house bounds over its chosen number field. -/
theorem ordinaryBorel_hasSubfactorialIntegralPrefixes
    (F : IntermediateField ℚ AlgebraicComplex) [NumberField F]
    (a : ℕ → AlgebraicComplex) (ha : HasWideEArithmetic a) (hmem : ∀ n, a n ∈ F) (r : ℕ) :
    HasSubfactorialIntegralPrefixes
      (ordinaryDerivativePrefix r (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem))) := by
  intro ε hε
  let η : ℝ := ε / (4 * ((r + 1 : ℕ) : ℝ))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηeq : ((r + 1 : ℕ) : ℝ) * η = ε / 4 := by
    dsimp [η]
    field_simp
    ring
  obtain ⟨C, hC, hconj, d, hd, hbd, hint⟩ := ha η hη
  obtain ⟨B, hB, hstretch⟩ := exists_affine_factorial_rpow_bound (r + 1) η hη.le
  let f := ordinaryDerivativePrefix r (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem))
  let δ (L : ℕ) := d (L + r)
  let M (L : ℕ) : ℝ := (C * B) ^ (L + 1) * (L.factorial : ℝ) ^ (ε / 4)
  let W : ℝ := (((r + 1) * 2 : ℕ) : ℝ) ^ r
  have hCB : 1 ≤ C * B := one_le_mul_of_one_le_of_one_le hC hB
  have hW : 1 ≤ W := by
    apply one_le_pow₀
    exact_mod_cast (Nat.mul_pos (Nat.succ_pos r) (by decide : 0 < (2 : ℕ)))
  have hM (L : ℕ) : 1 ≤ M L := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ hCB) (Real.one_le_rpow (by exact_mod_cast Nat.factorial_pos L) (by positivity))
  have hSize (L m : ℕ) (hm : m ≤ L + r) : C * (m.factorial : ℝ) ^ η ≤ M L := by
    have hidx : m ≤ (r + 1) * (L + 1) := hm.trans (by nlinarith)
    have h := affine_prefix_height_le (r + 1) m L η C B hη.le hC (hstretch L) hB hidx
    rw [hηeq] at h
    exact h
  have hδBound (L : ℕ) : (δ L : ℝ) ≤ M L := (hbd (L + r)).trans (hSize L (L + r) le_rfl)
  have hcoeff (i : Fin r) (n : ℕ) : PowerSeries.coeff F n (f i) =
      ((n + i.val).descFactorial i.val : F) * ordinaryBorelFieldCoefficient F a hmem (n + i.val) := by
    change PowerSeries.coeff F n ((PowerSeries.derivative F)^[i.val]
      (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem))) = _
    rw [stage26_coeff_iterate_derivative, descPochhammer_eval_eq_descFactorial, PowerSeries.coeff_mk]
  have hIntegral (L : ℕ) (i : Fin r) (n : ℕ) (hn : n ≤ L) :
      IsIntegral ℤ ((δ L : F) * PowerSeries.coeff F n (f i)) := by
    have hi : n + i.val ≤ L + r := by have := i.isLt; omega
    have hb := stage44_integral_coefficient_denominator F (ordinaryBorelFieldCoefficient F a hmem)
      (fun _ => rfl) (δ L) (n + i.val) (hint (L + r) (n + i.val) hi)
    rw [hcoeff, mul_left_comm]
    have hw : IsIntegral ℤ ((n + i.val).descFactorial i.val : F) := by
      exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := F)
        (x := ((n + i.val).descFactorial i.val : ℤ)))
    exact hw.mul hb
  let b (L : ℕ) (i : Fin r) (n : ℕ) : 𝓞 F :=
    if hn : n ≤ L then ⟨(δ L : F) * PowerSeries.coeff F n (f i), hIntegral L i n hn⟩ else 0
  have hb (L : ℕ) (i : Fin r) (n : ℕ) (hn : n ≤ L) :
      (b L i n : F) = (δ L : F) * PowerSeries.coeff F n (f i) := by
    simp only [b, dif_pos hn]
    rfl
  let X := (C * B) ^ 2 * W
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hCB) hW
  obtain ⟨D, hD, hAbsorb⟩ := exists_exp_pow_le_factorial_rpow X (ε / 2) hX (by positivity)
  have hFinal (L : ℕ) : M L ^ 2 * W ^ (L + 1) ≤ (X * D) * (L.factorial : ℝ) ^ ε := by
    have hh : ((L.factorial : ℝ) ^ (ε / 4)) ^ 2 = (L.factorial : ℝ) ^ (ε / 2) := by
      rw [← Real.rpow_mul_natCast (by positivity)]
      congr 1
      norm_num
      ring
    calc
      _ = X ^ (L + 1) * (L.factorial : ℝ) ^ (ε / 2) := by
        have hpow : ((C * B) ^ (L + 1)) ^ 2 = ((C * B) ^ 2) ^ (L + 1) := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm (L + 1) 2]
        dsimp only [M, X]
        rw [mul_pow ((C * B) ^ (L + 1)), hh, hpow, mul_pow ((C * B) ^ 2) W]
        ring
      _ ≤ _ := subfactorial_norm_absorb X D ε (zero_le_one.trans hX) L (hAbsorb L)
  refine ⟨X * D, one_le_mul_of_one_le_of_one_le hX hD, δ, (fun L => hd (L + r)), ?_, b, hb, ?_⟩
  · intro L
    exact (hδBound L).trans ((le_self_pow₀ (hM L) (by norm_num)).trans
      ((le_mul_of_one_le_right (by positivity) (one_le_pow₀ hW)).trans (hFinal L)))
  · intro L i n hn
    rw [hb L i n hn, hcoeff]
    apply le_trans _ (hFinal L)
    have hi : n + i.val ≤ L + r := by have := i.isLt; omega
    apply (NumberField.canonicalEmbedding.norm_le_iff _ _).mpr
    intro σ
    let u : F := ordinaryBorelFieldCoefficient F a hmem (n + i.val)
    obtain ⟨τ, hτ⟩ := algebraicComplex_embedding_extends F σ.toRatAlgHom
    have hnorm : ‖σ u‖ ≤ M L := by
      change ‖σ.toRatAlgHom u‖ ≤ M L
      rw [← hτ u]
      exact (hconj τ (n + i.val)).trans (hSize L (n + i.val) hi)
    have hfactor : ((n + i.val).descFactorial i.val : ℝ) ≤ W ^ (L + 1) := by
      dsimp [W]
      exact_mod_cast descFactorial_prefix_bound r L n i hn
    change ‖σ ((δ L : F) * (((n + i.val).descFactorial i.val : F) * u))‖ ≤ _
    rw [map_mul, map_mul, map_natCast, map_natCast, norm_mul, norm_mul,
      Complex.norm_natCast, Complex.norm_natCast]
    calc
      _ ≤ M L * (W ^ (L + 1) * M L) :=
        mul_le_mul (hδBound L)
          (mul_le_mul hfactor hnorm (norm_nonneg _) (pow_nonneg (zero_le_one.trans hW) _))
          (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (zero_le_one.trans (hM L))
      _ = _ := by ring

private theorem typeII_pade_house_factor (r t : ℕ) (κ H : ℝ) (ht : 0 < t) (hH : 1 ≤ H) :
    H * max 1 (κ ^ 2 * ((2 * r * t : ℕ) : ℝ) * H) ≤
      (2 * max 1 (κ ^ 2 * ((2 * r : ℕ) : ℝ))) ^ t * H ^ 2 := by
  let J : ℝ := max 1 (κ ^ 2 * ((2 * r : ℕ) : ℝ))
  have hJ : 1 ≤ J := le_max_left _ _
  have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hmax : max 1 (κ ^ 2 * ((2 * r * t : ℕ) : ℝ) * H) ≤ J * (t : ℝ) * H := by
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hJ htR) hH
    · rw [Nat.cast_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)) (by positivity)
  have hJt : J * (t : ℝ) ≤ (2 * J) ^ t := by
    simpa only [one_pow, mul_one] using typeII_fixed_factor_absorption J 1 hJ zero_le_one t ht
  calc
    _ ≤ H * (J * (t : ℝ) * H) := mul_le_mul_of_nonneg_left hmax (by positivity)
    _ = (J * (t : ℝ)) * H ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hJt (sq_nonneg _)

private theorem typeII_liftMatrixBound_scale (r e N : ℕ) (HT HQ H : ℝ) :
    typeIIIntegralLiftMatrixBound r e N HT (HQ * H ^ 2) H =
      typeIIIntegralLiftMatrixBound r e N HT HQ 1 * H ^ 3 := by
  rw [typeIIIntegralLiftMatrixBound, typeIIIntegralLiftMatrixBound, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem typeII_norm_size_of_house (r e τ t d : ℕ) (HT B H : ℝ)
    (hr : 0 < r) (ht : 0 < t) (hHT : 1 ≤ HT) (hB : 1 ≤ B) (hH : 1 ≤ H) :
    let N := 2 * r * t - 1
    let G := typeIIDeterminantExponentialBase r e τ HT B 1
    ((r.factorial : ℝ) * ((((N + (r - 1) * τ : ℕ) : ℝ) + 1) *
      typeIIIntegralLiftMatrixBound r e N HT (B ^ t * H ^ 2) H) ^ r) ^ d ≤
      G ^ (d * t) * H ^ (3 * r * d) := by
  dsimp only
  let N := 2 * r * t - 1
  let G := typeIIDeterminantExponentialBase r e τ HT B 1
  let S := (((N + (r - 1) * τ : ℕ) : ℝ) + 1) * typeIIIntegralLiftMatrixBound r e N HT (B ^ t) 1
  have hS : 0 ≤ S := by dsimp [S, typeIIIntegralLiftMatrixBound]; positivity
  have hD : (r.factorial : ℝ) * S ^ r ≤ G ^ t := by
    simpa only [S, N, G, one_pow] using
      (typeII_determinant_bound_exponential r e τ t HT B 1 hr ht hHT hB le_rfl).2
  calc
    _ = ((r.factorial : ℝ) * S ^ r * (H ^ 3) ^ r) ^ d := by
      rw [typeII_liftMatrixBound_scale, ← mul_assoc]
      change ((r.factorial : ℝ) * (S * H ^ 3) ^ r) ^ d = _
      rw [mul_pow S, ← mul_assoc]
    _ ≤ (G ^ t * (H ^ 3) ^ r) ^ d := by
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hD (by positivity)) _
    _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_comm t d, ← pow_mul, ← pow_mul, Nat.mul_assoc 3 r d]

/-- The exact integral Padé approximant and its literal full-rank lift give
subfactorial denominators for the divided connection matrices. The cutoff is
linear in the requested prefix, and the determinant house cost is fixed. -/
theorem hasSubfactorialConnectionDenominators_of_integralPrefixes
    {K : Type*} [Field K] [NumberField K] {r : ℕ} (hr : 0 < r)
    (T : Polynomial (𝓞 K)) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (f : Fin r → PowerSeries K)
    (hTne : T.map (algebraMap (𝓞 K) K) ≠ 0)
    (hclear : ∀ i l, algebraMap (Polynomial K) (RatFunc K) (U i l) =
      algebraMap (Polynomial K) (RatFunc K) (T.map (algebraMap (𝓞 K) K)) * A i l)
    (hli : LinearIndependent (RatFunc K) (fun i => HahnSeries.ofPowerSeries ℤ K (f i)))
    (hf : ∀ i, (T.map (algebraMap (𝓞 K) K) : PowerSeries K) * PowerSeries.derivative K (f i) =
      ∑ l, (U i l : PowerSeries K) * f l)
    (hprefix : HasSubfactorialIntegralPrefixes f) :
    HasSubfactorialConnectionDenominators (T.map (algebraMap (𝓞 K) K)) U := by
  classical
  intro ε hε
  have hT0 : typeIIRationalPolynomialMap (algebraMap (𝓞 K) K) T ≠ 0 :=
    RatFunc.algebraMap_ne_zero hTne
  obtain ⟨e, τ, HT, hHT, hTe, hT, hU, hTH⟩ := integral_clearing_finite_bounds T U
  obtain ⟨D, hD⟩ := exists_uniform_polynomial_dual_annihilator A
  obtain ⟨Z, _, hrank⟩ := typeII_rank_of_uniform_polynomial_annihilator hr A f hli D hD
  obtain ⟨κ, hκ⟩ := exists_integral_typeII_pade K
  let B : ℝ := 2 * max 1 (κ ^ 2 * ((2 * r : ℕ) : ℝ))
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le (by norm_num) (le_max_left _ _)
  let G := typeIIDeterminantExponentialBase r e τ HT B 1
  have hG : 1 ≤ G := (typeII_determinant_bound_exponential r e τ 1 HT B 1 hr
    (by decide) hHT hB le_rfl).1
  let d := Module.finrank ℚ K
  let kCut := r * (τ + 1) + Z + 1
  let LCut := (2 * r + 1) * kCut
  let p := 3 * r * d
  have hCut : 0 < LCut := Nat.mul_pos (by positivity) (by dsimp [kCut]; positivity)
  have hp : 0 < p := Nat.mul_pos (Nat.mul_pos (by decide) hr) Module.finrank_pos
  let η : ℝ := ε / (2 * ((LCut * p : ℕ) : ℝ))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηeq : (LCut : ℝ) * η * (p : ℝ) = ε / 2 := by
    have hne : ((LCut * p : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos hCut hp))
    dsimp only [η]
    field_simp [hne]
    ring
  obtain ⟨C, hC, δ, hδ, hδBound, b, hb, hbH⟩ := hprefix η hη
  obtain ⟨B₀, hB₀, hStretch⟩ := exists_affine_factorial_rpow_bound LCut η hη.le
  let E := G ^ (d * kCut) * (C * B₀) ^ p
  have hE : 1 ≤ E := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hG)
    (one_le_pow₀ (one_le_mul_of_one_le_of_one_le hC hB₀))
  obtain ⟨E₀, hE₀, hAbsorb⟩ := exists_exp_pow_le_factorial_rpow E (ε / 2) hE (by positivity)
  refine ⟨E * E₀, one_le_mul_of_one_le_of_one_le hE hE₀, fun s => ?_⟩
  let t := kCut * (s + 1)
  let N := 2 * r * t - 1
  let L := N + t
  let H := C * (L.factorial : ℝ) ^ η
  have hparam := typeII_affine_cutoff r τ Z s hr
  change 0 < t ∧ Z < t ∧ (s + r - 1) * (τ + 1) ≤ t at hparam
  have hdim : N + 1 = 2 * r * t := Nat.sub_add_cancel
    (Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (by decide) hr) hparam.1))
  have hL : L + 1 = (2 * r + 1) * t := by
    calc
      _ = (N + 1) + t := by dsimp [L]; omega
      _ = _ := by rw [hdim]; ring
  have hLcut : L ≤ LCut * (s + 1) := by
    have heq : (2 * r + 1) * t = LCut * (s + 1) := by simp only [t, LCut, mul_assoc]
    exact (Nat.le_succ _).trans_eq (hL.trans heq)
  have hSize : r * t < N + 1 := by rw [hdim]; nlinarith [Nat.mul_pos hr hparam.1]
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le hC
    (Real.one_le_rpow (by exact_mod_cast Nat.factorial_pos L) hη.le)
  obtain ⟨Q, P₀, hQ, hQN, hP₀N, _, hContact₀, hQHouse₀, _⟩ :=
    hκ r N t (δ L) f (b L) H H (hδ L) hSize (zero_le_one.trans hH) (hδBound L) (hb L) (hbH L)
  let φ : 𝓞 K →+* K := algebraMap (𝓞 K) K
  let P : Fin r → Polynomial K := fun i => (P₀ i).map φ
  have hQK : Q.map φ ≠ 0 := (Polynomial.map_ne_zero_iff NumberField.RingOfIntegers.coe_injective).mpr hQ
  have hPKN (i : Fin r) : (P i).natDegree ≤ N := Polynomial.natDegree_map_le.trans (hP₀N i)
  have hQKN : (Q.map φ).natDegree ≤ N := Polynomial.natDegree_map_le.trans hQN
  have hContact (i : Fin r) : seriesContact (N + t + 1)
      ((Q.map φ : PowerSeries K) * f i - (P i : PowerSeries K)) := hContact₀ i
  have hQHouse (j : ℕ) : NumberField.house (Q.coeff j : K) ≤ B ^ t * H ^ 2 := by
    have hκbound := typeII_balanced_kernel_bound κ H r t hr hparam.1
    have hQ₀ := hQHouse₀ j
    simp only [N, Nat.cast_add, Nat.cast_one] at hQ₀
    simp only [Nat.cast_add, Nat.cast_one] at hκbound
    rw [hκbound] at hQ₀
    exact hQ₀.trans (typeII_pade_house_factor r t κ H hparam.1 hH)
  have hRaw := hrank N t (Nat.le_of_lt hparam.2.1) (Q.map φ) hQK hQKN P hContact
  have hCutRank : (r - 1) * (τ + 1) ≤ t :=
    (Nat.mul_le_mul_right (τ + 1) (show r - 1 ≤ s + r - 1 by omega)).trans hparam.2.2
  obtain ⟨_, j, hj⟩ := typeII_literal_lift_det_and_coefficient_ne_zero T Q U P A f
    (b L) (δ L) (hδ L) N t τ hT0 hT hU hPKN hclear hf hContact (hb L) hCutRank hRaw
  let q := Int.natAbs (Algebra.norm ℤ ((typeIIIntegralLiftMatrix r N τ T Q (b L)).det.coeff j))
  obtain ⟨hq, hqSize, hqInt⟩ := typeII_same_matrix_positive_denominator T Q U P A f
    (b L) (δ L : K) N t τ s hT0 hT hU hPKN hclear hf hContact (hb L) hparam.2.2
    e hTe hQN HT (B ^ t * H ^ 2) H (by positivity) (by positivity) (by positivity)
    hTH hQHouse (hbH L) j hj
  refine ⟨q, hq, ?_, hqInt⟩
  have hqNorm : (q : ℝ) ≤ G ^ (d * t) * H ^ p :=
    hqSize.trans (typeII_norm_size_of_house r e τ t d HT B H hr hparam.1 hHT hB hH)
  have hHbound : H ≤ (C * B₀) ^ (s + 1) * (s.factorial : ℝ) ^ ((LCut : ℝ) * η) :=
    affine_prefix_height_le LCut L s η C B₀ hη.le hC (hStretch s) hB₀ hLcut
  have hPower : H ^ p ≤ ((C * B₀) ^ p) ^ (s + 1) * (s.factorial : ℝ) ^ (ε / 2) := by
    apply (pow_le_pow_left₀ (by positivity) hHbound _).trans
    rw [mul_pow, ← Real.rpow_mul_natCast (by positivity), hηeq,
      ← pow_mul, ← pow_mul, Nat.mul_comm (s + 1) p]
  calc
    _ ≤ G ^ (d * t) * H ^ p := hqNorm
    _ ≤ G ^ (d * t) * (((C * B₀) ^ p) ^ (s + 1) * (s.factorial : ℝ) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_left hPower (by positivity)
    _ = E ^ (s + 1) * (s.factorial : ℝ) ^ (ε / 2) := by
      dsimp only [E, t]
      rw [mul_pow (G ^ (d * kCut)), ← pow_mul G (d * kCut), Nat.mul_assoc d kCut, mul_assoc]
    _ ≤ _ := subfactorial_norm_absorb E E₀ ε (by positivity) s (hAbsorb s)

end WideE
