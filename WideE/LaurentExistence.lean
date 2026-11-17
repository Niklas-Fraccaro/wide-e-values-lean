import WideE.ConnectionArithmetic
import WideE.MinimalNonvanishing
import OrdinaryBorelMinimalCyclic

/-! Laurent operators and ordinary division for actual wide E-functions. -/

noncomputable section

namespace WideE

open StrictEUnit
open scoped BigOperators NumberField Matrix

/-- A nonzero wide E-function has an actual monic Laurent differential
operator. The ordinary Borel equation and all divided connection
denominators are constructed from its own coefficients. -/
theorem wideLaurentOperatorExistence : WideLaurentOperatorExistence := by
  intro f hf hfne
  classical
  have hData := hf
  obtain ⟨a, hd, hs, hODE, ha, _⟩ := hData
  have hne : ∃ n, a n ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hfne
    funext z
    have hz : HasSum (fun _ : ℕ => (0 : ℂ)) (f z) := by simpa [hn] using hs z
    exact hz.unique hasSum_zero
  obtain ⟨m, p, hp, hFormal⟩ := formal_polynomial_ode hd hs hODE
  rw [taylorRealization_factorialSeries hd hs] at hFormal
  obtain ⟨u, Q, hQ, hRec⟩ := factorialSeries_ode_original_coefficients_recurrence a m p hp hFormal
  obtain ⟨v, q, hq, hOrd⟩ := polynomial_recurrence_ordinary_series_ode a u Q hQ hRec
  obtain ⟨F, hF, haF, hqF⟩ := stage26_formal_ode_finite_coefficient_field v q (PowerSeries.mk a) hq hOrd
  letI : FiniteDimensional ℚ F := hF
  letI : NumberField F := ⟨⟩
  have hmem (n : ℕ) : a n ∈ F := by simpa only [PowerSeries.coeff_mk] using haF n
  obtain ⟨qF, _, hqFn, hqFO⟩ := ordinaryBorel_equation_descends F a hmem v q hqF hq hOrd
  let aF := ordinaryBorelFieldCoefficient F a hmem
  let G := PowerSeries.mk aF
  have haFne : ∃ n, aF n ≠ 0 := by
    obtain ⟨n, hn⟩ := hne
    exact ⟨n, fun hz => hn (congrArg (fun x : F => (x : AlgebraicComplex)) hz)⟩
  obtain ⟨r, hr, c, hCyclic⟩ := ordinaryBorel_exists_minimal_cyclic (HahnSeries.ofPowerSeries ℤ F G)
    (ordinaryBorel_laurent_mk_ne_zero aF haFne)
    (ordinaryBorel_laurent_scalar_relation G v qF hqFn hqFO)
  cases r with
  | zero => omega
  | succ n =>
    let A := minimalDerivativeCompanion (n + 1) c
    obtain ⟨_, _, _, _, _, _, T, UI, _, _, _, hT, hclear⟩ :=
      exists_integral_polynomial_matrix_clearing F (n + 1) A
    let U : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial F) :=
      Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 F) F))
    obtain ⟨hli, hSystem⟩ := minimal_companion_powerSeries_clearing G (n + 1) c hCyclic
      (T.map (algebraMap (𝓞 F) F)) U hclear
    have hPrefix := ordinaryBorel_hasSubfactorialIntegralPrefixes F a ha hmem (n + 1)
    have hden := hasSubfactorialConnectionDenominators_of_integralPrefixes hr T U A
      (ordinaryDerivativePrefix (n + 1) G) hT hclear hli hSystem hPrefix
    exact hasLaurentOperator_of_subfactorial_borel_connection hf hs F hmem n c hCyclic
      (T.map (algebraMap (𝓞 F) F)) U hT hclear hden

/-- Exact linear relations of wide functions at the ordinary point one lift
to polynomial relations on the whole plane. -/
theorem wideLinearOrdinaryLiftingAtOne : WideLinearOrdinaryLiftingAtOne :=
  wideLinearOrdinaryLiftingAtOne_of_laurentOperatorExistence wideLaurentOperatorExistence

/-- Division by (z - 1) is closed in the wide class at a vanishing value. -/
theorem wideEFunction_divAtOne {f : ℂ → ℂ} (hf : IsWideEFunction f) (hz : f 1 = 0) :
    ∃ g : ℂ → ℂ, IsWideEFunction g ∧ ∀ z : ℂ, (z - 1) * g z = f z :=
  wideEFunction_divAtOne_of_laurentOperatorExistence wideLaurentOperatorExistence hf hz

/-- Division at a nonzero algebraic zero, by rescaling the actual functions. -/
theorem wideEFunction_divAtAlgebraic {f : ℂ → ℂ} (hf : IsWideEFunction f)
    (a : AlgebraicComplex) (ha : a ≠ 0) (hz : f a = 0) :
    ∃ g : ℂ → ℂ, IsWideEFunction g ∧ ∀ z : ℂ, (z - (a : ℂ)) * g z = f z := by
  have haC : (a : ℂ) ≠ 0 := fun h => ha (Subtype.ext h)
  obtain ⟨g, hg, h⟩ := wideEFunction_divAtOne (hf.rescale a) (by simpa using hz)
  refine ⟨fun z => (a : ℂ)⁻¹ * g ((a : ℂ)⁻¹ * z), (hg.rescale a⁻¹).const_mul a⁻¹, ?_⟩
  intro z
  have hz' := h ((a : ℂ)⁻¹ * z)
  rw [← mul_assoc, mul_inv_cancel₀ haC, one_mul] at hz'
  rw [← mul_assoc, sub_mul, mul_inv_cancel₀ haC, mul_comm z]
  exact hz'

end WideE
