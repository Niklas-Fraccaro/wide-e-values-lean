import WideE.FiniteCoverMonodromy
import Stage16LaurentMatrixClearing
import MonicRootPolynomialEnvelope
import EntirePolynomialGrowth
import Mathlib.RingTheory.Localization.Integral

/-! Holomorphic functions integral over the Laurent coordinate ring are Laurent polynomials. -/

open scoped Topology
open Filter Set Polynomial LaurentPolynomial

noncomputable section

namespace WideE

/-- Pointwise evaluation of Laurent polynomials on the complex punctured line. -/
def complexLaurentFunctions : LaurentPolynomial ℂ →+* (ComplexPuncturedLine → ℂ) where
  toFun a z := StrictEUnit.stage16_laurentEval (Units.mk0 (z : ℂ) z.property) a
  map_one' := funext fun _ => map_one _
  map_zero' := funext fun _ => map_zero _
  map_mul' a b := funext fun _ => map_mul _ a b
  map_add' a b := funext fun _ => map_add _ a b

@[simp] theorem complexLaurentFunctions_toLaurent (P : Polynomial ℂ) (z : ComplexPuncturedLine) :
    complexLaurentFunctions P.toLaurent z = P.eval (z : ℂ) :=
  StrictEUnit.stage16_laurentEval_toLaurent _ P

@[simp] theorem complexLaurentFunctions_T_nat (n : ℕ) (z : ComplexPuncturedLine) :
    complexLaurentFunctions (T (n : ℤ)) z = (z : ℂ) ^ n :=
  StrictEUnit.stage16_laurentEval_T_nat _ n

theorem complexLaurentFunctions_injective : Function.Injective complexLaurentFunctions := by
  apply (injective_iff_map_eq_zero' complexLaurentFunctions).mpr
  intro a
  refine ⟨fun ha => ?_, fun ha => ha ▸ map_zero _⟩
  obtain ⟨n, P, hP⟩ := LaurentPolynomial.exists_T_pow a
  have hroot : ({0}ᶜ : Set ℂ) ⊆ {z | P.IsRoot z} := by
    intro z hz
    let w : ComplexPuncturedLine := ⟨z, hz⟩
    change P.eval z = 0
    have h := congrFun (congrArg complexLaurentFunctions hP) w
    rw [complexLaurentFunctions_toLaurent, map_mul, Pi.mul_apply, ha, Pi.zero_apply, zero_mul] at h
    exact h
  have hP₀ := P.eq_zero_of_infinite_isRoot ((Set.finite_singleton (0 : ℂ)).infinite_compl.mono hroot)
  have h := congrArg (fun b => b * T (-(n : ℤ))) hP
  simpa only [hP₀, map_zero, zero_mul, mul_T_assoc, add_neg_cancel, T_zero, mul_one] using h.symm

private theorem exists_polynomial_of_holomorphic_monic {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f ({0}ᶜ : Set ℂ))
    {p : Polynomial (Polynomial ℂ)} (hp : p.Monic)
    (hroot : ∀ z : ℂ, z ≠ 0 → (p.map (Polynomial.evalRingHom z)).eval (f z) = 0) :
    ∃ P : Polynomial ℂ, ∀ z, z ≠ 0 → P.eval z = f z := by
  let v := StrictEUnit.monicRootEnvelope p
  have hbound (z : ℂ) (hz : z ≠ 0) : ‖f z‖ ≤ v z :=
    StrictEUnit.norm_le_monicRootEnvelope hp (hroot z hz)
  let s := {z | v z < v 0 + 1}
  have hs : s ∈ 𝓝 (0 : ℂ) :=
    (StrictEUnit.continuous_monicRootEnvelope p).continuousAt.eventually_lt
      continuousAt_const (lt_add_one _)
  have hb : BddAbove (norm ∘ f '' (s \ {0})) := by
    refine ⟨v 0 + 1, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (hbound z hz.2).trans hz.1.le
  let F := Function.update f 0 (limUnder (𝓝[≠] 0) f)
  have hF₀ : DifferentiableAt ℂ F 0 :=
    (Complex.differentiableOn_update_limUnder_of_bddAbove hs
      (hf.mono fun _ hz => hz.2) hb).differentiableAt hs
  have hF : Differentiable ℂ F := by
    intro z
    by_cases hz : z = 0
    · simpa only [hz] using hF₀
    · have hnear : ∀ᶠ w in 𝓝 z, w ≠ (0 : ℂ) := isClosed_singleton.isOpen_compl.mem_nhds hz
      apply (hf.differentiableAt hnear).congr_of_eventuallyEq
      filter_upwards [hnear] with w hw
      exact Function.update_of_ne hw _ _
  obtain ⟨C, N, _, hN⟩ := StrictEUnit.monicRootEnvelope_polynomial_growth p
  obtain ⟨P, hP, _⟩ := StrictEUnit.entire_polynomial_of_modulus_growth hF C 0 N (by
    intro z hz
    have hz₀ : z ≠ 0 := fun h => (not_le_of_gt (zero_lt_one : (0 : ℝ) < 1)) (by simpa [h] using hz)
    simpa only [F, Function.update_of_ne hz₀, zero_mul, add_zero]
      using (hbound z hz₀).trans (hN z hz))
  exact ⟨P, fun z hz => (hP z).trans (Function.update_of_ne hz _ _)⟩

/-- Clearing Laurent denominators preserves monicity after scaling the root.
Removability at zero and polynomial growth then identify the actual function. -/
theorem exists_laurent_of_holomorphic_integral {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f ({0}ᶜ : Set ℂ))
    (hint : @IsIntegral (LaurentPolynomial ℂ) (ComplexPuncturedLine → ℂ) _ _
      complexLaurentFunctions.toAlgebra (fun z => f z)) :
    ∃ a : LaurentPolynomial ℂ, ∀ z : ComplexPuncturedLine, complexLaurentFunctions a z = f z := by
  letI : Algebra (LaurentPolynomial ℂ) (ComplexPuncturedLine → ℂ) := complexLaurentFunctions.toAlgebra
  letI : Algebra (Polynomial ℂ) (ComplexPuncturedLine → ℂ) :=
    (complexLaurentFunctions.comp (algebraMap (Polynomial ℂ) (LaurentPolynomial ℂ))).toAlgebra
  letI : IsScalarTower (Polynomial ℂ) (LaurentPolynomial ℂ) (ComplexPuncturedLine → ℂ) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨⟨m, ⟨n, rfl⟩⟩, p, hp, heval⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (Rₘ := LaurentPolynomial ℂ) (Submonoid.powers (Polynomial.X : Polynomial ℂ))
    (fun z : ComplexPuncturedLine => f z) hint
  let g (z : ℂ) := z ^ n * f z
  have hg : DifferentiableOn ℂ g ({0}ᶜ : Set ℂ) := (differentiableOn_id.pow n).mul hf
  have hroot (z : ℂ) (hz : z ≠ 0) : (p.map (Polynomial.evalRingHom z)).eval (g z) = 0 := by
    let w : ComplexPuncturedLine := ⟨z, hz⟩
    apply_fun Pi.evalRingHom (fun _ : ComplexPuncturedLine => ℂ) w at heval
    rw [Polynomial.hom_eval₂, map_zero] at heval
    have hcomp : (Pi.evalRingHom (fun _ : ComplexPuncturedLine => ℂ) w).comp
        (algebraMap (Polynomial ℂ) (ComplexPuncturedLine → ℂ)) = Polynomial.evalRingHom z := by
      apply RingHom.ext
      intro P
      exact complexLaurentFunctions_toLaurent P w
    have hvalue : Pi.evalRingHom (fun _ : ComplexPuncturedLine => ℂ) w
        ((⟨(Polynomial.X : Polynomial ℂ) ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers Polynomial.X) •
          (fun x : ComplexPuncturedLine => f x)) = g z := by
      rw [Submonoid.smul_def, Algebra.smul_def, map_mul]
      change complexLaurentFunctions (Polynomial.toLaurent (Polynomial.X ^ n)) w * f z = _
      rw [complexLaurentFunctions_toLaurent, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hcomp, hvalue] at heval
    simpa only [Polynomial.eval_map] using heval
  obtain ⟨P, hP⟩ := exists_polynomial_of_holomorphic_monic hg hp hroot
  refine ⟨P.toLaurent * T (-(n : ℤ)), fun z => ?_⟩
  rw [map_mul, Pi.mul_apply, complexLaurentFunctions_toLaurent, hP z z.property]
  have hcancel : complexLaurentFunctions (T (-(n : ℤ))) z * (z : ℂ) ^ n = 1 := by
    rw [← complexLaurentFunctions_T_nat n z, ← Pi.mul_apply, ← map_mul, ← T_add,
      neg_add_cancel, T_zero, map_one, Pi.one_apply]
  change ((z : ℂ) ^ n * f z) * complexLaurentFunctions (T (-(n : ℤ))) z = f z
  calc
    _ = (complexLaurentFunctions (T (-(n : ℤ))) z * (z : ℂ) ^ n) * f z := by ring
    _ = _ := by rw [hcancel, one_mul]

end WideE
