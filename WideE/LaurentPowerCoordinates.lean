import WideE.LaurentEtaleChart
import WideE.SimpleRootChart

/-! Analyticity of the power coordinates on the determinant open. -/

open scoped Topology
open Filter

noncomputable section

namespace WideE

variable {A : Type} [CommRing A] [Algebra (LaurentPolynomial ℂ) A] {n : ℕ}
  (b : Basis (Fin n) (LaurentPolynomial ℂ) A) (a s : A) (i : Fin n)

/-- The specialized power coordinate on the punctured line, extended by zero at the origin. -/
def complexEvaluationPowerCoordinates (z : ℂ) : ℂ :=
  if hz : z ≠ 0 then evaluationPowerCoordinates b a (laurentEvalAlg (Units.mk0 z hz)) s i else 0

@[simp] theorem complexEvaluationPowerCoordinates_of_ne {z : ℂ} (hz : z ≠ 0) :
    complexEvaluationPowerCoordinates b a s i z =
      evaluationPowerCoordinates b a (laurentEvalAlg (Units.mk0 z hz)) s i :=
  dif_pos hz

/-- The adjugate formula specializes to a quotient of evaluations of Laurent polynomials. -/
theorem complexEvaluationPowerCoordinates_eq_div {z : ℂ} (hz : z ≠ 0)
    (hD : laurentEvalAlg (Units.mk0 z hz) (powerCoordinateDet b a) ≠ 0) :
    complexEvaluationPowerCoordinates b a s i z =
      complexLaurentEvaluation z (powerCoordinateNumerator b a s i) /
        complexLaurentEvaluation z (powerCoordinateDet b a) := by
  rw [complexEvaluationPowerCoordinates_of_ne b a s i hz, complexLaurentEvaluation_of_ne hz]
  exact evaluationPowerCoordinates_eq_div b a (laurentEvalAlg (Units.mk0 z hz)) hD s i

/-- Each specialized power coordinate is holomorphic wherever the basis determinant is nonzero. -/
theorem complexEvaluationPowerCoordinates_analyticAt {z : ℂ} (hz : z ≠ 0)
    (hD : laurentEvalAlg (Units.mk0 z hz) (powerCoordinateDet b a) ≠ 0) :
    AnalyticAt ℂ (complexEvaluationPowerCoordinates b a s i) z := by
  have hNum := complexLaurentEvaluation_analyticAt (powerCoordinateNumerator b a s i) hz
  have hDen := complexLaurentEvaluation_analyticAt (powerCoordinateDet b a) hz
  have hDen₀ : complexLaurentEvaluation z (powerCoordinateDet b a) ≠ 0 := by
    rw [complexLaurentEvaluation_of_ne hz]
    exact hD
  apply (hNum.fun_div hDen hDen₀).congr
  have hnear : ∀ᶠ w in 𝓝 z, w ≠ (0 : ℂ) := isClosed_singleton.isOpen_compl.mem_nhds hz
  have hDenNear : ∀ᶠ w in 𝓝 z, complexLaurentEvaluation w (powerCoordinateDet b a) ≠ 0 :=
    hDen.continuousAt.eventually_ne hDen₀
  filter_upwards [hnear, hDenNear] with w hw hDw
  rw [complexLaurentEvaluation_of_ne hw] at hDw
  exact (complexEvaluationPowerCoordinates_eq_div b a s i hw hDw).symm

end WideE
