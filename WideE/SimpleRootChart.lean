import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Analytic.Polynomial
import Stage16LaurentMatrixClearing

/-! A local graph and uniqueness of the root germ at a simple root. -/

open scoped Topology
open Filter Set

noncomputable section

namespace WideE

section Implicit

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The triangular derivative of the map `(z, y) ↦ (z, F (z, y))` is invertible
when its vertical entry is nonzero. -/
private def simpleRootDerivativeEquiv (D : (𝕜 × 𝕜) →L[𝕜] 𝕜) (h : D (0, 1) ≠ 0) :
    (𝕜 × 𝕜) ≃L[𝕜] (𝕜 × 𝕜) :=
  (ContinuousLinearEquiv.refl 𝕜 𝕜).skewProd
    (ContinuousLinearEquiv.unitsEquivAut 𝕜 (Units.mk0 (D (0, 1)) h))
    (D.comp (ContinuousLinearMap.inl 𝕜 𝕜 𝕜))

private theorem simpleRootDerivativeEquiv_coe (D : (𝕜 × 𝕜) →L[𝕜] 𝕜) (h : D (0, 1) ≠ 0) :
    (simpleRootDerivativeEquiv D h : (𝕜 × 𝕜) →L[𝕜] (𝕜 × 𝕜)) =
      (ContinuousLinearMap.fst 𝕜 𝕜 𝕜).prod D := by
  apply ContinuousLinearMap.ext
  rintro ⟨x, y⟩
  refine Prod.ext rfl ?_
  change y * D (0, 1) + D (x, 0) = D (x, y)
  calc
    y * D (0, 1) + D (x, 0) = D (y • ((0, 1) : 𝕜 × 𝕜)) + D (x, 0) := by
      rw [map_smul, smul_eq_mul]
    _ = D ((y • ((0, 1) : 𝕜 × 𝕜)) + (x, 0)) := (map_add D _ _).symm
    _ = D (x, y) := by simp [Prod.smul_mk]

variable [CompleteSpace 𝕜]

/-- Near a simple root, the zero set is the graph of a continuous function
that is differentiable at the given base point. The graph and uniqueness
hold in a product of open neighborhoods. -/
theorem exists_local_simple_root {F : 𝕜 × 𝕜 → 𝕜} {D : (𝕜 × 𝕜) →L[𝕜] 𝕜} {z₀ y₀ : 𝕜}
    (hF : HasStrictFDerivAt F D (z₀, y₀)) (hroot : F (z₀, y₀) = 0) (hsimple : D (0, 1) ≠ 0) :
    ∃ (s : 𝕜 → 𝕜) (U V : Set 𝕜), IsOpen U ∧ z₀ ∈ U ∧ IsOpen V ∧ y₀ ∈ V ∧
      s z₀ = y₀ ∧ DifferentiableAt 𝕜 s z₀ ∧ ContinuousOn s U ∧ MapsTo s U V ∧
      ∀ z ∈ U, ∀ y ∈ V, F (z, y) = 0 ↔ y = s z := by
  let G : 𝕜 × 𝕜 → 𝕜 × 𝕜 := fun p => (p.1, F p)
  let E := simpleRootDerivativeEquiv D hsimple
  have hG : HasStrictFDerivAt G (E : (𝕜 × 𝕜) →L[𝕜] (𝕜 × 𝕜)) (z₀, y₀) := by
    rw [simpleRootDerivativeEquiv_coe]
    exact hasStrictFDerivAt_fst.prodMk hF
  let e := hG.toPartialHomeomorph G
  let i := ContinuousLinearMap.inl 𝕜 𝕜 𝕜
  let s : 𝕜 → 𝕜 := fun z => (e.symm (i z)).2
  have hi : G (z₀, y₀) = i z₀ := by
    change (z₀, F (z₀, y₀)) = (z₀, 0)
    rw [hroot]
  have hsource : (z₀, y₀) ∈ e.source := hG.mem_toPartialHomeomorph_source
  have htarget : i z₀ ∈ e.target := hi ▸ hG.image_mem_toPartialHomeomorph_target
  have hs₀ : s z₀ = y₀ := by
    have h := e.left_inv hsource
    change e.symm (G (z₀, y₀)) = (z₀, y₀) at h
    rw [hi] at h
    exact congrArg Prod.snd h
  have hs : DifferentiableAt 𝕜 s z₀ := by
    have hInv : DifferentiableAt 𝕜 e.symm (i z₀) :=
      hi ▸ hG.to_localInverse.hasFDerivAt.differentiableAt
    exact (hInv.comp z₀ i.differentiableAt).snd
  obtain ⟨U₀, V, hU₀, hz₀, hV, hy₀, hrect⟩ := mem_nhds_prod_iff'.mp
    (e.open_source.mem_nhds hsource)
  have hnearTarget : i ⁻¹' e.target ∈ 𝓝 z₀ :=
    (e.open_target.preimage i.continuous).mem_nhds htarget
  have hnearValue : s ⁻¹' V ∈ 𝓝 z₀ := by
    apply hs.continuousAt
    rw [hs₀]
    exact hV.mem_nhds hy₀
  obtain ⟨U, hUsub, hU, hz⟩ := mem_nhds_iff.mp
    (inter_mem (hU₀.mem_nhds hz₀) (inter_mem hnearTarget hnearValue))
  have hMap : MapsTo i U e.target := fun _ hz' => (hUsub hz').2.1
  have hsCont : ContinuousOn s U :=
    continuous_snd.comp_continuousOn (e.continuousOn_symm.comp i.continuous.continuousOn hMap)
  refine ⟨s, U, V, hU, hz, hV, hy₀, hs₀, hs, hsCont, fun _ hz' => (hUsub hz').2.2, ?_⟩
  intro z hz' y hy
  constructor
  · intro hzero
    have h := e.left_inv (hrect (show (z, y) ∈ U₀ ×ˢ V from ⟨(hUsub hz').1, hy⟩))
    change e.symm (z, F (z, y)) = (z, y) at h
    rw [hzero] at h
    exact (congrArg Prod.snd h).symm
  · rintro rfl
    have h := e.right_inv (hMap hz')
    change G (e.symm (i z)) = i z at h
    have hfst : (e.symm (i z)).1 = z := congrArg (fun p : 𝕜 × 𝕜 => p.1) h
    have he : e.symm (i z) = (z, s z) := Prod.ext hfst rfl
    rw [he] at h
    exact congrArg (fun p : 𝕜 × 𝕜 => p.2) h

/-- Every continuous root germ at the same simple root agrees with the local branch. -/
theorem exists_unique_simple_root_germ {F : 𝕜 × 𝕜 → 𝕜} {D : (𝕜 × 𝕜) →L[𝕜] 𝕜} {z₀ y₀ : 𝕜}
    (hF : HasStrictFDerivAt F D (z₀, y₀)) (hroot : F (z₀, y₀) = 0) (hsimple : D (0, 1) ≠ 0) :
    ∃ s : 𝕜 → 𝕜, s z₀ = y₀ ∧ DifferentiableAt 𝕜 s z₀ ∧
      (∀ᶠ z in 𝓝 z₀, F (z, s z) = 0) ∧
      ∀ t : 𝕜 → 𝕜, ContinuousAt t z₀ → t z₀ = y₀ →
        (∀ᶠ z in 𝓝 z₀, F (z, t z) = 0) → t =ᶠ[𝓝 z₀] s := by
  obtain ⟨s, U, V, hU, hz, hV, hy, hs₀, hs, _, hsV, hgraph⟩ := exists_local_simple_root hF hroot hsimple
  refine ⟨s, hs₀, hs, ?_, ?_⟩
  · filter_upwards [hU.mem_nhds hz] with z hz'
    exact (hgraph z hz' (s z) (hsV hz')).2 rfl
  · intro t ht ht₀ htroot
    have htV : t ⁻¹' V ∈ 𝓝 z₀ := by
      apply ht
      rw [ht₀]
      exact hV.mem_nhds hy
    filter_upwards [hU.mem_nhds hz, htV, htroot] with z hz' hzV hzero
    exact (hgraph z hz' (t z) hzV).1 hzero

end Implicit

section Laurent

/-- Evaluation on the punctured line, extended at zero by evaluation at one
so the ambient function has a total domain. -/
def complexLaurentEvaluation (z : ℂ) : LaurentPolynomial ℂ →+* ℂ :=
  if hz : z ≠ 0 then StrictEUnit.stage16_laurentEval (Units.mk0 z hz)
  else StrictEUnit.stage16_laurentEval 1

@[simp] theorem complexLaurentEvaluation_of_ne {z : ℂ} (hz : z ≠ 0) :
    complexLaurentEvaluation z = StrictEUnit.stage16_laurentEval (Units.mk0 z hz) :=
  dif_pos hz

/-- Evaluation of a polynomial whose coefficients are Laurent polynomials in
the base coordinate. -/
def laurentRootValue (p : Polynomial (LaurentPolynomial ℂ)) (w : ℂ × ℂ) : ℂ :=
  (p.map (complexLaurentEvaluation w.1)).eval w.2

@[simp] theorem laurentRootValue_of_ne (p : Polynomial (LaurentPolynomial ℂ))
    {z : ℂ} (hz : z ≠ 0) (y : ℂ) :
    laurentRootValue p (z, y) = (p.map (StrictEUnit.stage16_laurentEval (Units.mk0 z hz))).eval y := by
  rw [laurentRootValue, complexLaurentEvaluation_of_ne hz]

/-- Laurent coefficients are analytic at every nonzero complex point. -/
theorem complexLaurentEvaluation_analyticAt (a : LaurentPolynomial ℂ) {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ (fun w : ℂ => complexLaurentEvaluation w a) z := by
  obtain ⟨n, P, ha⟩ := LaurentPolynomial.exists_T_pow a
  have hP : AnalyticAt ℂ (fun w : ℂ => P.eval w) z :=
    AnalyticOnNhd.eval_polynomial P z (mem_univ z)
  have hn : AnalyticAt ℂ (fun w : ℂ => (w ^ n)⁻¹) z :=
    ((analyticAt_id (𝕜 := ℂ) (z := z)).fun_pow n).fun_inv (pow_ne_zero n hz)
  apply (hP.mul hn).congr
  have hnear : ∀ᶠ w in 𝓝 z, w ≠ (0 : ℂ) := isClosed_singleton.isOpen_compl.mem_nhds hz
  filter_upwards [hnear] with w hw
  change P.eval w * (w ^ n)⁻¹ = complexLaurentEvaluation w a
  have hclear := StrictEUnit.stage16_laurent_clearing_eval a P n ha (Units.mk0 w hw)
  simp only [Units.val_mk0] at hclear
  rw [complexLaurentEvaluation_of_ne hw, hclear, mul_comm (w ^ n), mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero n hw), mul_one]

/-- The bivariate equation associated with Laurent coefficients is analytic
where the base coordinate is nonzero. -/
theorem laurentRootValue_analyticAt (p : Polynomial (LaurentPolynomial ℂ))
    {z y : ℂ} (hz : z ≠ 0) : AnalyticAt ℂ (laurentRootValue p) (z, y) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have h : laurentRootValue (p + q) = fun w => laurentRootValue p w + laurentRootValue q w := by
      funext w
      simp only [laurentRootValue, Polynomial.map_add, Polynomial.eval_add]
    rw [h]
    exact hp.add hq
  | monomial n a =>
    have ha : AnalyticAt ℂ (fun w : ℂ × ℂ => complexLaurentEvaluation w.1 a) (z, y) :=
      (complexLaurentEvaluation_analyticAt a hz).comp_of_eq'
        ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (z, y)) rfl
    have hy : AnalyticAt ℂ (fun w : ℂ × ℂ => w.2 ^ n) (z, y) :=
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (z, y)).fun_pow n
    have h : laurentRootValue (Polynomial.monomial n a) =
        fun w => complexLaurentEvaluation w.1 a * w.2 ^ n := by
      funext w
      simp only [laurentRootValue, Polynomial.map_monomial, Polynomial.eval_monomial]
    rw [h]
    exact ha.mul hy

/-- The vertical component of the Fréchet derivative is the derivative of the
specialized polynomial. -/
theorem laurentRootValue_verticalDerivative (p : Polynomial (LaurentPolynomial ℂ))
    {D : (ℂ × ℂ) →L[ℂ] ℂ} {z y : ℂ} (hD : HasFDerivAt (laurentRootValue p) D (z, y)) :
    D (0, 1) = ((p.map (complexLaurentEvaluation z)).derivative).eval y := by
  have hv : HasFDerivAt (fun t : ℂ => (z, t)) (ContinuousLinearMap.inr ℂ ℂ ℂ) y :=
    (hasFDerivAt_const (𝕜 := ℂ) z y).prodMk (hasFDerivAt_id y)
  have hd : HasDerivAt (fun t : ℂ => (p.map (complexLaurentEvaluation z)).eval t) (D (0, 1)) y :=
    (hD.comp y hv).hasDerivAt
  exact hd.unique ((p.map (complexLaurentEvaluation z)).hasDerivAt y)

private theorem laurentRootValue_simpleDerivative (p : Polynomial (LaurentPolynomial ℂ))
    {z y : ℂ} (hz : z ≠ 0)
    (hsimple : ((p.map (StrictEUnit.stage16_laurentEval (Units.mk0 z hz))).derivative).eval y ≠ 0) :
    HasStrictFDerivAt (laurentRootValue p) (fderiv ℂ (laurentRootValue p) (z, y)) (z, y) ∧
      fderiv ℂ (laurentRootValue p) (z, y) (0, 1) ≠ 0 := by
  have hF := (laurentRootValue_analyticAt (y := y) p hz).hasStrictFDerivAt
  refine ⟨hF, ?_⟩
  rw [laurentRootValue_verticalDerivative p hF.hasFDerivAt, complexLaurentEvaluation_of_ne hz]
  exact hsimple

/-- The simple roots of the actual Laurent equation are locally the graph of
a continuous section on the punctured base. -/
theorem exists_laurent_simple_root_chart (p : Polynomial (LaurentPolynomial ℂ))
    {z₀ y₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (hroot : (p.map (StrictEUnit.stage16_laurentEval (Units.mk0 z₀ hz₀))).eval y₀ = 0)
    (hsimple : ((p.map (StrictEUnit.stage16_laurentEval (Units.mk0 z₀ hz₀))).derivative).eval y₀ ≠ 0) :
    ∃ (s : ℂ → ℂ) (U V : Set ℂ), IsOpen U ∧ z₀ ∈ U ∧ (∀ z ∈ U, z ≠ 0) ∧
      IsOpen V ∧ y₀ ∈ V ∧ s z₀ = y₀ ∧ DifferentiableAt ℂ s z₀ ∧ ContinuousOn s U ∧
      MapsTo s U V ∧ ∀ z ∈ U, ∀ y ∈ V, ∀ hz : z ≠ 0,
        (p.map (StrictEUnit.stage16_laurentEval (Units.mk0 z hz))).eval y = 0 ↔ y = s z := by
  obtain ⟨hF, hD⟩ := laurentRootValue_simpleDerivative p hz₀ hsimple
  have hzero : laurentRootValue p (z₀, y₀) = 0 := (laurentRootValue_of_ne p hz₀ y₀).trans hroot
  obtain ⟨s, U, V, hU, hzU, hV, hyV, hs₀, hs, hsCont, hsV, hgraph⟩ := exists_local_simple_root hF hzero hD
  let W := U ∩ ({0}ᶜ : Set ℂ)
  refine ⟨s, W, V, hU.inter isClosed_singleton.isOpen_compl, ⟨hzU, hz₀⟩, fun _ hz => hz.2,
    hV, hyV, hs₀, hs, hsCont.mono inter_subset_left, fun _ hz => hsV hz.1, ?_⟩
  intro z hzU' y hyV' hz'
  rw [← laurentRootValue_of_ne p hz' y]
  exact hgraph z hzU'.1 y hyV'

/-- The branch at a simple root of the Laurent equation agrees with every
continuous germ satisfying the same equation and initial value. -/
theorem exists_unique_laurent_simple_root_germ (p : Polynomial (LaurentPolynomial ℂ))
    {z₀ y₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (hroot : (p.map (StrictEUnit.stage16_laurentEval (Units.mk0 z₀ hz₀))).eval y₀ = 0)
    (hsimple : ((p.map (StrictEUnit.stage16_laurentEval (Units.mk0 z₀ hz₀))).derivative).eval y₀ ≠ 0) :
    ∃ s : ℂ → ℂ, s z₀ = y₀ ∧ DifferentiableAt ℂ s z₀ ∧
      (∀ᶠ z in 𝓝 z₀, ∃ hz : z ≠ 0,
        (p.map (StrictEUnit.stage16_laurentEval (Units.mk0 z hz))).eval (s z) = 0) ∧
      ∀ t : ℂ → ℂ, ContinuousAt t z₀ → t z₀ = y₀ →
        (∀ᶠ z in 𝓝 z₀, ∃ hz : z ≠ 0,
          (p.map (StrictEUnit.stage16_laurentEval (Units.mk0 z hz))).eval (t z) = 0) → t =ᶠ[𝓝 z₀] s := by
  obtain ⟨hF, hD⟩ := laurentRootValue_simpleDerivative p hz₀ hsimple
  have hzero : laurentRootValue p (z₀, y₀) = 0 := (laurentRootValue_of_ne p hz₀ y₀).trans hroot
  obtain ⟨s, hs₀, hsDiff, hs, huniq⟩ := exists_unique_simple_root_germ hF hzero hD
  refine ⟨s, hs₀, hsDiff, ?_, ?_⟩
  · have hnear : ∀ᶠ z in 𝓝 z₀, z ≠ (0 : ℂ) := isClosed_singleton.isOpen_compl.mem_nhds hz₀
    filter_upwards [hnear, hs] with z hz hsz
    exact ⟨hz, (laurentRootValue_of_ne p hz (s z)).symm.trans hsz⟩
  · intro t ht ht₀ htroot
    apply huniq t ht ht₀
    filter_upwards [htroot] with z htz
    obtain ⟨hz, htz⟩ := htz
    exact (laurentRootValue_of_ne p hz (t z)).trans htz

end Laurent

end WideE
