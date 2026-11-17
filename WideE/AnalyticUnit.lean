import ElementaryGeneratorGrowth
import Stage17ArithmeticPowerPullback
import Stage18BoundedArithmeticLocalization
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Analytic realization of Laurent units

A finite Laurent realization of bounded arithmetic entire functions can be
written with a single monomial denominator. The resulting arithmetic entire
fraction is classified by the existing complex-analytic theorem.
-/

noncomputable section

open scoped BigOperators Topology
open Filter StrictEUnit

namespace WideE

/-- Evaluation of a Laurent polynomial at a nonzero complex argument. -/
def evalLaurentAt (k : Subfield ℂ) (z : Stage16PuncturedPlane) :
    LaurentPolynomial k →+* ℂ :=
  LaurentPolynomial.eval₂ k.subtype (Units.mk0 z.val z.property)

@[simp] theorem evalLaurentAt_T (k : Subfield ℂ) (z : Stage16PuncturedPlane) (n : ℤ) :
    evalLaurentAt k z (LaurentPolynomial.T n) = z.val ^ n := by
  simp only [evalLaurentAt, LaurentPolynomial.eval₂_T, Units.val_zpow_eq_zpow_val, Units.val_mk0]

@[simp] theorem evalLaurentAt_C (k : Subfield ℂ) (z : Stage16PuncturedPlane) (a : k) :
    evalLaurentAt k z (LaurentPolynomial.C a) = (a : ℂ) :=
  LaurentPolynomial.eval₂_C _ _ _

@[simp] theorem evalLaurentAt_one (k : Subfield ℂ) (p : LaurentPolynomial k) :
    evalLaurentAt k ⟨1, one_ne_zero⟩ p =
      ((LaurentPolynomial.eval₂ (RingHom.id k) (1 : kˣ) p : k) : ℂ) := by
  have hunit : Units.mk0 (1 : ℂ) one_ne_zero = 1 := Units.ext rfl
  unfold evalLaurentAt
  simp only [hunit]
  refine p.induction_on' ?_ ?_
  · intro p q hp hq
    rw [map_add, map_add, hp, hq]
    rfl
  · intro n a
    simp [LaurentPolynomial.eval₂_C_mul_T]

private def boundedCoordinate (k : Subfield ℂ) (D : ℕ) :
    stage18_boundedArithmeticEntireAlgebra k D :=
  stage18_boundArithmeticFunction k D (subfieldEntireCoordinate k)
    (powerExponentialBound_coordinate D (id : ℂ → ℂ))

/-- An arithmetic entire numerator divided by a monomial has the expected
exterior bound on the punctured plane. -/
theorem puncturedBound_of_monomial_fraction (k : Subfield ℂ) {D L : ℕ}
    (F : stage18_boundedArithmeticEntireAlgebra k D)
    (u : Stage16PuncturedPlane → ℂ)
    (hu : ∀ z, u z = F.val z.val / z.val ^ L) :
    HasPowerExponentialBoundOn D (fun z : Stage16PuncturedPlane => z.val) u := by
  obtain ⟨C, hC, M, hF⟩ := F.property.2.2
  refine ⟨C, hC, M, fun z hz => ?_⟩
  rw [hu z, norm_div, norm_pow]
  exact (div_le_self (norm_nonneg _) (one_le_pow₀ hz)).trans (hF z.val hz)

/-- A punctured unit represented by a bounded arithmetic entire numerator
over a power of the coordinate has the form of Lemma 9.1. -/
theorem puncturedUnit_eq_zpow_exp_polynomial (k : Subfield ℂ) {D L : ℕ}
    (hD : 0 < D) (F : stage18_boundedArithmeticEntireAlgebra k D)
    {u v : Stage16PuncturedPlane → ℂ}
    (hu : ∀ z, u z = F.val z.val / z.val ^ L)
    (huv : ∀ z, u z * v z = 1) :
    ∃ m : ℤ, ∃ α : k, ∃ P : Polynomial k,
      α ≠ 0 ∧ P.coeff 0 = 0 ∧ P.natDegree ≤ D ∧
      ∀ z, u z = (α : ℂ) * z.val ^ m * Complex.exp ((P.map k.subtype).eval z.val) := by
  let G := (boundedCoordinate k D) ^ L
  have hG (z : ℂ) : G.val z = z ^ L := rfl
  have hFnz (z : ℂ) (hz : z ≠ 0) : F.val z ≠ 0 := by
    intro hzero
    let w : Stage16PuncturedPlane := ⟨z, hz⟩
    have hwu := hu w
    change u w = F.val z / z ^ L at hwu
    have h0 : u w = 0 := by rw [hwu, hzero, zero_div]
    exact zero_ne_one (by simpa only [h0, zero_mul] using huv w)
  obtain ⟨m, α, P, hα, hP0, hPD, hclass⟩ :=
    stage18_entire_fraction_eq_zpow_subfield_exp_polynomial k hD F.property.1
      G.property.1 hFnz (fun z hz => hG z ▸ pow_ne_zero L hz)
      F.property.2.2 G.property.2.2 F.property.2.1 G.property.2.1
  refine ⟨m, α, P, hα, hP0, hPD, fun z => ?_⟩
  rw [hu z, ← hG z.val]
  exact hclass z.val z.property

/-- The monomial factor disappears at the normalization point one. -/
theorem puncturedUnit_at_one_eq_scalar_exp (k : Subfield ℂ) {D L : ℕ}
    (hD : 0 < D) (F : stage18_boundedArithmeticEntireAlgebra k D)
    {u v : Stage16PuncturedPlane → ℂ}
    (hu : ∀ z, u z = F.val z.val / z.val ^ L)
    (huv : ∀ z, u z * v z = 1) :
    ∃ α β : k, α ≠ 0 ∧ u ⟨1, one_ne_zero⟩ = (α : ℂ) * Complex.exp (β : ℂ) := by
  obtain ⟨m, α, P, hα, _, _, hclass⟩ :=
    puncturedUnit_eq_zpow_exp_polynomial k hD F hu huv
  have hEval : (P.map k.subtype).eval 1 = (P.eval 1 : k) := by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_one k.subtype
  exact ⟨α, P.eval 1, hα,
    by simpa only [one_zpow, mul_one, hEval] using hclass ⟨1, one_ne_zero⟩⟩

private theorem exists_common_laurent_denominator {ι : Type*} [Fintype ι]
    (k : Subfield ℂ) (p : ι → LaurentPolynomial k) :
    ∃ L : ℕ, ∃ P : ι → Polynomial k, ∀ i,
      (P i).toLaurent = p i * LaurentPolynomial.T (L : ℤ) := by
  classical
  choose s Q hQ using fun i => (p i).exists_T_pow
  let L := ∑ i, s i
  refine ⟨L, fun i => Q i * Polynomial.X ^ (L - s i), fun i => ?_⟩
  have hs : s i ≤ L := Finset.single_le_sum (fun j _ => Nat.zero_le (s j)) (Finset.mem_univ i)
  have hL : (s i : ℤ) + ((L - s i : ℕ) : ℤ) = (L : ℤ) := by
    exact_mod_cast Nat.add_sub_of_le hs
  simp only [map_mul, hQ, Polynomial.toLaurent_X_pow, mul_assoc, ← LaurentPolynomial.T_add,
    hL]

/-- Clearing the Laurent denominators of a finite sum gives an actual entire
numerator with the same growth degree and coefficient subfield. -/
theorem exists_bounded_numerator_of_laurent_sum {ι : Type*} [Fintype ι]
    (k : Subfield ℂ) (D : ℕ) (p : ι → LaurentPolynomial k)
    (f : ι → stage18_boundedArithmeticEntireAlgebra k D) :
    ∃ L : ℕ, ∃ F : stage18_boundedArithmeticEntireAlgebra k D,
      ∀ z : Stage16PuncturedPlane,
        (∑ i, evalLaurentAt k z (p i) * (f i).val z.val) = F.val z.val / z.val ^ L := by
  classical
  obtain ⟨L, P, hP⟩ := exists_common_laurent_denominator k p
  let A := stage18_boundedArithmeticEntireAlgebra k D
  let F : A := ∑ i, Polynomial.aeval (boundedCoordinate k D) (P i) * f i
  refine ⟨L, F, fun z => (eq_div_iff (pow_ne_zero L z.property)).2 ?_⟩
  let ev : A →ₐ[k] ℂ := (Pi.evalAlgHom k (fun _ : ℂ => ℂ) z.val).comp A.val
  have hP_eval (i : ι) :
      (P i).eval₂ k.subtype z.val = evalLaurentAt k z (p i) * z.val ^ L := by
    have h := congrArg (evalLaurentAt k z) (hP i)
    simpa only [evalLaurentAt, LaurentPolynomial.eval₂_toLaurent, map_mul,
      LaurentPolynomial.eval₂_T_n, Units.val_mk0] using h
  calc
    _ = ∑ i, (evalLaurentAt k z (p i) * z.val ^ L) * (f i).val z.val := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = F.val z.val := by
      change _ = ev F
      rw [show F = ∑ i, Polynomial.aeval (boundedCoordinate k D) (P i) * f i from rfl,
        map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, ← Polynomial.aeval_algHom_apply, ← hP_eval i]
      change _ = Polynomial.aeval z.val (P i) * (f i).val z.val
      rw [Polynomial.aeval_def]
      rfl

/-- The actual power substitution from §8.4 retains algebraic Taylor
coefficients and turns the order-two bound into order $2q$. -/
theorem exists_bounded_numerator_of_ramified_laurent_sum {ι : Type*} [Fintype ι]
    (k : Subfield ℂ) {q : ℕ} (hq : 0 < q)
    (p : ι → LaurentPolynomial k) (f : ι → subfieldEntireFunctionAlgebra k)
    (hf : ∀ i, ∃ C : ℝ, 0 < C ∧
      ∀ z : ℂ, ‖(f i).val.val z‖ ≤ C * Real.exp (‖z‖ ^ 2)) :
    ∃ L : ℕ, ∃ F : stage18_boundedArithmeticEntireAlgebra k (2 * q),
      ∀ z : Stage16PuncturedPlane,
        (∑ i, evalLaurentAt k z (p i) * (f i).val.val (z.val ^ q)) =
          F.val z.val / z.val ^ L := by
  have hg (i : ι) : HasPowerExponentialBound (2 * q)
      (stage17_arithmeticPowerPullback k q hq.ne' (f i)).val.val := by
    obtain ⟨C, hC, hi⟩ := hf i
    apply powerExponentialBound_of_separate_constants (2 * q) 0 id _ C 1 hC zero_le_one
    intro z _
    simpa only [stage17_arithmeticPowerPullback_apply, id_eq, norm_pow, pow_zero,
      mul_one, one_mul, pow_mul, Nat.mul_comm 2 q] using hi (z ^ q)
  simpa only [stage18_boundArithmeticFunction_apply, stage17_arithmeticPowerPullback_apply] using
    exists_bounded_numerator_of_laurent_sum k (2 * q) p
      (fun i => stage18_boundArithmeticFunction k (2 * q)
        (stage17_arithmeticPowerPullback k q hq.ne' (f i)) (hg i))

/-- A Laurent germ with coefficients in k is recorded by a power clearing
the pole, an analytic germ at zero, and its normalized Taylor coefficients. -/
def HasArithmeticLaurentGerm (k : Subfield ℂ) (u : ℂ → ℂ) : Prop :=
  ∃ L : ℕ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
    (∀ n : ℕ, iteratedDeriv n g 0 / (n.factorial : ℂ) ∈ k) ∧
    (fun z => z ^ L * u z) =ᶠ[𝓝[≠] (0 : ℂ)] g

/-- The arithmetic Laurent germ controls actual meromorphy at the origin. -/
theorem HasArithmeticLaurentGerm.meromorphicAt {k : Subfield ℂ} {u : ℂ → ℂ}
    (hu : HasArithmeticLaurentGerm k u) : MeromorphicAt u 0 := by
  obtain ⟨L, g, hg, _, hEq⟩ := hu
  refine (hg.meromorphicAt.div' (analyticAt_id.pow L).meromorphicAt).congr ?_
  filter_upwards [hEq, self_mem_nhdsWithin] with z hz hz0
  have hne := Set.mem_compl_singleton_iff.mp hz0
  exact (div_eq_iff (pow_ne_zero L hne)).2 (hz.symm.trans (mul_comm _ _))

/-- Proposition 8.1 for a finite Laurent realization. The coefficients are
recorded as the normalized Taylor coefficients after clearing the pole. -/
theorem ramifiedLaurentSum_analytic_properties {ι : Type*} [Fintype ι]
    (k : Subfield ℂ) {q : ℕ} (hq : 0 < q)
    (p : ι → LaurentPolynomial k) (f : ι → subfieldEntireFunctionAlgebra k)
    (hf : ∀ i, ∃ C : ℝ, 0 < C ∧
      ∀ z : ℂ, ‖(f i).val.val z‖ ≤ C * Real.exp (‖z‖ ^ 2))
    {u : ℂ → ℂ}
    (hu : ∀ z : Stage16PuncturedPlane,
      u z.val = ∑ i, evalLaurentAt k z (p i) * (f i).val.val (z.val ^ q)) :
    DifferentiableOn ℂ u ({0} : Set ℂ)ᶜ ∧ MeromorphicAt u 0 ∧
      HasArithmeticLaurentGerm k u ∧ HasPowerExponentialBound (2 * q) u := by
  obtain ⟨L, F, hF⟩ := exists_bounded_numerator_of_ramified_laurent_sum k hq p f hf
  have hFrac (z : Stage16PuncturedPlane) : u z.val = F.val z.val / z.val ^ L :=
    (hu z).trans (hF z)
  have hGerm : HasArithmeticLaurentGerm k u := by
    refine ⟨L, F.val, F.property.1.analyticAt 0, ?_, ?_⟩
    · intro n
      have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      rw [← entireCauchyCoefficient_factorial F.property.1 n, mul_div_cancel_left₀ _ hfac]
      exact F.property.2.1 n
    · apply eventuallyEq_nhdsWithin_of_eqOn
      intro z hz
      have hne := Set.mem_compl_singleton_iff.mp hz
      change z^L * u z = F.val z
      rw [hFrac ⟨z, hne⟩, mul_div_cancel₀ _ (pow_ne_zero L hne)]
  refine ⟨?_, hGerm.meromorphicAt, hGerm, ?_⟩
  · refine (F.property.1.differentiableOn.div ((differentiable_id.pow L).differentiableOn)
      (fun z hz => pow_ne_zero L (Set.mem_compl_singleton_iff.mp hz))).congr ?_
    intro z hz
    exact hFrac ⟨z, Set.mem_compl_singleton_iff.mp hz⟩
  · obtain ⟨C, hC, M, hGrowth⟩ :=
      puncturedBound_of_monomial_fraction k F (fun z => u z.val) hFrac
    refine ⟨C, hC, M, fun z hz => ?_⟩
    have hne : z ≠ 0 := by
      rintro rfl
      norm_num at hz
    exact hGrowth ⟨z, hne⟩ hz

/-- Glue the arithmetic germ at zero to the cleared punctured function. -/
theorem exists_bounded_numerator_of_laurent_germ (k : Subfield ℂ) {D : ℕ}
    {u : ℂ → ℂ} (hu : DifferentiableOn ℂ u ({0} : Set ℂ)ᶜ)
    (hgerm : HasArithmeticLaurentGerm k u)
    (hbound : HasPowerExponentialBound D u) :
    ∃ L : ℕ, ∃ F : stage18_boundedArithmeticEntireAlgebra k D,
      ∀ z : Stage16PuncturedPlane, u z.val = F.val z.val / z.val ^ L := by
  obtain ⟨L, g, hg, hg_coeff, hg_eq⟩ := hgerm
  let F : ℂ → ℂ := fun z => if z = 0 then g 0 else z ^ L * u z
  have hlocal : F =ᶠ[𝓝 (0 : ℂ)] g := by
    apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE _ (by simp [F])
    filter_upwards [hg_eq, self_mem_nhdsWithin] with z hEq hz
    have hz0 : z ≠ 0 := by simpa using hz
    simpa [F, hz0] using hEq
  have hF : Differentiable ℂ F := by
    intro z
    by_cases hz : z = 0
    · subst z
      exact (hg.congr hlocal.symm).differentiableAt
    · have hz_mem : z ∈ ({0} : Set ℂ)ᶜ := by simpa using hz
      have hmem := isOpen_compl_singleton.mem_nhds hz_mem
      refine ((differentiableAt_id.pow L).mul
        ((hu z hz_mem).differentiableAt hmem)).congr_of_eventuallyEq ?_
      filter_upwards [hmem] with w hw
      have hw0 : w ≠ 0 := by simpa using hw
      simp [F, hw0]
  have hcoeff (n : ℕ) : entireCauchyCoefficient F n ∈ k := by
    have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hEq : entireCauchyCoefficient F n = iteratedDeriv n g 0 / (n.factorial : ℂ) := by
      apply (eq_div_iff hfac).2
      rw [mul_comm, entireCauchyCoefficient_factorial hF, hlocal.iteratedDeriv_eq n]
    exact hEq ▸ hg_coeff n
  have hF_bound : HasPowerExponentialBound D F := by
    have hpow := powerExponentialBound_pow D id id (powerExponentialBound_coordinate D id) L
    obtain ⟨C, hC, M, hgrowth⟩ :=
      powerExponentialBound_mul D id (fun z : ℂ => z ^ L) u hpow hbound
    refine ⟨C, hC, M, fun z hz => ?_⟩
    have hz0 : z ≠ 0 := by
      rintro rfl
      norm_num at hz
    simpa [F, hz0] using hgrowth z hz
  refine ⟨L, ⟨F, hF, hcoeff, hF_bound⟩, fun z => ?_⟩
  change u z.val = F z.val / z.val ^ L
  simp [F, z.property, mul_div_cancel_left₀ _ (pow_ne_zero L z.property)]

/-- Lemma 9.1 for actual functions on the punctured plane and an arithmetic
Laurent germ at zero. The numerator theorem needs the exterior growth bound
for u. -/
theorem laurentGermUnit_eq_zpow_exp_polynomial (k : Subfield ℂ) {D : ℕ}
    (hD : 0 < D) {u v : ℂ → ℂ} (hu : DifferentiableOn ℂ u ({0} : Set ℂ)ᶜ)
    (hgerm : HasArithmeticLaurentGerm k u)
    (hbound : HasPowerExponentialBound D u)
    (huv : ∀ z : ℂ, z ≠ 0 → u z * v z = 1) :
    ∃ m : ℤ, ∃ α : k, ∃ P : Polynomial k,
      α ≠ 0 ∧ P.coeff 0 = 0 ∧ P.natDegree ≤ D ∧
      ∀ z : ℂ, z ≠ 0 → u z = (α : ℂ) * z ^ m * Complex.exp ((P.map k.subtype).eval z) := by
  obtain ⟨L, F, hF⟩ := exists_bounded_numerator_of_laurent_germ k hu hgerm hbound
  obtain ⟨m, α, P, hα, hP0, hPD, hclass⟩ :=
    puncturedUnit_eq_zpow_exp_polynomial k hD F hF (fun z => huv z.val z.property)
  exact ⟨m, α, P, hα, hP0, hPD, fun z hz => hclass ⟨z, hz⟩⟩

/-- The final analytic implication for the ramified realization of a unit.
At the point one its two scalar parameters lie in the fixed subfield. -/
theorem ramifiedLaurentUnit_at_one_eq_scalar_exp {ι : Type*} [Fintype ι]
    (k : Subfield ℂ) {q : ℕ} (hq : 0 < q)
    (p : ι → LaurentPolynomial k) (f : ι → subfieldEntireFunctionAlgebra k)
    (hf : ∀ i, ∃ C : ℝ, 0 < C ∧
      ∀ z : ℂ, ‖(f i).val.val z‖ ≤ C * Real.exp (‖z‖ ^ 2))
    {u v : Stage16PuncturedPlane → ℂ}
    (hu : ∀ z, u z = ∑ i, evalLaurentAt k z (p i) * (f i).val.val (z.val ^ q))
    (huv : ∀ z, u z * v z = 1) :
    ∃ α β : k, α ≠ 0 ∧ u ⟨1, one_ne_zero⟩ = (α : ℂ) * Complex.exp (β : ℂ) := by
  obtain ⟨L, F, hF⟩ := exists_bounded_numerator_of_ramified_laurent_sum k hq p f hf
  exact puncturedUnit_at_one_eq_scalar_exp k (Nat.mul_pos (by decide) hq) F
    (fun z => (hu z).trans (hF z)) huv

/-- Specializing to the algebraic numbers gives the numerical form used in
the classification of wide E-value units. -/
theorem ramifiedLaurentUnit_at_one_eq_algebraic_scalar_exp {ι : Type*} [Fintype ι]
    {q : ℕ} (hq : 0 < q)
    (p : ι → LaurentPolynomial (algebraicClosure ℚ ℂ).toSubfield)
    (f : ι → subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield)
    (hf : ∀ i, ∃ C : ℝ, 0 < C ∧
      ∀ z : ℂ, ‖(f i).val.val z‖ ≤ C * Real.exp (‖z‖ ^ 2))
    {u v : Stage16PuncturedPlane → ℂ}
    (hu : ∀ z, u z = ∑ i, evalLaurentAt (algebraicClosure ℚ ℂ).toSubfield z (p i) *
      (f i).val.val (z.val ^ q))
    (huv : ∀ z, u z * v z = 1) :
    ∃ α β : ℂ, IsAlgebraic ℚ α ∧ α ≠ 0 ∧ IsAlgebraic ℚ β ∧
      u ⟨1, one_ne_zero⟩ = α * Complex.exp β := by
  obtain ⟨α, β, hα, h⟩ :=
    ramifiedLaurentUnit_at_one_eq_scalar_exp (algebraicClosure ℚ ℂ).toSubfield hq p f hf hu huv
  exact ⟨α, β, mem_algebraicClosure_iff.mp α.property, fun h0 => hα (Subtype.ext h0),
    mem_algebraicClosure_iff.mp β.property, h⟩

end WideE
