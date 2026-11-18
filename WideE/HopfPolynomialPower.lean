import WideE.HopfLieMatrixAdjoint
import WideE.KostantWeightAlgebra
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Polynomial powers of unipotent group points

For a point whose generating matrix is unipotent, interpolate its
nonnegative powers using the binomial polynomials. The argument extends
the polynomial construction in `UnitriangularConnected` to any nilpotent
matrix difference from the identity. Its tangent has the same leading
weight as that difference.
-/

noncomputable section

open scoped Matrix Polynomial TensorProduct

namespace WideE

section BinomialPowers

variable {k ι : Type*} [Field k] [CharZero k] [Fintype ι] [DecidableEq ι]

private def binomialPolynomial (r : ℕ) : k[X] :=
  Polynomial.C (r.factorial : k)⁻¹ * descPochhammer k r

private theorem binomialPolynomial_eval_nat (m r : ℕ) :
    (binomialPolynomial (k := k) r).eval (m : k) = (m.choose r : k) := by
  have hr : (r.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [binomialPolynomial, Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]

private def matrixPowerPolynomial (P : Matrix ι ι k) (d : ℕ) (i j : ι) : k[X] :=
  ∑ r ∈ Finset.range d, binomialPolynomial r * Polynomial.C (((P - 1) ^ r) i j)

private theorem matrixPowerPolynomial_eval_nat (P : Matrix ι ι k) {d : ℕ}
    (hN : (P - 1) ^ d = 0) (m : ℕ) (i j : ι) :
    (matrixPowerPolynomial P d i j).eval (m : k) = (P ^ m) i j := by
  let N := P - 1
  have hPow : P ^ m = ∑ r ∈ Finset.range (m + 1), (m.choose r : k) • N ^ r := by
    rw [show P = N + 1 from (sub_add_cancel P 1).symm, (Commute.one_right N).add_pow]
    simp only [one_pow, mul_one, ← nsmul_eq_mul', Nat.cast_smul_eq_nsmul]
  let a (r : ℕ) := (m.choose r : k) * (N ^ r) i j
  have hAgree : (∑ r ∈ Finset.range d, a r) = ∑ r ∈ Finset.range (m + 1), a r := by
    calc
      _ = ∑ r ∈ Finset.range (max d (m + 1)), a r := by
        apply Finset.sum_subset (Finset.range_mono (le_max_left _ _))
        intro r _ hr
        have hr' : d ≤ r := Nat.le_of_not_lt fun h => hr (Finset.mem_range.mpr h)
        have hZero : N ^ r = 0 := pow_eq_zero_of_le hr' hN
        simp only [a, hZero, Matrix.zero_apply, mul_zero]
      _ = _ := by
        symm
        apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
        intro r _ hr
        have hm : m < r := Nat.lt_of_succ_le (Nat.le_of_not_lt fun h => hr (Finset.mem_range.mpr h))
        simp only [a, Nat.choose_eq_zero_of_lt hm, Nat.cast_zero, zero_mul]
  rw [hPow, matrixPowerPolynomial, Polynomial.eval_finset_sum]
  simpa only [Polynomial.eval_mul, binomialPolynomial_eval_nat, Polynomial.eval_C, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul] using hAgree

omit [Fintype ι] [DecidableEq ι] in
private theorem polynomial_eq_zero_of_eval_nat (p : k[X]) (hp : ∀ m : ℕ, p.eval (m : k) = 0) :
    p = 0 := by
  by_contra h
  apply Set.infinite_range_of_injective (Nat.cast_injective (R := k))
  exact (Polynomial.finite_setOf_isRoot h).subset (by rintro _ ⟨m, rfl⟩; exact hp m)

end BinomialPowers

section ActualPowers

variable {k H ι : Type*} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Fintype ι] [DecidableEq ι]

variable (U : (Matrix ι ι H)ˣ)
  (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
  (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
  (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)

include hD he hGen in
private theorem exists_hopfPolynomialPower_of_pow_eq_zero (p : H →ₐ[k] k) {d : ℕ}
    (hN : (U.val.map p - 1) ^ d = 0) :
    letI : Group (H →ₐ[k] k) := hopfPointGroup
    ∃ γ : H →ₐ[k] k[X], (∀ i j, γ (U.val i j) = matrixPowerPolynomial (U.val.map p) d i j) ∧
      ∀ m : ℕ, (Polynomial.aeval (m : k)).comp γ = p ^ m := by
  letI : Group (H →ₐ[k] k) := hopfPointGroup
  let f : MvPolynomial (ι × ι) k →ₐ[k] H := MvPolynomial.aeval fun ij => U.val ij.1 ij.2
  have hf : Function.Surjective f := (AlgHom.range_eq_top f).mp
    ((Algebra.adjoin_range_eq_range_aeval k _).symm.trans hGen)
  let v : MvPolynomial (ι × ι) k →ₐ[k] k[X] :=
    MvPolynomial.aeval fun ij => matrixPowerPolynomial (U.val.map p) d ij.1 ij.2
  have hEval (m : ℕ) : (Polynomial.aeval (m : k)).comp v = (p ^ m).comp f := by
    have hPow : U.val.map (p ^ m) = (U.val.map p) ^ m :=
      congrArg Units.val ((hopfPointMatrix U hD he).map_pow p m)
    apply MvPolynomial.algHom_ext
    intro ij
    simp only [AlgHom.comp_apply, v, f, MvPolynomial.aeval_X]
    change (matrixPowerPolynomial (U.val.map p) d ij.1 ij.2).eval (m : k) =
      (U.val.map (p ^ m)) ij.1 ij.2
    rw [matrixPowerPolynomial_eval_nat _ hN, hPow]
  let I := RingHom.ker f.toRingHom
  have hI : I ≤ RingHom.ker v.toRingHom := by
    intro w hw
    change v w = 0
    apply polynomial_eq_zero_of_eval_nat
    intro m
    have h := DFunLike.congr_fun (hEval m) w
    change (v w).eval (m : k) = (p ^ m) (f w) at h
    change f w = 0 at hw
    rwa [hw, map_zero] at h
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := f) hf
  let γ := (Ideal.Quotient.liftₐ I v hI).comp e.symm.toAlgHom
  have hγ (w : MvPolynomial (ι × ι) k) : γ (f w) = v w := by
    change Ideal.Quotient.liftₐ I v hI (e.symm (e (Ideal.Quotient.mk I w))) = v w
    rw [AlgEquiv.symm_apply_apply]
    rfl
  refine ⟨γ, fun i j => ?_, fun m => AlgHom.ext fun z => ?_⟩
  · simpa only [v, f, MvPolynomial.aeval_X] using hγ (MvPolynomial.X (i, j))
  · obtain ⟨w, rfl⟩ := hf z
    exact (congrArg (Polynomial.aeval (m : k)) (hγ w)).trans (DFunLike.congr_fun (hEval m) w)

private theorem coeff_one_mul (p q : k[X]) :
    (p * q).coeff 1 = p.coeff 0 * q.coeff 1 + q.coeff 0 * p.coeff 1 := by
  have h (a : k[X]) : a.derivative.eval 0 = a.coeff 1 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
    simp
  rw [← h, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
    h, h, ← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero]
  ring

include hD he hGen in
private theorem exists_hopfLieMatrix_polynomialPower (p : H →ₐ[k] k) {d : ℕ}
    (hN : (U.val.map p - 1) ^ d = 0) :
    ∃ D : hopfInvariantDerivations k H,
      hopfLieMatrix U.val D =
        ∑ r ∈ Finset.range d, (binomialPolynomial (k := k) r).coeff 1 • (U.val.map p - 1) ^ r := by
  letI : Group (H →ₐ[k] k) := hopfPointGroup
  obtain ⟨γ, hMatrix, hEval⟩ := exists_hopfPolynomialPower_of_pow_eq_zero U hD he hGen p hN
  have h₀ (a : H) : (γ a).coeff 0 = Bialgebra.counitAlgHom k H a := by
    rw [Polynomial.coeff_zero_eq_aeval_zero]
    have h := DFunLike.congr_fun (hEval 0) a
    simp only [Nat.cast_zero, pow_zero, AlgHom.comp_apply] at h
    exact h
  let δ : hopfCounitDerivations k H k := ⟨(Polynomial.lcoeff k 1).comp γ.toLinearMap, fun a b => by
    change (γ (a * b)).coeff 1 = _ * (γ b).coeff 1 + _ * (γ a).coeff 1
    rw [map_mul, coeff_one_mul, h₀, h₀]⟩
  let x := (hopfLieDerivationEquiv k H k).symm δ
  refine ⟨hopfLieVectorInvariantDerivations x, Matrix.ext fun i j => ?_⟩
  change (Bialgebra.counitAlgHom k H) ((hopfLieVectorInvariantDerivations x).val (U.val i j)) = _
  rw [hopfLieVectorInvariantDerivations_counit, hopfLieDerivationEquiv_symm_apply]
  change (γ (U.val i j)).coeff 1 = _
  rw [hMatrix, matrixPowerPolynomial]
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_mul_C, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]

include hD he hGen in
/-- At every strictly negative depth, the matrix of a genuine group tangent agrees
with the group matrix minus the identity through its leading depth. -/
theorem exists_hopfLieMatrix_leading_of_mem_kostantWeightFiltration
    (p : H →ₐ[k] k) (a : Matrix ι ι k) {r : ℕ} (hr : 0 < r)
    (hp : U.val.map p - 1 ∈ kostantWeightFiltration (k := k) a r) :
    ∃ D : hopfInvariantDerivations k H,
      hopfLieMatrix U.val D - (U.val.map p - 1) ∈ kostantWeightFiltration (k := k) a (r + 1) := by
  let N := U.val.map p - 1
  obtain ⟨d, hd⟩ := isNilpotent_of_mem_kostantWeightFiltration a hr hp
  have hd' : N ^ (2 + d) = 0 := pow_eq_zero_of_le (by omega) hd
  obtain ⟨D, hD'⟩ := exists_hopfLieMatrix_polynomialPower U hD he hGen p hd'
  refine ⟨D, ?_⟩
  rw [hD', Finset.sum_range_add]
  have hHead : (∑ i ∈ Finset.range 2, (binomialPolynomial (k := k) i).coeff 1 • N ^ i) = N := by
    simp [Finset.sum_range_succ, binomialPolynomial, descPochhammer_zero, descPochhammer_one, Polynomial.coeff_one]
  change (∑ i ∈ Finset.range 2, (binomialPolynomial (k := k) i).coeff 1 • N ^ i) +
    (∑ i ∈ Finset.range d, (binomialPolynomial (k := k) (2 + i)).coeff 1 • N ^ (2 + i)) -
      N ∈ kostantWeightFiltration (k := k) a (r + 1)
  rw [hHead, add_comm N, add_sub_cancel_right]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  refine kostantWeightFiltration_antitone a ?_ (pow_mem_kostantWeightFiltration a hp (2 + i))
  have hLe : 2 * r ≤ (2 + i) * r := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  omega

end ActualPowers

end WideE
