import WideE.BlockDiagonalHopfQuotient
import Mathlib.RingTheory.Polynomial.Pochhammer

/-! Polynomial power curves connect all points of a unitriangular group. -/

noncomputable section

open scoped Matrix BigOperators TensorProduct

namespace WideE

section PolynomialPowers

variable {k : Type*} [Field k] [CharZero k] {n : ℕ}

omit [CharZero k] in
private theorem strictUpperTriangular_pow_eq_zero (N : Matrix (Fin n) (Fin n) k)
    (hN : ∀ i j, j ≤ i → N i j = 0) : N ^ n = 0 := by
  have hPow (r : ℕ) (i j : Fin n) (h : (j : ℕ) < (i : ℕ) + r) : (N ^ r) i j = 0 := by
    induction r generalizing i j with
    | zero =>
      have hji : j < i := by simpa only [Nat.add_zero] using h
      rw [pow_zero, Matrix.one_apply, if_neg hji.ne']
    | succ r ih =>
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : (l : ℕ) < (i : ℕ) + r
      · rw [ih i l hl, zero_mul]
      · have hle : j ≤ l := by
          change (j : ℕ) ≤ (l : ℕ)
          omega
        rw [hN l j hle, mul_zero]
  ext i j
  exact hPow n i j (j.isLt.trans_le (Nat.le_add_left n i.val))

private def binomialPolynomial (r : ℕ) : Polynomial k :=
  Polynomial.C (r.factorial : k)⁻¹ * descPochhammer k r

private theorem binomialPolynomial_eval_nat (m r : ℕ) :
    (binomialPolynomial (k := k) r).eval (m : k) = (m.choose r : k) := by
  have hr : (r.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [binomialPolynomial, Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]

private def unitriangularPowerPolynomial (P : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    Polynomial k :=
  ∑ r ∈ Finset.range n, binomialPolynomial r * Polynomial.C (((P - 1) ^ r) i j)

private theorem unitriangularPowerPolynomial_eval_nat
    (P : Matrix (Fin n) (Fin n) k) (hN : (P - 1) ^ n = 0)
    (m : ℕ) (i j : Fin n) :
    (unitriangularPowerPolynomial P i j).eval (m : k) = (P ^ m) i j := by
  let N := P - 1
  have hPow : P ^ m = ∑ r ∈ Finset.range (m + 1), (m.choose r : k) • N ^ r := by
    rw [show P = N + 1 from (sub_add_cancel P 1).symm, (Commute.one_right N).add_pow]
    simp only [one_pow, mul_one, ← nsmul_eq_mul', Nat.cast_smul_eq_nsmul]
  let a (r : ℕ) := (m.choose r : k) * (N ^ r) i j
  have hAgree : (∑ r ∈ Finset.range n, a r) = ∑ r ∈ Finset.range (m + 1), a r := by
    calc
      _ = ∑ r ∈ Finset.range (max n (m + 1)), a r := by
        apply Finset.sum_subset (Finset.range_mono (le_max_left _ _))
        intro r _ hr
        have hn : n ≤ r := Nat.le_of_not_lt fun h => hr (Finset.mem_range.mpr h)
        have hZero : N ^ r = 0 := by
          rw [← Nat.add_sub_of_le hn, pow_add, show N ^ n = 0 from hN, zero_mul]
        simp only [a, hZero, Matrix.zero_apply, mul_zero]
      _ = _ := by
        symm
        apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
        intro r _ hr
        have hm : m < r := Nat.lt_of_succ_le (Nat.le_of_not_lt fun h => hr (Finset.mem_range.mpr h))
        simp only [a, Nat.choose_eq_zero_of_lt hm, Nat.cast_zero, zero_mul]
  rw [hPow, unitriangularPowerPolynomial, Polynomial.eval_finset_sum]
  simpa only [Polynomial.eval_mul, binomialPolynomial_eval_nat, Polynomial.eval_C, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul] using hAgree

private theorem polynomial_eq_zero_of_nat_eval (p : Polynomial k)
    (hp : ∀ m : ℕ, p.eval (m : k) = 0) : p = 0 := by
  by_contra h
  have hf := Polynomial.finite_setOf_isRoot h
  apply Set.infinite_range_of_injective (Nat.cast_injective (R := k))
  apply hf.subset
  rintro _ ⟨m, rfl⟩
  exact hp m

end PolynomialPowers

section Group

universe u

variable {k H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  {n : ℕ} (M : Matrix (Fin n) (Fin n) H)

omit [CharZero k] in
private theorem hopfMatrix_map_pow
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (M i j) = if i = j then 1 else 0)
    (p : H →ₐ[k] k) (m : ℕ) :
    letI := hopfPointGroup (k := k) (H := H) (A := k)
    M.map (p ^ m) = (M.map p) ^ m := by
  letI := hopfPointGroup (k := k) (H := H) (A := k)
  have hMul (a b : H →ₐ[k] k) : M.map (a * b) = M.map a * M.map b := by
    ext i j
    change tensorPoint a b (Coalgebra.comul (R := k) (M i j)) = _
    rw [hΔ, map_sum, Matrix.mul_apply]
    simp only [tensorPoint_tmul, Matrix.map_apply]
  induction m with
  | zero =>
    rw [pow_zero, pow_zero]
    ext i j
    change Bialgebra.counitAlgHom k H (M i j) = _
    rw [Matrix.one_apply]
    exact hε i j
  | succ m ih =>
    rw [pow_succ, pow_succ, hMul, ih]

/-- The nonnegative integral powers of any point lie on one polynomial curve
inside the affine group, with the identity at zero and the point at one. -/
theorem exists_unitriangularPolynomialPower
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (M i j) = if i = j then 1 else 0)
    (hUpper : M.BlockTriangular id) (hDiag : ∀ i, M i i = 1)
    (hGen : Algebra.adjoin k (Set.range fun ij : Fin n × Fin n => M ij.1 ij.2) = ⊤)
    (p : H →ₐ[k] k) :
    letI := hopfPointGroup (k := k) (H := H) (A := k)
    ∃ γ : H →ₐ[k] Polynomial k, ∀ m : ℕ, (Polynomial.aeval (m : k)).comp γ = p ^ m := by
  letI := hopfPointGroup (k := k) (H := H) (A := k)
  let P := M.map p
  have hNil : (P - 1) ^ n = 0 := by
    apply strictUpperTriangular_pow_eq_zero
    intro i j hle
    rcases hle.lt_or_eq with hlt | rfl
    · have hij : M i j = 0 := hUpper hlt
      simp only [P, Matrix.sub_apply, Matrix.map_apply, hij, map_zero, Matrix.one_apply, if_neg hlt.ne',
        sub_zero]
    · simp only [P, Matrix.sub_apply, Matrix.map_apply, hDiag, map_one, Matrix.one_apply, if_pos rfl, if_true,
        sub_self]
  let f : MvPolynomial (Fin n × Fin n) k →ₐ[k] H := MvPolynomial.aeval fun ij => M ij.1 ij.2
  have hf : Function.Surjective f := (AlgHom.range_eq_top f).mp
    ((Algebra.adjoin_range_eq_range_aeval k _).symm.trans hGen)
  let v : MvPolynomial (Fin n × Fin n) k →ₐ[k] Polynomial k :=
    MvPolynomial.aeval fun ij => unitriangularPowerPolynomial P ij.1 ij.2
  have hEval (m : ℕ) : (Polynomial.aeval (m : k)).comp v = (p ^ m).comp f := by
    apply MvPolynomial.algHom_ext
    intro ij
    simp only [AlgHom.comp_apply, v, f, MvPolynomial.aeval_X]
    change (unitriangularPowerPolynomial P ij.1 ij.2).eval (m : k) = (p ^ m) (M ij.1 ij.2)
    rw [unitriangularPowerPolynomial_eval_nat P hNil, ← hopfMatrix_map_pow M hΔ hε p m]
    rfl
  let I := RingHom.ker f.toRingHom
  have hI : I ≤ RingHom.ker v.toRingHom := by
    intro w hw
    change v w = 0
    apply polynomial_eq_zero_of_nat_eval
    intro m
    have h := DFunLike.congr_fun (hEval m) w
    change (v w).eval (m : k) = (p ^ m) (f w) at h
    change f w = 0 at hw
    rwa [hw, map_zero] at h
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := f) hf
  let γ := (Ideal.Quotient.liftₐ I v hI).comp e.symm.toAlgHom
  refine ⟨γ, fun m => AlgHom.ext fun z => ?_⟩
  obtain ⟨w, rfl⟩ := hf z
  have hγ : γ (f w) = v w := by
    change Ideal.Quotient.liftₐ I v hI (e.symm (e (Ideal.Quotient.mk I w))) = v w
    rw [AlgEquiv.symm_apply_apply]
    rfl
  exact (congrArg (Polynomial.aeval (m : k)) hγ).trans (DFunLike.congr_fun (hEval m) w)

/-- A group with a generating unitriangular representation is connected. -/
theorem unitriangular_connectedSpace [IsAlgClosed k]
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (M i j) = if i = j then 1 else 0)
    (hUpper : M.BlockTriangular id) (hDiag : ∀ i, M i i = 1)
    (hGen : Algebra.adjoin k (Set.range fun ij : Fin n × Fin n => M ij.1 ij.2) = ⊤) :
    ConnectedSpace (PrimeSpectrum H) := by
  let ε := Bialgebra.counitAlgHom k H
  let e := hopfPointPrime ε
  refine connectedSpace_iff_connectedComponent.mpr ⟨e, Set.eq_univ_of_forall fun x => ?_⟩
  by_contra hx
  letI : Algebra.FiniteType k H := ⟨Subalgebra.fg_def.mpr ⟨_, Set.finite_range _, hGen⟩⟩
  letI : IsJacobsonRing H := isJacobsonRing_of_finiteType (A := k) (B := H)
  obtain ⟨y, hy, hClosed⟩ := PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing
    ((connectedComponent e)ᶜ) isClosed_connectedComponent.isOpen_compl ⟨x, hx⟩
  letI : y.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hClosed
  let p := StrictEUnit.maximalIdealPoint (k := k) y.asIdeal
  have hpy : hopfPointPrime p = y := PrimeSpectrum.ext (StrictEUnit.maximalIdealPoint_ker _)
  letI := hopfPointGroup (k := k) (H := H) (A := k)
  obtain ⟨γ, hγ⟩ := exists_unitriangularPolynomialPower M hΔ hε hUpper hDiag hGen p
  let C := PrimeSpectrum.comap γ.toRingHom
  have hC : IsPreconnected (Set.range C) := isPreconnected_range C.continuous
  let r (a : k) : PrimeSpectrum (Polynomial k) :=
    ⟨RingHom.ker (Polynomial.aeval a).toRingHom, RingHom.ker_isPrime _⟩
  have hCzero : C (r 0) = e := by
    have h : (Polynomial.aeval (0 : k)).comp γ = ε := by
      simpa only [Nat.cast_zero, pow_zero] using hγ 0
    exact PrimeSpectrum.ext (congrArg (fun f : H →ₐ[k] k => RingHom.ker f.toRingHom) h)
  have hCone : C (r 1) = y := by
    have h : (Polynomial.aeval (1 : k)).comp γ = p := by
      simpa only [Nat.cast_one, pow_one] using hγ 1
    exact (PrimeSpectrum.ext (congrArg (fun f : H →ₐ[k] k => RingHom.ker f.toRingHom) h)).trans hpy
  exact hy (hC.subset_connectedComponent ⟨r 0, hCzero⟩ ⟨r 1, hCone⟩)

/-- The identity fiber of the diagonal-block quotient is connected. -/
theorem blockDiagonalKernel_connectedSpace [IsAlgClosed k] {β : Type*} [LinearOrder β]
    (b : Fin n → β) (hb : Monotone b)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (M i j) = if i = j then 1 else 0)
    (hUpper : M.BlockTriangular b)
    (hGen : Algebra.adjoin k (Set.range fun ij : Fin n × Fin n => M ij.1 ij.2) = ⊤) :
    ConnectedSpace (PrimeSpectrum (H ⧸ blockDiagonalKernelIdeal b M hΔ hUpper)) := by
  letI := (blockDiagonalKernelIdeal_isHopf b M hΔ hUpper).quotientHopf
  obtain ⟨hD, he, hG⟩ := blockDiagonalKernelMatrix_relations b M hΔ hUpper hε hGen
  obtain ⟨ht, hd⟩ := blockDiagonalKernelMatrix_unitriangular b M hΔ hUpper hb hε
  exact unitriangular_connectedSpace (blockDiagonalKernelMatrix b M hΔ hUpper) hD he ht hd hG

end Group

end WideE
