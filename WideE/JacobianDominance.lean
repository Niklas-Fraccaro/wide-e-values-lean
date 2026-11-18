import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-!
# A Jacobian criterion for algebraic independence

Over a field of characteristic zero, one can differentiate a least-degree
polynomial relation. An invertible-over-the-fraction-field matrix of
derivatives would then force a relation of smaller degree.
-/

noncomputable section

open scoped Matrix

namespace WideE

section ChainRule

variable {k A ι : Type*} [Field k] [CommRing A] [Algebra k A] [Fintype ι]

/-- The multivariate chain rule for a derivation on the coefficient algebra. -/
theorem derivation_apply_mvPolynomial_aeval (D : Derivation k A A)
    (x : ι → A) (p : MvPolynomial ι k) :
    D (MvPolynomial.aeval x p) = ∑ i, D (x i) * MvPolynomial.aeval x (MvPolynomial.pderiv i p) := by
  classical
  let e := MvPolynomial.aeval (R := k) x
  letI : Algebra (MvPolynomial ι k) A := e.toRingHom.toAlgebra
  letI : IsScalarTower k (MvPolynomial ι k) A := IsScalarTower.of_algHom e
  let r : Derivation k (MvPolynomial ι k) A :=
    ∑ i, D (x i) • (Algebra.linearMap (MvPolynomial ι k) A).compDer (MvPolynomial.pderiv i)
  have hr (q : MvPolynomial ι k) : r q = ∑ i, D (x i) * e (MvPolynomial.pderiv i q) := by
    change Derivation.coeFnAddMonoidHom
      (∑ i, D (x i) • (Algebra.linearMap (MvPolynomial ι k) A).compDer
        (MvPolynomial.pderiv i)) q = _
    rw [map_sum, Finset.sum_apply]
    rfl
  have h : D.compAlgebraMap (MvPolynomial ι k) = r := by
    apply MvPolynomial.derivation_ext
    intro i
    change D (e (MvPolynomial.X i)) = r (MvPolynomial.X i)
    rw [hr, MvPolynomial.aeval_X, Finset.sum_eq_single i]
    · rw [MvPolynomial.pderiv_X_self, map_one, mul_one]
    · intro j _ hji
      rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hji), map_zero, mul_zero]
    · exact fun hj => (hj (Finset.mem_univ _)).elim
  exact (DFunLike.congr_fun h p).trans (hr p)

end ChainRule

section Degrees

variable {k ι : Type*} [Field k]

private theorem coeff_pderiv_shift (p : MvPolynomial ι k) (i : ι) (d : ι →₀ ℕ) :
    (MvPolynomial.pderiv i p).coeff d =
      p.coeff (d + Finsupp.single i 1) * ((d i + 1 : ℕ) : k) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases hm : m i = 0
    · have hne : m ≠ d + Finsupp.single i 1 := by
        intro h
        have hd : m i = d i + 1 := by
          simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using congrArg (fun z : ι →₀ ℕ => z i) h
        rw [hm] at hd
        exact Nat.noConfusion hd
      simp only [hm, Nat.cast_zero, mul_zero, ite_self, if_neg hne, zero_mul]
    · have hEq : m - Finsupp.single i 1 = d ↔ m = d + Finsupp.single i 1 := by
        constructor
        · intro h
          rw [← h, Finsupp.sub_add_single_one_cancel hm]
        · intro h
          rw [h, add_tsub_cancel_right]
      by_cases h : m = d + Finsupp.single i 1
      · have hd : m i = d i + 1 := by
          rw [h, Finsupp.add_apply, Finsupp.single_eq_same]
        rw [if_pos (hEq.mpr h), if_pos h, hd]
      · rw [if_neg (hEq.not.mpr h), if_neg h, zero_mul]
  | add p q hp hq =>
    rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, add_mul]

private theorem pderiv_totalDegree_lt (p : MvPolynomial ι k) (i : ι)
    (hp : 0 < p.totalDegree) : (MvPolynomial.pderiv i p).totalDegree < p.totalDegree := by
  rw [MvPolynomial.totalDegree, Finset.sup_lt_iff hp]
  intro d hd
  have hmem : d + Finsupp.single i 1 ∈ p.support := by
    rw [MvPolynomial.mem_support_iff, coeff_pderiv_shift] at hd
    exact MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hd)
  have hdeg := MvPolynomial.le_totalDegree hmem
  change (d + Finsupp.single i 1).degree ≤ p.totalDegree at hdeg
  change d.degree < p.totalDegree
  rw [Finsupp.degree_add, Finsupp.degree_single] at hdeg
  exact hdeg

private theorem exists_pderiv_ne_zero [CharZero k] (p : MvPolynomial ι k)
    (hp : 0 < p.totalDegree) : ∃ i, MvPolynomial.pderiv i p ≠ 0 := by
  classical
  have hm : ∃ m ∈ p.support, m ≠ 0 := by
    by_contra! h
    exact (Nat.ne_of_gt hp) ((Finset.sup_eq_bot_iff _ _).mpr fun m hm => by rw [h m hm]; simp)
  obtain ⟨m, hm, hm₀⟩ := hm
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hm₀
  have hi₀ := Finsupp.mem_support_iff.mp hi
  let d := m - Finsupp.single i 1
  have hd : d + Finsupp.single i 1 = m := Finsupp.sub_add_single_one_cancel hi₀
  refine ⟨i, fun h => ?_⟩
  have hc : (MvPolynomial.pderiv i p).coeff d ≠ 0 := by
    rw [coeff_pderiv_shift, hd]
    exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hm)
      (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))
  exact hc (h ▸ MvPolynomial.coeff_zero _)

end Degrees

section Criterion

variable {k A ι : Type*} [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
  [Fintype ι] [DecidableEq ι]

/-- A nonzero determinant of derivatives certifies algebraic independence
over a characteristic-zero field. -/
theorem algebraicIndependent_of_jacobian_det_ne_zero (x : ι → A)
    (D : ι → Derivation k A A)
    (hJ : (Matrix.of fun i j => D i (x j)).det ≠ 0) : AlgebraicIndependent k x := by
  classical
  rw [algebraicIndependent_iff]
  intro q hq
  by_contra hq₀
  let e := MvPolynomial.aeval (R := k) x
  let P (n : ℕ) := ∃ p : MvPolynomial ι k, p.totalDegree = n ∧ e p = 0 ∧ p ≠ 0
  have hExists : ∃ n, P n := ⟨q.totalDegree, q, rfl, hq, hq₀⟩
  obtain ⟨p, hpDeg, hpEv, hp₀⟩ := Nat.find_spec hExists
  have hpPos : 0 < p.totalDegree := by
    by_contra! h
    have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp h)
    have hConst : algebraMap k A (p.coeff 0) = 0 := by
      conv_lhs at hpEv => rw [hc]
      simpa only [e, MvPolynomial.aeval_C] using hpEv
    exact hp₀ (hc.trans (by
      rw [(injective_iff_map_eq_zero (algebraMap k A)).mp
        (FaithfulSMul.algebraMap_injective k A) _ hConst, map_zero]))
  let J : Matrix ι ι A := Matrix.of fun i j => D i (x j)
  let y : ι → A := fun i => e (MvPolynomial.pderiv i p)
  have hJy : J *ᵥ y = 0 := by
    funext i
    change (∑ j, D i (x j) * e (MvPolynomial.pderiv j p)) = 0
    rw [← derivation_apply_mvPolynomial_aeval, hpEv, map_zero]
  have hy : J.det • y = 0 := by
    have h := congrArg (fun z => J.adjugate *ᵥ z) hJy
    change J.adjugate *ᵥ (J *ᵥ y) = J.adjugate *ᵥ 0 at h
    rwa [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec_assoc,
      Matrix.one_mulVec, Matrix.mulVec_zero] at h
  obtain ⟨i, hi⟩ := exists_pderiv_ne_zero p hpPos
  have hiEv : e (MvPolynomial.pderiv i p) = 0 :=
    (mul_eq_zero.mp (congrFun hy i)).resolve_left hJ
  exact Nat.find_min hExists ((pderiv_totalDegree_lt p i hpPos).trans_eq hpDeg)
    ⟨MvPolynomial.pderiv i p, rfl, hiEv, hi⟩

end Criterion

end WideE
