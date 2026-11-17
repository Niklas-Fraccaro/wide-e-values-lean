import LaurentLogBase
import LaurentLogSimplicity
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Polynomial.Ideal

/-! Laurent polynomial algebra for the basis changes and specializations in §§4–5 and §7. -/

noncomputable section

namespace WideE
open LaurentPolynomial

section Evaluation

variable (K : Type*) [CommRing K]

/-- Specialization of the Laurent variable at one. -/
def evalAtOne : LaurentPolynomial K →+* K :=
  LaurentPolynomial.eval₂ (RingHom.id K) 1

@[simp] theorem evalAtOne_T (n : ℤ) : evalAtOne K (T n) = 1 := by
  simp [evalAtOne]

@[simp] theorem evalAtOne_C (a : K) : evalAtOne K (C a) = a := by
  simp [evalAtOne]

@[simp] theorem evalAtOne_toLaurent (p : Polynomial K) :
    evalAtOne K p.toLaurent = p.eval 1 := by
  simp [evalAtOne]

/-- The Kummer pullback sends the Laurent variable to its (q)th power. -/
def kummer (q : ℕ) : LaurentPolynomial K →+* LaurentPolynomial K :=
  AddMonoidAlgebra.mapDomainRingHom K (AddMonoidHom.mulLeft (q : ℤ))

@[simp] theorem kummer_T (q : ℕ) (n : ℤ) :
    kummer K q (T n) = T ((q : ℤ) * n) := by
  change Finsupp.mapDomain (fun m : ℤ => (q : ℤ) * m) (Finsupp.single n 1) = _
  rw [Finsupp.mapDomain_single]
  rfl

@[simp] theorem kummer_C (q : ℕ) (a : K) : kummer K q (C a) = C a := by
  change Finsupp.mapDomain (fun m : ℤ => (q : ℤ) * m) (Finsupp.single 0 a) = _
  rw [Finsupp.mapDomain_single, mul_zero]
  rfl

/-- The Kummer pullback fixes the coefficient algebra. -/
def kummerAlgHom (q : ℕ) : LaurentPolynomial K →ₐ[K] LaurentPolynomial K :=
  { kummer K q with commutes' := kummer_C K q }

@[simp] theorem kummerAlgHom_apply (q : ℕ) (p : LaurentPolynomial K) :
    kummerAlgHom K q p = kummer K q p :=
  rfl

theorem eval₂_comp_kummer {S : Type*} [CommRing S] (φ : K →+* S) (x : Sˣ) (q : ℕ) :
    (LaurentPolynomial.eval₂ φ x).comp (kummer K q) = LaurentPolynomial.eval₂ φ (x ^ q) := by
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply]
  induction p using LaurentPolynomial.induction_on' with
  | add p r hp hr => simp only [map_add, hp, hr]
  | C_mul_T n a =>
    simp only [RingHom.comp_apply, map_mul, kummer_C, kummer_T, eval₂_C, eval₂_T]
    rw [zpow_mul, zpow_natCast]

@[simp] theorem evalAtOne_kummer (q : ℕ) (p : LaurentPolynomial K) :
    evalAtOne K (kummer K q p) = evalAtOne K p := by
  change ((LaurentPolynomial.eval₂ (RingHom.id K) 1).comp (kummer K q)) p = _
  rw [eval₂_comp_kummer, one_pow]
  rfl

theorem evalAtOne_surjective : Function.Surjective (evalAtOne K) :=
  fun a => ⟨C a, evalAtOne_C K a⟩

/-- The ideal of the point (T=1). -/
def evaluationIdeal : Ideal (LaurentPolynomial K) :=
  Ideal.span {T 1 - 1}

theorem ker_evalAtOne : RingHom.ker (evalAtOne K) = evaluationIdeal K := by
  ext p
  rw [evaluationIdeal, RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hp
    obtain ⟨n, f, hf⟩ := LaurentPolynomial.exists_T_pow p
    have hf0 : f.IsRoot 1 := by
      have h := congrArg (evalAtOne K) hf
      simpa only [Polynomial.IsRoot, evalAtOne_toLaurent, map_mul, evalAtOne_T, mul_one, hp]
        using h
    obtain ⟨g, hg⟩ := Polynomial.dvd_iff_isRoot.mpr hf0
    refine ⟨g.toLaurent * T (-(n : ℤ)), ?_⟩
    calc
      p = p * T (n : ℤ) * T (-(n : ℤ)) := by
        rw [mul_T_assoc, add_neg_cancel, T_zero, mul_one]
      _ = (T 1 - 1) * (g.toLaurent * T (-(n : ℤ))) := by
        rw [← hf, hg, map_mul, map_sub, Polynomial.toLaurent_X, map_one,
          Polynomial.toLaurent_one, mul_assoc]
  · rintro ⟨p, rfl⟩
    simp

/-- The residue ring of the Laurent line at (1) is the coefficient ring. -/
def evaluationQuotientEquiv : (LaurentPolynomial K ⧸ evaluationIdeal K) ≃+* K :=
  (Ideal.quotEquivOfEq (ker_evalAtOne K).symm).trans
    (RingHom.quotientKerEquivOfRightInverse (evalAtOne_C K))

@[simp] theorem evaluationQuotientEquiv_mk (p : LaurentPolynomial K) :
    evaluationQuotientEquiv K (Ideal.Quotient.mk (evaluationIdeal K) p) = evalAtOne K p :=
  rfl

end Evaluation

section Units

variable {K : Type*} [CommRing K] [IsDomain K]

/-- The units in the Laurent ring are the Laurent monomials with invertible coefficient. -/
theorem laurent_isUnit_iff (p : LaurentPolynomial K) :
    IsUnit p ↔ ∃ (a : K) (n : ℤ), IsUnit a ∧ p = C a * T n := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨m, f, hf⟩ := LaurentPolynomial.exists_T_pow (u : LaurentPolynomial K)
    obtain ⟨n, g, hg⟩ := LaurentPolynomial.exists_T_pow (↑u⁻¹ : LaurentPolynomial K)
    have hfg : f * g = Polynomial.X ^ (m + n) := by
      apply Polynomial.toLaurent_injective
      rw [map_mul, hf, hg, Polynomial.toLaurent_X_pow, Nat.cast_add, T_add]
      calc
        ((u : LaurentPolynomial K) * T (m : ℤ)) * (↑u⁻¹ * T (n : ℤ)) =
          ((u : LaurentPolynomial K) * ↑u⁻¹) * (T (m : ℤ) * T (n : ℤ)) := by ac_rfl
        _ = _ := by rw [Units.mul_inv, one_mul]
    obtain ⟨i, _, hassoc⟩ := (dvd_prime_pow Polynomial.prime_X (m + n)).mp ⟨g, hfg.symm⟩
    obtain ⟨v, hv⟩ := hassoc.symm
    obtain ⟨a, ha, ha'⟩ := Polynomial.isUnit_iff.mp v.isUnit
    refine ⟨a, (i : ℤ) - (m : ℤ), ha, ?_⟩
    calc
      (u : LaurentPolynomial K) = ↑u * T (m : ℤ) * T (-(m : ℤ)) := by
        rw [mul_T_assoc, add_neg_cancel, T_zero, mul_one]
      _ = C a * T ((i : ℤ) - (m : ℤ)) := by
        rw [← hf, ← hv, ← ha', map_mul, Polynomial.toLaurent_X_pow, Polynomial.toLaurent_C,
          mul_comm (T (i : ℤ)), mul_T_assoc, ← sub_eq_add_neg]
  · rintro ⟨a, n, ha, rfl⟩
    exact (ha.map C).mul (isUnit_T n)

end Units

section Differential

variable {K : Type*} [CommRing K]

private def laurentEulerLinear : LaurentPolynomial K →ₗ[K] LaurentPolynomial K where
  toFun p := Finsupp.onFinset p.support (fun n : ℤ => (n : K) * p n) (by
    intro n hn
    exact Finsupp.mem_support_iff.mpr (fun hp => hn (by simp [hp])))
  map_add' p q := by
    ext n
    exact mul_add _ _ _
  map_smul' r p := by
    ext n
    change (n : K) * (r * p n) = r * ((n : K) * p n)
    exact mul_left_comm _ _ _

private theorem laurentEulerLinear_monomial (n : ℤ) (a : K) :
    laurentEulerLinear (C a * T n : LaurentPolynomial K) = C ((n : K) * a) * T n := by
  simp only [← single_eq_C_mul_T]
  ext m
  change (m : K) * Finsupp.single n a m = Finsupp.single n ((n : K) * a) m
  by_cases h : n = m
  · subst m
    simp only [Finsupp.single_eq_same]
  · simp only [Finsupp.single_apply, if_neg h, mul_zero]

/-- The Euler derivation multiplies each coefficient by its Laurent exponent. -/
def laurentEulerDerivation :
    Derivation K (LaurentPolynomial K) (LaurentPolynomial K) :=
  Derivation.mk' laurentEulerLinear (by
    intro p q
    change laurentEulerLinear (p * q) =
      p * laurentEulerLinear q + q * laurentEulerLinear p
    induction p using LaurentPolynomial.induction_on' with
    | add p r hp hr =>
      simp only [add_mul, mul_add, map_add, hp, hr]
      abel
    | C_mul_T n a =>
      induction q using LaurentPolynomial.induction_on' with
      | add p q hp hq =>
        simp only [add_mul, mul_add, map_add, hp, hq]
        abel
      | C_mul_T m b =>
        have hm (ι κ : ℤ) (c d : K) :
            (C c * T ι) * (C d * T κ) = C (c * d) * T (ι + κ) := by
          rw [map_mul, T_add]
          ac_rfl
        rw [hm, laurentEulerLinear_monomial, laurentEulerLinear_monomial,
          laurentEulerLinear_monomial, hm, hm, add_comm m n, ← add_mul, ← map_add]
        congr 2
        push_cast
        ring)

@[simp] theorem laurentEulerDerivation_coeff (p : LaurentPolynomial K) (n : ℤ) :
    laurentEulerDerivation p n = (n : K) * p n :=
  rfl

private theorem laurentEulerDerivation_monomial (n : ℤ) (a : K) :
    laurentEulerDerivation (C a * T n : LaurentPolynomial K) = C ((n : K) * a) * T n :=
  laurentEulerLinear_monomial n a

/-- The ordinary derivation on (K[T,T^{-1}]). -/
def laurentDerivation : Derivation K (LaurentPolynomial K) (LaurentPolynomial K) :=
  (T (-1) : LaurentPolynomial K) • laurentEulerDerivation

@[simp] theorem laurentDerivation_monomial (n : ℤ) (a : K) :
    laurentDerivation (C a * T n : LaurentPolynomial K) = C ((n : K) * a) * T (n - 1) := by
  change T (-1) * laurentEulerDerivation (C a * T n) = _
  rw [laurentEulerDerivation_monomial, mul_comm, mul_T_assoc, sub_eq_add_neg]

@[simp] theorem laurentDerivation_T (n : ℤ) :
    laurentDerivation (T n : LaurentPolynomial K) = C (n : K) * T (n - 1) := by
  simpa only [map_one, one_mul, mul_one] using laurentDerivation_monomial n (1 : K)

@[simp] theorem laurentDerivation_C (a : K) :
    laurentDerivation (C a : LaurentPolynomial K) = 0 := by
  simpa only [T_zero, mul_one, Int.cast_zero, zero_mul, map_zero, zero_mul]
    using laurentDerivation_monomial 0 a

@[simp] theorem laurentDerivation_toLaurent (p : Polynomial K) :
    laurentDerivation p.toLaurent = p.derivative.toLaurent := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    cases n with
    | zero => simp [Polynomial.monomial_zero_left]
    | succ n =>
      rw [Polynomial.derivative_monomial_succ, ← Polynomial.C_mul_X_pow_eq_monomial,
        ← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [Polynomial.toLaurent_C_mul_X_pow, laurentDerivation_monomial,
        Int.natCast_succ, Int.cast_add, Int.cast_natCast, Int.cast_one, add_sub_cancel_right]
      rw [mul_comm (a : K) (_ + _)]

/-- The chain rule for a Laurent polynomial under a homomorphism of coefficient algebras. -/
theorem laurentDerivation_chain {S : Type*} [CommRing S] [Algebra K S]
    (φ : LaurentPolynomial K →ₐ[K] S) (δ : Derivation K S S) (p : LaurentPolynomial K) :
    δ (φ p) = δ (φ (T 1)) * φ (laurentDerivation p) := by
  let P (f : LaurentPolynomial K) :=
    δ (φ f) = δ (φ (T 1)) * φ (laurentDerivation f)
  have hD1 : laurentDerivation (T 1 : LaurentPolynomial K) = 1 := by simp
  have h_one : P (T 1) := by simp [P, hD1]
  have h_negOne : P (T (-1)) := by
    have h : (T (-1) : LaurentPolynomial K) * T 1 = 1 := by
      rw [← T_add, neg_add_cancel, T_zero]
    have hφ : φ (T (-1)) * φ (T 1) = 1 := by
      simpa only [map_mul, map_one] using congrArg φ h
    change δ (φ (T (-1))) = _
    rw [δ.leibniz_of_mul_eq_one hφ, laurentDerivation.leibniz_of_mul_eq_one h, hD1]
    simp only [smul_eq_mul, mul_one, map_neg, map_pow]
    ac_rfl
  have h_mul {f g : LaurentPolynomial K} (hf : P f) (hg : P g) : P (f * g) := by
    change δ (φ f) = _ at hf
    change δ (φ g) = _ at hg
    simp only [P, map_mul, Derivation.leibniz, smul_eq_mul, map_add, mul_add, hf, hg]
    ac_rfl
  apply LaurentPolynomial.induction_on (M := P) p
  · intro a
    change δ (φ (C a)) = _
    rw [laurentDerivation_C, map_zero, mul_zero, LaurentPolynomial.C_eq_algebraMap,
      AlgHom.commutes, δ.map_algebraMap]
  · intro f g hf hg
    change δ (φ f) = _ at hf
    change δ (φ g) = _ at hg
    simp only [P, map_add, mul_add, hf, hg]
  · intro n a ih
    rw [T_add, ← mul_assoc]
    exact h_mul ih h_one
  · intro n a ih
    rw [T_sub, ← mul_assoc]
    exact h_mul ih h_negOne

/-- Change of independent variable by the power map. -/
theorem laurentDerivation_kummer (q : ℕ) (p : LaurentPolynomial K) :
    laurentDerivation (kummer K q p) =
      C (q : K) * T ((q : ℤ) - 1) * kummer K q (laurentDerivation p) := by
  rw [← kummerAlgHom_apply, laurentDerivation_chain]
  simp only [kummerAlgHom_apply, kummer_T, mul_one, laurentDerivation_T, Int.cast_natCast]

end Differential

section CharacteristicZero

variable {K : Type*} [Field K] [CharZero K]

/-- The constants of the Laurent differential ring are exactly the coefficient field. -/
theorem laurentDerivation_eq_zero_iff (p : LaurentPolynomial K) :
    laurentDerivation p = 0 ↔ ∃ a : K, p = C a := by
  constructor
  · intro h
    have hEuler : laurentEulerDerivation p = 0 := by
      change T (-1) * laurentEulerDerivation p = 0 at h
      have h := congrArg (fun f : LaurentPolynomial K => T 1 * f) h
      simpa only [← mul_assoc, ← T_add, add_neg_cancel, T_zero, one_mul, mul_zero] using h
    refine ⟨p 0, Finsupp.support_subset_singleton.mp ?_⟩
    intro n hn
    apply Finset.mem_singleton.mpr
    by_contra hn0
    have hcoeff := congrArg (fun f : LaurentPolynomial K => f n) hEuler
    change laurentEulerDerivation p n = 0 at hcoeff
    rw [laurentEulerDerivation_coeff, mul_eq_zero] at hcoeff
    exact hcoeff.elim (fun hc => hn0 (Int.cast_eq_zero.mp hc))
      (Finsupp.mem_support_iff.mp hn)
  · rintro ⟨a, rfl⟩
    exact laurentDerivation_C a

/-- There are no proper nonzero differential ideals in the Laurent differential ring. -/
theorem laurentDerivation_stable_ideal_eq_top (I : Ideal (LaurentPolynomial K))
    (hI : ∀ p ∈ I, laurentDerivation p ∈ I) (hI0 : I ≠ ⊥) : I = ⊤ := by
  obtain ⟨p, hpI, hp0⟩ := (Submodule.ne_bot_iff I).mp hI0
  obtain ⟨n, f, hf⟩ := LaurentPolynomial.exists_T_pow p
  have hfI : f.toLaurent ∈ I := by
    rw [hf, mul_comm]
    exact I.mul_mem_left _ hpI
  have hf0 : f ≠ 0 := by
    intro h
    rw [h, map_zero] at hf
    exact hp0 ((mul_eq_zero.mp hf.symm).resolve_right (isUnit_T (n : ℤ)).ne_zero)
  have hiter (j : ℕ) : ((Polynomial.derivative^[j]) f).toLaurent ∈ I := by
    induction j with
    | zero => exact hfI
    | succ j ih =>
      rw [Function.iterate_succ_apply', ← laurentDerivation_toLaurent]
      exact hI _ ih
  obtain ⟨a, ha0, ha⟩ := StrictEUnit.polynomial_top_derivative_constant f hf0
  have haI := hiter f.natDegree
  rw [ha, Polynomial.toLaurent_C] at haI
  exact I.eq_top_of_isUnit_mem haI ((isUnit_iff_ne_zero.mpr ha0).map C)

end CharacteristicZero

end WideE
