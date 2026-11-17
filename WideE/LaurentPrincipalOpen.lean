import WideE.AffinePatching
import WideE.GenericSection
import WideE.Laurent

/-! A generic section on the Laurent line is defined on its intersection
with an open neighborhood of zero in the affine line. -/

noncomputable section

namespace WideE

open LaurentPolynomial

variable {K : Type*} [Field K]

private theorem factor_at_zero {p : Polynomial K} (hp : p ≠ 0) :
    ∃ (n : ℕ) (q : Polynomial K), q.coeff 0 ≠ 0 ∧ p = Polynomial.X ^ n * q := by
  induction hDegree : p.natDegree using Nat.strong_induction_on generalizing p with
  | h m ih =>
    by_cases hz : p.coeff 0 = 0
    · obtain ⟨g, hg⟩ := Polynomial.X_dvd_iff.mpr hz
      have hg0 : g ≠ 0 := fun e => hp (by rw [hg, e, mul_zero])
      have hm : g.natDegree < m := by
        rw [← hDegree, hg, Polynomial.natDegree_X_mul hg0]
        exact Nat.lt_succ_self _
      obtain ⟨n, q, hq, he⟩ := ih g.natDegree hm hg0 rfl
      exact ⟨n + 1, q, hq, by rw [hg, he, pow_succ', mul_assoc]⟩
    · exact ⟨0, p, hz, by simp⟩

/-- A nonzero Laurent polynomial and a polynomial having nonzero constant
coefficient differ by a unit. -/
theorem laurent_associated_polynomial_not_vanishing_at_zero {p : LaurentPolynomial K} (hp : p ≠ 0) :
    ∃ q : Polynomial K, q.coeff 0 ≠ 0 ∧ Associated p q.toLaurent := by
  obtain ⟨m, f, hf⟩ := p.exists_T_pow
  have hf0 : f ≠ 0 := by
    intro e
    rw [e, map_zero] at hf
    exact (mul_ne_zero hp (isUnit_T (m : ℤ)).ne_zero) hf.symm
  obtain ⟨n, q, hq, he⟩ := factor_at_zero hf0
  have h : p * T (m : ℤ) = q.toLaurent * T (n : ℤ) := by
    rw [← hf, he, map_mul, Polynomial.toLaurent_X_pow, mul_comm]
  refine ⟨q, hq, ⟨(isUnit_T (R := K) ((m : ℤ) - (n : ℤ))).unit, ?_⟩⟩
  change p * ↑((isUnit_T (R := K) ((m : ℤ) - (n : ℤ))).unit) = q.toLaurent
  rw [IsUnit.unit_spec]
  calc
    _ = (p * T (m : ℤ)) * T (-(n : ℤ)) := by rw [mul_T_assoc, sub_eq_add_neg]
    _ = _ := by rw [h, mul_T_assoc, add_neg_cancel, T_zero, mul_one]

/-- The principal open receiving a generic point can be chosen to be the
intersection of the Laurent line with a principal open of the affine line
containing zero. -/
theorem exists_laurent_section_on_polynomial_open
    {F S : Type*} [Field F] [Algebra (LaurentPolynomial K) F]
    [IsFractionRing (LaurentPolynomial K) F] [CommRing S] [Algebra (LaurentPolynomial K) S]
    [Algebra.FiniteType (LaurentPolynomial K) S] (s : S →ₐ[LaurentPolynomial K] F) :
    ∃ q : Polynomial K, q.coeff 0 ≠ 0 ∧
      Nonempty (S →ₐ[LaurentPolynomial K] Localization.Away q.toLaurent) := by
  obtain ⟨p, hp, l, _⟩ := exists_principalOpen_section s
  obtain ⟨q, hq, hAssoc⟩ := laurent_associated_polynomial_not_vanishing_at_zero hp
  letI : IsLocalization.Away q.toLaurent (Localization.Away p) := IsLocalization.Away.of_associated hAssoc
  let e := IsLocalization.algEquiv (Submonoid.powers q.toLaurent) (Localization.Away p)
    (Localization.Away q.toLaurent)
  exact ⟨q, hq, ⟨e.toAlgHom.comp l⟩⟩

/-- Restriction from the polynomial principal open to its part on the Laurent line. -/
def polynomialOpenToLaurentOpen (p : Polynomial K) :
    Localization.Away p →ₐ[Polynomial K] Localization.Away p.toLaurent :=
  IsLocalization.liftAlgHom (M := Submonoid.powers p)
    (f := Algebra.ofId (Polynomial K) (Localization.Away p.toLaurent)) (by
      rintro ⟨g, n, rfl⟩
      change IsUnit (algebraMap (Polynomial K) (Localization.Away p.toLaurent) (p ^ n))
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away p.toLaurent) p.toLaurent).pow n)

/-- The overlap can be obtained from either principal open. -/
theorem polynomialOpen_localizationAtCoordinate (p : Polynomial K) :
    letI := (polynomialOpenToLaurentOpen p).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (Polynomial K) (Localization.Away p) Polynomial.X)
      (Localization.Away p.toLaurent) := by
  letI := (polynomialOpenToLaurentOpen p).toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom (polynomialOpenToLaurentOpen p)
  letI : IsLocalization.Away (algebraMap (Polynomial K) (LaurentPolynomial K) p)
      (Localization.Away p.toLaurent) := by
    change IsLocalization.Away p.toLaurent (Localization.Away p.toLaurent)
    infer_instance
  exact IsLocalization.Away.commutes (Localization.Away p) (LaurentPolynomial K)
    (Localization.Away p.toLaurent) p Polynomial.X

end WideE
