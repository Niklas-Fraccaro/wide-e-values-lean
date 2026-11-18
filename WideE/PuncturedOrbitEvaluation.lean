import WideE.ProjectiveOrbitIdeal
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Etale.Basic

/-! Laurent coordinates for the nonzero vectors in a projective orbit. -/

noncomputable section

namespace WideE

variable {k H ι : Type*} [CommRing k] [CommRing H] [Algebra k H] [Fintype ι]

section Points

variable {A : Type*} [CommRing A] [Algebra k A]

/-- Evaluate both the coefficient algebra and the invertible Laurent coordinate. -/
def evalLaurentPoint (p : H →ₐ[k] A) (c : Aˣ) : LaurentPolynomial H →ₐ[k] A where
  __ := LaurentPolynomial.eval₂ p.toRingHom c
  commutes' a := by
    rw [LaurentPolynomial.algebraMap_apply]
    exact (LaurentPolynomial.eval₂_C _ _ _).trans (p.commutes a)

@[simp] theorem evalLaurentPoint_C (p : H →ₐ[k] A) (c : Aˣ) (a : H) :
    evalLaurentPoint p c (LaurentPolynomial.C a) = p a :=
  LaurentPolynomial.eval₂_C _ _ _

@[simp] theorem evalLaurentPoint_T_one (p : H →ₐ[k] A) (c : Aˣ) :
    evalLaurentPoint p c (LaurentPolynomial.T 1) = (c : A) :=
  (LaurentPolynomial.eval₂_T p.toRingHom c 1).trans (by rw [zpow_one])

end Points

private def polynomialToLaurent : Polynomial H →ₐ[k] LaurentPolynomial H where
  __ := Polynomial.toLaurent
  commutes' c := Polynomial.toLaurent_C (algebraMap k H c)

/-- Evaluate on the universal orbit vector multiplied by an invertible scalar. -/
def puncturedOrbitEvaluation (U : Matrix ι ι H) (v : ι → k) :
    MvPolynomial ι k →ₐ[k] LaurentPolynomial H :=
  polynomialToLaurent.comp (orbitConeEvaluation U v)

@[simp] theorem puncturedOrbitEvaluation_X (U : Matrix ι ι H) (v : ι → k) (i : ι) :
    puncturedOrbitEvaluation U v (MvPolynomial.X i) = LaurentPolynomial.C (orbitVector U v i) *
      LaurentPolynomial.T 1 := by
  rw [puncturedOrbitEvaluation, AlgHom.comp_apply, orbitConeEvaluation_X]
  change Polynomial.toLaurent (Polynomial.C (orbitVector U v i) * Polynomial.X) = _
  rw [map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X]

theorem puncturedOrbitEvaluation_ker (U : Matrix ι ι H) (v : ι → k) :
    RingHom.ker (puncturedOrbitEvaluation U v).toRingHom = orbitConeIdeal U v := by
  ext p
  change Polynomial.toLaurent (orbitConeEvaluation U v p) = 0 ↔ orbitConeEvaluation U v p = 0
  exact map_eq_zero_iff _ Polynomial.toLaurent_injective

/-- Laurent polynomials over a finite-type algebra are still of finite type. -/
theorem laurentPolynomial_finiteType [Algebra.FiniteType k H] :
    Algebra.FiniteType k (LaurentPolynomial H) := by
  letI : Algebra.Etale (Polynomial H) (LaurentPolynomial H) :=
    Algebra.Etale.of_isLocalization_Away (Polynomial.X : Polynomial H)
  letI : IsScalarTower H (Polynomial H) (LaurentPolynomial H) :=
    IsScalarTower.of_algebraMap_eq fun c => (Polynomial.toLaurent_C c).symm
  letI : Algebra.FiniteType H (LaurentPolynomial H) :=
    Algebra.FiniteType.trans (S := Polynomial H) inferInstance inferInstance
  exact Algebra.FiniteType.trans (S := H) inferInstance inferInstance

end WideE
