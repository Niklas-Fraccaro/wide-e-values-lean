import NilpotentMatrixExpDerivative
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Exponentiating a nilpotent matrix tangent

If the coefficients of a matrix generate an affine algebra and its invariant
vector field has matrix `U N` with `N` nilpotent, the finite matrix exponential
of `t N` respects all relations of the generators. The resulting algebra map is
an actual point over the polynomial parameter ring.
-/

noncomputable section

open scoped Polynomial Matrix
open StrictEUnit

namespace WideE

section DerivationIntertwining

variable {k ι A : Type*} [Field k] [CommRing A] [Algebra k A]

private theorem derivation_intertwines_of_variables (δ : Derivation k (MvPolynomial ι k) (MvPolynomial ι k))
    (a : MvPolynomial ι k →ₐ[k] A) (D : Derivation k A A)
    (hX : ∀ i, a (δ (MvPolynomial.X i)) = D (a (MvPolynomial.X i))) (p : MvPolynomial ι k) :
    a (δ p) = D (a p) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.derivation_C, map_zero]
    change (0 : A) = D (a (algebraMap k (MvPolynomial ι k) r))
    rw [AlgHom.commutes, D.map_algebraMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [δ.leibniz, map_mul a, D.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, hp, hX]

private theorem polynomial_eq_zero_of_all_derivatives_at_zero [CharZero k]
    (p : k[X]) (h : ∀ n : ℕ, Polynomial.aeval (0 : k) (Polynomial.derivative^[n] p) = 0) : p = 0 := by
  apply Polynomial.ext
  intro n
  have h₀ := h n
  rw [← Polynomial.coeff_zero_eq_aeval_zero, Polynomial.coeff_iterate_derivative,
    zero_add, Nat.descFactorial_self, nsmul_eq_mul] at h₀
  exact (mul_eq_zero.mp h₀).resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

end DerivationIntertwining

section ExponentialMatrix

variable {k ι : Type*} [Field k] [CharZero k] [Fintype ι] [DecidableEq ι]

/-- The finite exponential of `t N` as a matrix of polynomials. -/
def polynomialMatrixExponential (N : Matrix ι ι k) : Matrix ι ι k[X] :=
  IsNilpotent.exp ((Polynomial.X : k[X]) • (algebraMap k k[X]).mapMatrix N)

omit [CharZero k] in
private theorem polynomialMatrixExponential_nilpotent_argument
    (N : Matrix ι ι k) (hN : IsNilpotent N) :
    IsNilpotent ((Polynomial.X : k[X]) • (algebraMap k k[X]).mapMatrix N) :=
  (hN.map (algebraMap k k[X]).mapMatrix).smul Polynomial.X

/-- Differentiation of the polynomial matrix exponential multiplies by the original tangent. -/
theorem polynomialMatrixExponential_derivative (N : Matrix ι ι k) (hN : IsNilpotent N) :
    matrixDerivative (Polynomial.derivative' (R := k)) (polynomialMatrixExponential N) =
      polynomialMatrixExponential N * (algebraMap k k[X]).mapMatrix N := by
  let M : Matrix ι ι k[X] := (algebraMap k k[X]).mapMatrix N
  have h := matrixDerivative_nilpotent_exp (Polynomial.derivative' (R := k)) Polynomial.X N hN
  change matrixDerivative (Polynomial.derivative' (R := k)) (polynomialMatrixExponential N) =
    Polynomial.derivative (Polynomial.X : k[X]) • (M * polynomialMatrixExponential N) at h
  rw [Polynomial.derivative_X, one_smul] at h
  rw [h]
  change Commute M (IsNilpotent.exp ((Polynomial.X : k[X]) • M))
  obtain ⟨m, hm⟩ := polynomialMatrixExponential_nilpotent_argument N hN
  change ((Polynomial.X : k[X]) • M) ^ m = 0 at hm
  rw [IsNilpotent.exp_eq_sum hm]
  exact Commute.sum_right _ _ _ fun i _ =>
    (((Commute.refl M).smul_right (Polynomial.X : k[X])).pow_right i).smul_right ((i.factorial : ℚ)⁻¹)

/-- Evaluation of the finite polynomial exponential gives the actual exponential of `t N`. -/
theorem polynomialMatrixExponential_eval (N : Matrix ι ι k) (hN : IsNilpotent N) (t : k) :
    (polynomialMatrixExponential N).map (Polynomial.aeval t) = IsNilpotent.exp (t • N) := by
  let q := Polynomial.aeval (R := k) t
  change q.toRingHom.mapMatrix (polynomialMatrixExponential N) = _
  rw [polynomialMatrixExponential,
    IsNilpotent.map_exp (polynomialMatrixExponential_nilpotent_argument N hN)]
  congr 1
  apply Matrix.ext
  intro i j
  change q (Polynomial.X * algebraMap k k[X] (N i j)) = t * N i j
  rw [map_mul, Polynomial.aeval_X, q.commutes]
  rfl

end ExponentialMatrix

section GroupPoint

variable {k H ι : Type*} [Field k] [CharZero k] [CommRing H] [Bialgebra k H]
variable [Fintype ι] [DecidableEq ι]

/-- The finite exponential is a polynomial-valued point when the generating
matrix carries the stated invariant derivation. Its specialization at zero is the counit. -/
theorem exists_hopfPolynomialPoint_matrixExponential (U : Matrix ι ι H)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U ij.1 ij.2) = ⊤)
    (hOne : U.map (Bialgebra.counitAlgHom k H) = 1)
    (D : Derivation k H H) (N : Matrix ι ι k) (hN : IsNilpotent N)
    (hD : matrixDerivative D U = U * (algebraMap k H).mapMatrix N) :
    ∃ q : H →ₐ[k] k[X], U.map q = polynomialMatrixExponential N ∧
      (Polynomial.aeval (0 : k)).comp q = Bialgebra.counitAlgHom k H := by
  let P := MvPolynomial (ι × ι) k
  let π : P →ₐ[k] H := MvPolynomial.aeval fun ij => U ij.1 ij.2
  let E := polynomialMatrixExponential N
  let a : P →ₐ[k] k[X] := MvPolynomial.aeval fun ij => E ij.1 ij.2
  let δ : Derivation k P P := MvPolynomial.mkDerivation k fun ij =>
    ∑ l, MvPolynomial.X (ij.1, l) * MvPolynomial.C (N l ij.2)
  have hπ : Function.Surjective π := by
    rw [← AlgHom.range_eq_top]
    exact (Algebra.adjoin_range_eq_range_aeval k _).symm.trans hGen
  have hInter : ∀ p : P, π (δ p) = D (π p) := by
    apply derivation_intertwines_of_variables
    rintro ⟨i, j⟩
    change π (MvPolynomial.mkDerivation k _ (MvPolynomial.X (i, j))) =
      D (MvPolynomial.aeval (fun ij : ι × ι => U ij.1 ij.2) (MvPolynomial.X (i, j)))
    rw [MvPolynomial.mkDerivation_X, MvPolynomial.aeval_X, map_sum]
    simp only [map_mul, show ∀ u : ι × ι, π (MvPolynomial.X u) = U u.1 u.2 from MvPolynomial.aeval_X _,
      show ∀ c : k, π (MvPolynomial.C c) = algebraMap k H c from π.commutes]
    exact (congrFun (congrFun hD i) j).symm
  have hExpInter : ∀ p : P, a (δ p) = Polynomial.derivative (a p) := by
    apply derivation_intertwines_of_variables δ a (Polynomial.derivative' (R := k))
    rintro ⟨i, j⟩
    change a (MvPolynomial.mkDerivation k _ (MvPolynomial.X (i, j))) =
      Polynomial.derivative (MvPolynomial.aeval (fun ij : ι × ι => E ij.1 ij.2)
        (MvPolynomial.X (i, j)))
    rw [MvPolynomial.mkDerivation_X, MvPolynomial.aeval_X, map_sum]
    simp only [map_mul, show ∀ u : ι × ι, a (MvPolynomial.X u) = E u.1 u.2 from MvPolynomial.aeval_X _,
      show ∀ c : k, a (MvPolynomial.C c) = algebraMap k k[X] c from a.commutes]
    exact (congrFun (congrFun (polynomialMatrixExponential_derivative N hN) i) j).symm
  have hInitial : (Polynomial.aeval (0 : k)).comp a = (Bialgebra.counitAlgHom k H).comp π := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    change (Polynomial.aeval (0 : k)) (a (MvPolynomial.X (i, j))) =
      Bialgebra.counitAlgHom k H (π (MvPolynomial.X (i, j)))
    rw [show a (MvPolynomial.X (i, j)) = E i j from MvPolynomial.aeval_X _ _,
      show π (MvPolynomial.X (i, j)) = U i j from MvPolynomial.aeval_X _ _]
    have hE : E.map (Polynomial.aeval (0 : k)) = 1 := by
      rw [polynomialMatrixExponential_eval N hN, zero_smul, IsNilpotent.exp_zero]
    exact (congrFun (congrFun hE i) j).trans (congrFun (congrFun hOne i) j).symm
  have hKer : RingHom.ker π.toRingHom ≤ RingHom.ker a.toRingHom := by
    intro p hp
    change π p = 0 at hp
    change a p = 0
    apply polynomial_eq_zero_of_all_derivatives_at_zero
    intro n
    have hπDer (n : ℕ) : π ((δ : P → P)^[n] p) = 0 := by
      induction n with
      | zero => exact hp
      | succ n ih =>
        rw [Function.iterate_succ_apply', show ∀ x, π ((δ : P → P) x) = D (π x) from hInter,
          ih, map_zero]
    have haDer (n : ℕ) : Polynomial.derivative^[n] (a p) = a ((δ : P → P)^[n] p) := by
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hExpInter]
    rw [haDer n]
    have hAt := DFunLike.congr_fun hInitial ((δ : P → P)^[n] p)
    change Polynomial.aeval (0 : k) (a ((δ : P → P)^[n] p)) =
      Bialgebra.counitAlgHom k H (π ((δ : P → P)^[n] p)) at hAt
    rw [hAt, hπDer n, map_zero]
  let e := Ideal.quotientKerAlgEquivOfSurjective hπ
  let a₀ : (P ⧸ RingHom.ker π.toRingHom) →ₐ[k] k[X] := Ideal.Quotient.liftₐ _ a hKer
  let q := a₀.comp e.symm.toAlgHom
  have hFactor (p : P) : q (π p) = a p := by
    have he : e (Ideal.Quotient.mk (RingHom.ker π.toRingHom) p) = π p := rfl
    change a₀ (e.symm (π p)) = a p
    rw [← he, e.symm_apply_apply]
    rfl
  refine ⟨q, ?_, ?_⟩
  · apply Matrix.ext
    intro i j
    have h := hFactor (MvPolynomial.X (i, j))
    change q (MvPolynomial.aeval (fun ij : ι × ι => U ij.1 ij.2) (MvPolynomial.X (i, j))) =
      MvPolynomial.aeval (fun ij : ι × ι => E ij.1 ij.2) (MvPolynomial.X (i, j)) at h
    simpa only [Matrix.map_apply, MvPolynomial.aeval_X] using h
  · apply AlgHom.ext
    intro x
    obtain ⟨p, rfl⟩ := hπ x
    change (Polynomial.aeval (0 : k)) (q (π p)) = Bialgebra.counitAlgHom k H (π p)
    rw [hFactor]
    exact DFunLike.congr_fun hInitial p

/-- Evaluation of the polynomial-valued point gives a group point over the base field. -/
theorem exists_hopfPoint_matrixExponential (U : Matrix ι ι H)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U ij.1 ij.2) = ⊤)
    (hOne : U.map (Bialgebra.counitAlgHom k H) = 1)
    (D : Derivation k H H) (N : Matrix ι ι k) (hN : IsNilpotent N)
    (hD : matrixDerivative D U = U * (algebraMap k H).mapMatrix N) (t : k) :
    ∃ p : H →ₐ[k] k, U.map p = IsNilpotent.exp (t • N) := by
  obtain ⟨q, hq, _⟩ := exists_hopfPolynomialPoint_matrixExponential U hGen hOne D N hN hD
  refine ⟨(Polynomial.aeval t).comp q, ?_⟩
  change (U.map q).map (Polynomial.aeval t) = _
  rw [hq, polynomialMatrixExponential_eval N hN]

end GroupPoint

end WideE
