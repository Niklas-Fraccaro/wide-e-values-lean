import WideE.ConnectedEtaleDomain
import WideE.FiniteEtaleNormalization
import WideE.KummerIntermediateAlgebra
import WideE.KummerSections

/-! The connected finite étale Laurent covers over the algebraic numbers. -/

noncomputable section

namespace WideE

/-- A connected finite étale Laurent cover of the algebraic coefficient field
is the positive power cover of degree equal to its Laurent rank. -/
theorem exists_kummerEquiv_of_connected_finiteEtaleLaurent (A : Type) [CommRing A]
    [Algebra (LaurentPolynomial AlgebraicComplex) A] [ConnectedSpace (PrimeSpectrum A)]
    [Module.Finite (LaurentPolynomial AlgebraicComplex) A]
    [Algebra.Etale (LaurentPolynomial AlgebraicComplex) A] :
    ∃ q : ℕ, 0 < q ∧ q = Module.finrank (LaurentPolynomial AlgebraicComplex) A ∧
      Nonempty (A ≃ₐ[LaurentPolynomial AlgebraicComplex] KummerExtension AlgebraicComplex q) := by
  let K := AlgebraicComplex
  let R := LaurentPolynomial K
  letI : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ
  letI : IsDomain A := isDomain_of_connected_finiteEtaleLaurent (K := K) (A := A)
  letI : IsPrincipalIdealRing R := StrictEUnit.laurentPolynomial_isPrincipalIdealRing K
  letI : IsIntegrallyClosed A := isIntegrallyClosed_of_finite_unramified_pid R A
  letI : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  obtain ⟨q, hq, ⟨f⟩⟩ := finiteLaurentCoverHasKummerMap_algebraicComplex A
  obtain ⟨d, hd, _, ⟨e⟩⟩ := exists_kummerEquiv_of_integral_kummerMap hq f
  refine ⟨d, hd, ?_, ⟨e⟩⟩
  rw [Module.finrank_eq_card_basis ((KummerExtension.basis K d hd).map e.symm.toLinearEquiv),
    Fintype.card_fin]

end WideE
