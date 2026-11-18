import WideE.ComplexEtaleCover
import WideE.EtaleFiniteFree

/-! Kummer points over a prescribed point of a finite étale complex cover. -/

noncomputable section

namespace WideE

/-- A point above one of a finite étale complex Laurent algebra extends to
a Laurent-algebra map into a positive Kummer cover. -/
theorem finiteLaurentCoverHasPointedKummerMap_complex
    (A : Type) [CommRing A] [Nontrivial A] [Algebra (LaurentPolynomial ℂ) A]
    [Module.Finite (LaurentPolynomial ℂ) A] [Algebra.Etale (LaurentPolynomial ℂ) A]
    (e : A →+* ℂ)
    (he : ∀ r : LaurentPolynomial ℂ, e (algebraMap (LaurentPolynomial ℂ) A r) = evalAtOne ℂ r) :
    ∃ q : ℕ, 0 < q ∧ ∃ f : A →ₐ[LaurentPolynomial ℂ] KummerExtension ℂ q,
      ∀ a : A, evalAtOne ℂ (KummerExtension.toLaurent ℂ q (f a)) = e a := by
  letI : Algebra ℂ A := ((algebraMap (LaurentPolynomial ℂ) A).comp
    (algebraMap ℂ (LaurentPolynomial ℂ))).toAlgebra
  letI : IsScalarTower ℂ (LaurentPolynomial ℂ) A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let eAlg : A →ₐ[ℂ] ℂ :=
    { e with commutes' := fun c => (he (LaurentPolynomial.C c)).trans (evalAtOne_C ℂ c) }
  let x : ComplexLaurentPoints A := ⟨puncturedOne, ⟨eAlg, by
    apply AlgHom.ext
    intro r
    change e (algebraMap (LaurentPolynomial ℂ) A r) = complexLaurentFunctions r puncturedOne
    rw [he, complexLaurentFunctions_puncturedOne]⟩⟩
  let b := finiteEtaleLaurentBasis (K := ℂ) (A := A)
  exact ComplexLaurentPoints.exists_pointed_kummerPoint b.2 x rfl

end WideE
