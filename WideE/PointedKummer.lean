import WideE.ComponentEtaleDescent
import WideE.KummerPointSpecialization
import WideE.PointedComplexKummer

/-! A pointed Kummer map for the finite étale quotient of an affine torsor. -/

noncomputable section

namespace WideE

/-- Finite étale covers of the algebraic Laurent line have Kummer maps
through every prescribed point above one. -/
theorem finiteLaurentCoverHasPointedKummerMap_algebraicComplex :
    FiniteLaurentCoverHasPointedKummerMap AlgebraicComplex :=
  finiteLaurentCoverHasPointedKummerMap_of_complex finiteLaurentCoverHasPointedKummerMap_complex

universe u

variable {k S H : Type u} [Field k] [IsAlgClosed k] [CommRing S] [CommRing H]
  [Algebra k S] [Algebra (LaurentPolynomial k) S] [IsScalarTower k (LaurentPolynomial k) S]
  [HopfAlgebra k H]

/-- The component quotient pulls back along a Kummer map compatible with the
chosen point of the original torsor above one. -/
theorem exists_pointed_kummerComponentMap_of_cover
    (hCover : FiniteLaurentCoverHasPointedKummerMap k)
    (T : AffineHopfTorsor k (LaurentPolynomial k) S H)
    (G : ComponentHopfPresentation k H) (p : S →ₐ[k] k)
    (hp : ∀ a, p (algebraMap (LaurentPolynomial k) S a) = evalAtOne k a) :
    ∃ q : ℕ, 0 < q ∧
      ∃ j : componentTorsorQuotient T G →ₐ[LaurentPolynomial k] KummerExtension k q,
        ∀ x, evalAtOne k (KummerExtension.toLaurent k q (j x)) = p (x : S) := by
  let Q := componentTorsorQuotient T G
  let e : Q →+* k := p.toRingHom.comp Q.val.toRingHom
  letI : Nontrivial Q := e.domain_nontrivial
  letI := componentTorsorQuotient_finite T G
  letI := componentTorsorQuotient_etale T G
  exact hCover Q e hp

end WideE
