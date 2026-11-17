import WideE.ComponentPullback
import WideE.LaurentPrincipalOpen
import PointedTorsor

/-! A section gives an actual constant-group chart, including after taking
the principal open used in the affine-line extension. -/

open scoped TensorProduct

noncomputable section

namespace WideE

open StrictEUnit

variable {K B A S H : Type*}
  [CommRing K] [CommRing B] [CommRing A] [CommRing S] [CommRing H]
  [Algebra K B] [Algebra K A] [Algebra K S] [Algebra K H]
  [Algebra B A] [Algebra B S] [IsScalarTower K B A] [IsScalarTower K B S]

/-- The chart produced by a point on the indicated base change of the torsor. -/
def torsorChartOfSection (e : S ⊗[K] H ≃ₐ[S] S ⊗[B] S) (s : S →ₐ[B] A) :
    A ⊗[B] S ≃ₐ[A] A ⊗[K] H := by
  let chart := componentTorsorChart (A := A) e
  let point := (componentSections B A S).symm s
  exact pointedTorsorEquiv (inverseMultiplicationCoaction chart) point
    (relativeCandidateCanonical_bijective (k := A) chart)

omit [CommRing K] [CommRing B] [CommRing A] [CommRing S] [CommRing H]
  [Algebra K B] [Algebra K A] [Algebra K S] [Algebra K H]
  [Algebra B A] [Algebra B S] [IsScalarTower K B A] [IsScalarTower K B S] in
/-- A generic point of the Laurent torsor trivializes it over the overlap
with one principal open of the affine line containing zero. -/
theorem laurentTorsor_trivialization_on_polynomial_open
    {k F S H : Type*} [Field k] [Field F] [CommRing S] [CommRing H]
    [Algebra k H] [Algebra k S] [Algebra (LaurentPolynomial k) S]
    [IsScalarTower k (LaurentPolynomial k) S]
    [Algebra (LaurentPolynomial k) F] [IsFractionRing (LaurentPolynomial k) F]
    [Algebra.FiniteType (LaurentPolynomial k) S]
    (chart : S ⊗[k] H ≃ₐ[S] S ⊗[LaurentPolynomial k] S)
    (genericPoint : S →ₐ[LaurentPolynomial k] F) :
    ∃ p : Polynomial k, p.coeff 0 ≠ 0 ∧ Nonempty
      (Localization.Away p.toLaurent ⊗[LaurentPolynomial k] S ≃ₐ[Localization.Away p.toLaurent]
        Localization.Away p.toLaurent ⊗[k] H) := by
  obtain ⟨p, hp, ⟨sectionMap⟩⟩ := exists_laurent_section_on_polynomial_open genericPoint
  exact ⟨p, hp, ⟨torsorChartOfSection chart sectionMap⟩⟩

end WideE
