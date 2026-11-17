import WideE.ComplexEtaleCover
import WideE.EtaleFiniteFree
import WideE.KummerPointSpecialization
import WideE.OrdinaryPVConnectedReduction

/-! The Kummer base change required by the global section argument, and the
classification reduced to Pianzola's connected-group theorem. -/

noncomputable section

namespace WideE

/-- The finite étale quotient admits a complex point after a Kummer cover. -/
theorem finiteLaurentCoverHasKummerMap_complex : FiniteLaurentCoverHasKummerMap ℂ := by
  intro A _ _ _ _ _
  letI : Algebra ℂ A := ((algebraMap (LaurentPolynomial ℂ) A).comp
    (algebraMap ℂ (LaurentPolynomial ℂ))).toAlgebra
  letI : IsScalarTower ℂ (LaurentPolynomial ℂ) A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let b := finiteEtaleLaurentBasis (K := ℂ) (A := A)
  exact ComplexLaurentPoints.exists_kummerPoint b.2

/-- The Kummer point can be taken over the original algebraic coefficient field. -/
theorem finiteLaurentCoverHasKummerMap_algebraicComplex :
    FiniteLaurentCoverHasKummerMap AlgebraicComplex :=
  finiteLaurentCoverHasKummerMap_of_complex finiteLaurentCoverHasKummerMap_complex

theorem widePVKummerSectionExistence_of_pianzola
    (hPianzola : PianzolaForKummerAlgebras AlgebraicComplex) : WidePVKummerSectionExistence :=
  widePVKummerSectionExistence_of_kummerMap finiteLaurentCoverHasKummerMap_algebraicComplex hPianzola

theorem wideEValueUnit_iff_algebraicScalarExp_of_pianzola
    (hPianzola : PianzolaForKummerAlgebras AlgebraicComplex) (ξ : ℂ) :
    IsWideEValueUnit ξ ↔ IsAlgebraicScalarExp ξ :=
  wideEValueUnit_iff_algebraicScalarExp_of_sections (widePVKummerSectionExistence_of_pianzola hPianzola) ξ

theorem isUnit_valueSubring_iff_algebraicScalarExp_of_pianzola
    (hPianzola : PianzolaForKummerAlgebras AlgebraicComplex) (u : valueSubring) :
    IsUnit u ↔ IsAlgebraicScalarExp (u : ℂ) :=
  isUnit_valueSubring_iff_algebraicScalarExp_of_sections
    (widePVKummerSectionExistence_of_pianzola hPianzola) u

end WideE
