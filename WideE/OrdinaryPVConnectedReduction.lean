import WideE.ResidualConnectedReduction
import WideE.HopfSmoothness
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The finite component quotient and residual torsor of the ordinary PV algebra. -/

noncomputable section

open scoped WideE

namespace WideE

attribute [local instance 2000] Subalgebra.toCommRing

universe u

section Ordinary

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {r : ℕ}
  (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))

local instance ordinaryConnectedPVCommRing : CommRing (ordinaryPVAlgebra A) := (ordinaryPVAlgebra A).toCommRing
local instance ordinaryConnectedPVLaurentAlgebra : Algebra (LaurentPolynomial K) (ordinaryPVAlgebra A) := (ordinaryPVAlgebra A).algebra
local instance ordinaryConnectedPVCoefficientAlgebra : Algebra K (ordinaryPVAlgebra A) := (ordinaryPVAlgebra A).algebra'

/-- The ordinary Picard–Vessiot torsor has a finite étale component quotient
and a residual torsor under a smooth connected constant group. -/
theorem ordinaryPV_connectedTorsorReduction :
    Nonempty (ConnectedTorsorReduction K (ordinaryPVAlgebra A)) := by
  letI := ordinaryPVHopf A
  letI := ordinaryPVGroup_smooth A
  obtain ⟨G⟩ := ordinaryPV_componentHopf A
  exact ⟨connectedTorsorReduction_of_affine (ordinaryPVTorsor A) G⟩

end Ordinary

/-- Only a map from each finite quotient to a Kummer coordinate algebra is
needed when the residual torsor has a global section. -/
theorem widePVKummerSectionExistence_of_kummerMap
    (hCover : FiniteLaurentCoverHasKummerMap AlgebraicComplex)
    (hPianzola : PianzolaForKummerAlgebras AlgebraicComplex) :
    WidePVKummerSectionExistence := by
  intro r A
  letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  letI := ordinaryConnectedPVCommRing A
  letI := ordinaryConnectedPVCoefficientAlgebra A
  letI := ordinaryConnectedPVLaurentAlgebra A
  obtain ⟨data⟩ := ordinaryPV_connectedTorsorReduction A
  exact data.exists_section_of_kummerMap hCover hPianzola

/-- The affine group quotients in the geometric Kummer reduction are the
ones obtained from the actual ordinary Picard–Vessiot construction. -/
theorem widePVKummerSectionExistence_of_connectedGeometry
    (hCover : ConnectedLaurentCoverIsKummer AlgebraicComplex)
    (hPianzola : PianzolaForKummerAlgebras AlgebraicComplex) :
    WidePVKummerSectionExistence :=
  widePVKummerSectionExistence_of_kummerMap hCover.hasKummerMap hPianzola

end WideE
