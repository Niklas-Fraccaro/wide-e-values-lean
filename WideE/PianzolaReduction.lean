import WideE.Classification
import WideE.TorsorBaseChange
import WideE.TorsorReduction
import Mathlib.RingTheory.Smooth.Basic

/-! The residual torsor on a Kummer component keeps the original connected
constant group, so its section can be composed with the map to the original
torsor. -/

open scoped WideE

noncomputable section

namespace WideE

universe u

/-- The affine form of Pianzola's connected-group theorem on the Laurent
algebras occurring as Kummer covers. -/
def PianzolaForKummerAlgebras (K : Type u) [Field K] : Prop :=
  ∀ (q : ℕ), 0 < q →
    ∀ (H : Type u) [CommRing H] [Algebra K H] [HopfAlgebra K H]
      [Algebra.Smooth K H] [ConnectedSpace (PrimeSpectrum H)]
      (S : Type u) [CommRing S] [Algebra K S] [Algebra (KummerExtension K q) S]
      [IsScalarTower K (KummerExtension K q) S],
      AffineHopfTorsor K (KummerExtension K q) S H →
        Nonempty (S →ₐ[KummerExtension K q] KummerExtension K q)

section Residual

variable {K Q S H : Type u} [Field K] [CommRing Q] [Nontrivial Q] [CommRing S] [CommRing H]
  [Algebra K Q] [Algebra K S] [Algebra K H] [HopfAlgebra K H]
  [Algebra (LaurentPolynomial K) Q] [Algebra (LaurentPolynomial K) S] [Algebra Q S]
  [IsScalarTower K (LaurentPolynomial K) Q] [IsScalarTower K Q S]
  [IsScalarTower (LaurentPolynomial K) Q S]

/-- Apply the connected-group theorem to a component of the finite quotient.
The output is a section over the original Laurent ring and the same Kummer cover. -/
theorem exists_kummerSection_of_pianzola_map [Algebra.Smooth K H] [ConnectedSpace (PrimeSpectrum H)]
    [Module.Finite (LaurentPolynomial K) Q] [Algebra.Etale (LaurentPolynomial K) Q]
    (hCover : FiniteLaurentCoverHasKummerMap K) (hPianzola : PianzolaForKummerAlgebras K)
    (residual : AffineHopfTorsor K Q S H) :
    ∃ q : ℕ, 0 < q ∧ Nonempty (S →ₐ[LaurentPolynomial K] KummerExtension K q) := by
  apply exists_kummerSection_of_finiteEtale_quotient_map (Q := Q) hCover
  intro q hq j
  letI := j.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom (j.restrictScalars K)
  exact hPianzola q hq H (KummerComponentPullback j S) (residual.kummerComponent j)

theorem exists_kummerSection_of_pianzola [Algebra.Smooth K H] [ConnectedSpace (PrimeSpectrum H)]
    [Module.Finite (LaurentPolynomial K) Q] [Algebra.Etale (LaurentPolynomial K) Q]
    (hCover : ConnectedLaurentCoverIsKummer K) (hPianzola : PianzolaForKummerAlgebras K)
    (residual : AffineHopfTorsor K Q S H) :
    ∃ q : ℕ, 0 < q ∧ Nonempty (S →ₐ[LaurentPolynomial K] KummerExtension K q) :=
  exists_kummerSection_of_pianzola_map hCover.hasKummerMap hPianzola residual

end Residual

/-- The finite quotient and the torsor under the smooth connected constant
group over that quotient. -/
structure ConnectedTorsorReduction (K S : Type u) [Field K] [CommRing S]
    [Algebra K S] [Algebra (LaurentPolynomial K) S] where
  quotient : Type u
  [quotientRing : CommRing quotient]
  [quotientNontrivial : Nontrivial quotient]
  [quotientCoefficients : Algebra K quotient]
  [quotientLaurent : Algebra (LaurentPolynomial K) quotient]
  [quotientTower : IsScalarTower K (LaurentPolynomial K) quotient]
  [quotientFinite : Module.Finite (LaurentPolynomial K) quotient]
  [quotientEtale : Algebra.Etale (LaurentPolynomial K) quotient]
  [quotientToTorsor : Algebra quotient S]
  [torsorCoefficientTower : IsScalarTower K quotient S]
  [torsorLaurentTower : IsScalarTower (LaurentPolynomial K) quotient S]
  group : Type u
  [groupRing : CommRing group]
  [groupCoefficients : Algebra K group]
  [groupHopf : HopfAlgebra K group]
  [groupSmooth : Algebra.Smooth K group]
  [groupConnected : ConnectedSpace (PrimeSpectrum group)]
  residual : AffineHopfTorsor K quotient S group

theorem ConnectedTorsorReduction.exists_section_of_kummerMap {K S : Type u} [Field K] [CommRing S]
    [Algebra K S] [Algebra (LaurentPolynomial K) S] (data : ConnectedTorsorReduction K S)
    (hCover : FiniteLaurentCoverHasKummerMap K) (hPianzola : PianzolaForKummerAlgebras K) :
    ∃ q : ℕ, 0 < q ∧ Nonempty (S →ₐ[LaurentPolynomial K] KummerExtension K q) := by
  letI := data.quotientRing
  letI := data.quotientNontrivial
  letI := data.quotientCoefficients
  letI := data.quotientLaurent
  letI := data.quotientTower
  letI := data.quotientFinite
  letI := data.quotientEtale
  letI := data.quotientToTorsor
  letI := data.torsorCoefficientTower
  letI := data.torsorLaurentTower
  letI := data.groupRing
  letI := data.groupCoefficients
  letI := data.groupHopf
  letI := data.groupSmooth
  letI := data.groupConnected
  exact exists_kummerSection_of_pianzola_map hCover hPianzola data.residual

theorem ConnectedTorsorReduction.exists_section {K S : Type u} [Field K] [CommRing S]
    [Algebra K S] [Algebra (LaurentPolynomial K) S] (data : ConnectedTorsorReduction K S)
    (hCover : ConnectedLaurentCoverIsKummer K) (hPianzola : PianzolaForKummerAlgebras K) :
    ∃ q : ℕ, 0 < q ∧ Nonempty (S →ₐ[LaurentPolynomial K] KummerExtension K q) :=
  data.exists_section_of_kummerMap hCover.hasKummerMap hPianzola

set_option synthInstance.maxHeartbeats 120000 in
/-- Supply the global section theorem from the three geometric steps of §7. -/
theorem widePVKummerSectionExistence_of_geometry
    (hCover : ConnectedLaurentCoverIsKummer AlgebraicComplex)
    (hPianzola : PianzolaForKummerAlgebras AlgebraicComplex)
    (hQuotient : ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) (LaurentPolynomial AlgebraicComplex)),
      Nonempty (ConnectedTorsorReduction AlgebraicComplex (ordinaryPVAlgebra A))) :
    WidePVKummerSectionExistence := by
  intro r A
  obtain ⟨data⟩ := hQuotient r A
  exact data.exists_section hCover hPianzola

end WideE
