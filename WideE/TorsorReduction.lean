import WideE.ComponentPullback
import WideE.FiniteEtaleComponent

/-! Reduction of the section problem to the connected group after choosing
one connected component of an actual finite étale quotient. -/

noncomputable section

namespace WideE

universe u

/-- The geometric classification of connected covers used in §7.1. -/
def ConnectedLaurentCoverIsKummer (K : Type u) [Field K] : Prop :=
  ∀ (Q : Type u) [CommRing Q] [Algebra (LaurentPolynomial K) Q]
    [Module.Finite (LaurentPolynomial K) Q] [Algebra.Etale (LaurentPolynomial K) Q]
    [ConnectedSpace (PrimeSpectrum Q)],
    ∃ q : ℕ, 0 < q ∧ Nonempty (Q ≃ₐ[LaurentPolynomial K] KummerExtension K q)

/-- The existence of a map from a Kummer cover to a nonempty finite étale cover
is sufficient for pulling back a section. -/
def FiniteLaurentCoverHasKummerMap (K : Type u) [Field K] : Prop :=
  ∀ (Q : Type u) [CommRing Q] [Nontrivial Q] [Algebra (LaurentPolynomial K) Q]
    [Module.Finite (LaurentPolynomial K) Q] [Algebra.Etale (LaurentPolynomial K) Q],
    ∃ q : ℕ, 0 < q ∧ Nonempty (Q →ₐ[LaurentPolynomial K] KummerExtension K q)

theorem ConnectedLaurentCoverIsKummer.hasKummerMap {K : Type u} [Field K]
    (hCover : ConnectedLaurentCoverIsKummer K) : FiniteLaurentCoverHasKummerMap K := by
  intro Q _ _ _ _ _
  obtain ⟨x⟩ := (inferInstance : Nonempty (PrimeSpectrum Q))
  obtain ⟨e, _, _, hConn, hFin, hEtale⟩ :=
    exists_finite_etale_quotientComponent (R := LaurentPolynomial K) x
  letI := hConn
  letI := hFin
  letI := hEtale
  obtain ⟨q, hq, ⟨coordinate⟩⟩ := hCover (QuotientComponent Q e)
  exact ⟨q, hq, ⟨coordinate.toAlgHom.comp
    (Ideal.Quotient.mkₐ (LaurentPolynomial K) (Ideal.span {1 - e}))⟩⟩

open scoped WideE

variable {K Q S : Type u} [Field K] [CommRing Q] [Nontrivial Q] [CommRing S]
  [Algebra (LaurentPolynomial K) Q] [Algebra (LaurentPolynomial K) S] [Algebra Q S]
  [IsScalarTower (LaurentPolynomial K) Q S]

/-- A point on the pullback of a torsor over one Kummer component of its
finite quotient gives a section of the original torsor after the same cover. -/
theorem exists_kummerSection_of_finiteEtale_quotient_map
    [Module.Finite (LaurentPolynomial K) Q] [Algebra.Etale (LaurentPolynomial K) Q]
    (hCover : FiniteLaurentCoverHasKummerMap K)
    (hPoint : ∀ (q : ℕ), 0 < q →
      ∀ j : Q →ₐ[LaurentPolynomial K] KummerExtension K q,
        Nonempty (KummerComponentSection j S)) :
    ∃ q : ℕ, 0 < q ∧ Nonempty (S →ₐ[LaurentPolynomial K] KummerExtension K q) := by
  obtain ⟨q, hq, ⟨j⟩⟩ := hCover Q
  obtain ⟨s⟩ := hPoint q hq j
  exact ⟨q, hq, ⟨kummerSectionAlgHom j s⟩⟩

theorem exists_kummerSection_of_finiteEtale_quotient
    [Module.Finite (LaurentPolynomial K) Q] [Algebra.Etale (LaurentPolynomial K) Q]
    (hCover : ConnectedLaurentCoverIsKummer K)
    (hPoint : ∀ (q : ℕ), 0 < q →
      ∀ j : Q →ₐ[LaurentPolynomial K] KummerExtension K q,
        Nonempty (KummerComponentSection j S)) :
    ∃ q : ℕ, 0 < q ∧ Nonempty (S →ₐ[LaurentPolynomial K] KummerExtension K q) :=
  exists_kummerSection_of_finiteEtale_quotient_map hCover.hasKummerMap hPoint

end WideE
