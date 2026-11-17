import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-! Connected components of finite étale affine schemes over a Noetherian base. -/

namespace WideE

open Set TopologicalSpace

private theorem isClopen_connectedComponent_of_noetherian {X : Type*}
    [TopologicalSpace X] [NoetherianSpace X] (x : X) : IsClopen (connectedComponent x) := by
  refine ⟨isClosed_connectedComponent, isClosed_compl_iff.mp ?_⟩
  let parts := {Z ∈ irreducibleComponents X | Disjoint Z (connectedComponent x)}
  have hf : parts.Finite :=
    NoetherianSpace.finite_irreducibleComponents.subset (fun _ h => h.1)
  letI : Finite parts := hf.to_subtype
  have hparts : (connectedComponent x)ᶜ = ⋃₀ parts := by
    ext y
    constructor
    · intro hy
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩,
        mem_irreducibleComponent⟩
      apply Set.disjoint_left.mpr
      intro w hw hw'
      apply hy
      rw [connectedComponent_eq hw',
        ← connectedComponent_eq (irreducibleComponent_subset_connectedComponent hw)]
      exact mem_connectedComponent
    · rintro ⟨Z, hZ, hy⟩
      exact fun h => Set.disjoint_left.mp hZ.2 hy h
  rw [hparts, Set.sUnion_eq_iUnion]
  exact isClosed_iUnion_of_finite fun z : parts =>
    isClosed_of_mem_irreducibleComponents _ z.property.1

universe u

variable (Q : Type u) [CommRing Q]

/-- The open-and-closed part where the idempotent is one. -/
abbrev QuotientComponent (e : Q) := Q ⧸ Ideal.span {1 - e}

theorem quotientComponent_range {e : Q} (he : IsIdempotentElem e) :
    Set.range (PrimeSpectrum.comap (algebraMap Q (QuotientComponent Q e))) =
      PrimeSpectrum.basicOpen e := by
  letI := IsLocalization.Away.quotient_of_isIdempotentElem he
  exact PrimeSpectrum.localization_away_comap_range _ e

/-- Over a Noetherian base, every connected component of a finite étale affine scheme has a
coordinate ring that is again finite étale. -/
theorem exists_finite_etale_quotientComponent {R Q : Type u} [CommRing R] [CommRing Q]
    [Algebra R Q] [IsNoetherianRing R] [Module.Finite R Q] [Algebra.Etale R Q]
    (x : PrimeSpectrum Q) :
    ∃ e : Q, IsIdempotentElem e ∧
      Set.range (PrimeSpectrum.comap (algebraMap Q (QuotientComponent Q e))) =
        connectedComponent x ∧
      ConnectedSpace (PrimeSpectrum (QuotientComponent Q e)) ∧
      Module.Finite R (QuotientComponent Q e) ∧ Algebra.Etale R (QuotientComponent Q e) := by
  letI := IsNoetherianRing.of_finite R Q
  obtain ⟨e, he, hcx⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    (isClopen_connectedComponent_of_noetherian x)
  letI := IsLocalization.Away.quotient_of_isIdempotentElem he
  letI : Algebra.Etale Q (QuotientComponent Q e) := Algebra.Etale.of_isLocalization_Away e
  have hrange := (quotientComponent_range Q he).trans hcx.symm
  refine ⟨e, he, hrange, ?_, ?_, Algebra.Etale.comp R Q _⟩
  · have hEmb := (PrimeSpectrum.localization_away_isOpenEmbedding (QuotientComponent Q e) e)
      |>.toIsEmbedding
    refine connectedSpace_iff_univ.mpr ⟨?_, ?_⟩
    · obtain ⟨y, _⟩ := (Set.mem_range.mp (hrange.symm ▸ mem_connectedComponent (x := x)))
      exact ⟨y, Set.mem_univ _⟩
    · rw [← hEmb.isInducing.isPreconnected_image, Set.image_univ, hrange]
      exact isPreconnected_connectedComponent
  · exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ R (Ideal.span {1 - e})).toLinearMap
      Ideal.Quotient.mk_surjective

end WideE
