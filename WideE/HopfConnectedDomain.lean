import WideE.HopfSmoothness
import WideE.IdentityComponentHopf
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-! A reduced connected affine group over an algebraically closed field
has an integral coordinate algebra. -/

noncomputable section

open Set TopologicalSpace

namespace WideE

universe u

section Groups

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

private def spectrumTranslation (p : H →ₐ[k] k) : PrimeSpectrum H ≃ₜ PrimeSpectrum H :=
  (PrimeSpectrum.homeomorphOfRingEquiv (hopfTranslation p).toRingEquiv).symm

private theorem spectrumTranslation_counit (p : H →ₐ[k] k) :
    spectrumTranslation p (hopfPointPrime (Bialgebra.counitAlgHom k H)) = hopfPointPrime p := by
  apply PrimeSpectrum.ext
  ext a
  change Bialgebra.counitAlgHom k H (hopfTranslation p a) = 0 ↔ p a = 0
  rw [hopfTranslation_counit]

private theorem exists_closed_point_in_closed {s : Set (PrimeSpectrum H)}
    (hS : IsClosed s) (hne : s.Nonempty) : ∃ x ∈ s, x.asIdeal.IsMaximal := by
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hS
  obtain ⟨y, hy⟩ := hne
  obtain ⟨m, hm, hM⟩ := y.asIdeal.exists_le_maximal y.isPrime.ne_top
  exact ⟨⟨m, hm.isPrime⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr
    (hM.trans' ((PrimeSpectrum.mem_zeroLocus _ _).mp hy)), hm⟩

variable [IsAlgClosed k] [Algebra.FiniteType k H]

include k

private theorem exists_irreducible_open_neighborhood_at_maximal
    (x : PrimeSpectrum H) (hx : x.asIdeal.IsMaximal) :
    ∃ u : Set (PrimeSpectrum H), IsOpen u ∧ x ∈ u ∧ IsIrreducible u := by
  letI : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  letI : IsJacobsonRing H := isJacobsonRing_of_finiteType (A := k)
  let e := hopfPointPrime (Bialgebra.counitAlgHom k H)
  let C := irreducibleComponent e
  have hC : C ∈ irreducibleComponents (PrimeSpectrum H) := irreducibleComponent_mem_irreducibleComponents e
  obtain ⟨U, hU, hne, hUC⟩ := NoetherianSpace.exists_open_ne_empty_le_irreducibleComponent C hC
  have hUn : U.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  have hI : IsIrreducible U := hC.1.isPreirreducible.subset_irreducible hUn hU subset_rfl hUC
  obtain ⟨y, hy, hY⟩ := PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing U hU hUn
  letI : y.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hY
  letI := hx
  let p := StrictEUnit.maximalIdealPoint (k := k) y.asIdeal
  let q := StrictEUnit.maximalIdealPoint (k := k) x.asIdeal
  have hp : spectrumTranslation p e = y :=
    (spectrumTranslation_counit p).trans (PrimeSpectrum.ext (StrictEUnit.maximalIdealPoint_ker _))
  have hq : spectrumTranslation q e = x :=
    (spectrumTranslation_counit q).trans (PrimeSpectrum.ext (StrictEUnit.maximalIdealPoint_ker _))
  let t := (spectrumTranslation p).symm.trans (spectrumTranslation q)
  have ht : t y = x := by
    change spectrumTranslation q ((spectrumTranslation p).symm y) = x
    rw [← hp, Homeomorph.symm_apply_apply, hq]
  exact ⟨t '' U, t.isOpenMap U hU, ⟨y, hy, ht⟩, hI.image t t.continuous.continuousOn⟩

private theorem irreducibleComponents_eq_of_nonempty_inter
    {C D : Set (PrimeSpectrum H)} (hC : C ∈ irreducibleComponents (PrimeSpectrum H))
    (hD : D ∈ irreducibleComponents (PrimeSpectrum H)) (hCD : (C ∩ D).Nonempty) : C = D := by
  obtain ⟨x, hx, hMax⟩ := exists_closed_point_in_closed
    ((isClosed_of_mem_irreducibleComponents C hC).inter (isClosed_of_mem_irreducibleComponents D hD)) hCD
  obtain ⟨U, hU, hxU, hI⟩ := exists_irreducible_open_neighborhood_at_maximal (k := k) x hMax
  have hC' : C ⊆ closure U :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hC.1.isPreirreducible hU ⟨x, hx.1, hxU⟩).trans
      (closure_mono Set.inter_subset_right)
  have hD' : D ⊆ closure U :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hD.1.isPreirreducible hU ⟨x, hx.2, hxU⟩).trans
      (closure_mono Set.inter_subset_right)
  exact (hC'.antisymm (hC.2 hI.closure hC')).trans (hD'.antisymm (hD.2 hI.closure hD')).symm

private theorem irreducible_univ_of_hopf_connected [ConnectedSpace (PrimeSpectrum H)] :
    IsIrreducible (univ : Set (PrimeSpectrum H)) := by
  letI : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  let C := irreducibleComponent (hopfPointPrime (Bialgebra.counitAlgHom k H))
  have hC : C ∈ irreducibleComponents (PrimeSpectrum H) := irreducibleComponent_mem_irreducibleComponents _
  let F := irreducibleComponents (PrimeSpectrum H) \ {C}
  have hF : F.Finite := NoetherianSpace.finite_irreducibleComponents.subset Set.diff_subset
  letI : Finite F := hF.to_subtype
  have hComp : Cᶜ = ⋃₀ F := by
    ext x
    constructor
    · intro hx
      refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x, ?_⟩,
        mem_irreducibleComponent⟩
      intro he
      exact hx ((Set.mem_singleton_iff.mp he) ▸ mem_irreducibleComponent)
    · rintro ⟨D, hD, hxD⟩ hxC
      exact hD.2 (Set.mem_singleton_iff.mpr
        (irreducibleComponents_eq_of_nonempty_inter (k := k) hD.1 hC ⟨x, hxD, hxC⟩))
  have hClosed : IsClosed Cᶜ := by
    rw [hComp, Set.sUnion_eq_iUnion]
    exact isClosed_iUnion_of_finite fun D : F => isClosed_of_mem_irreducibleComponents _ D.property.1
  have hClopen : IsClopen C :=
    ⟨isClosed_of_mem_irreducibleComponents _ hC, by simpa only [compl_compl] using hClosed.isOpen_compl⟩
  have hUniv := (isClopen_iff.mp hClopen).resolve_left hC.1.nonempty.ne_empty
  exact hUniv ▸ hC.1

/-- A reduced connected affine group over an algebraically closed field
has a domain as its coordinate algebra. -/
theorem hopfDomain_of_connected_reduced [IsReduced H] [ConnectedSpace (PrimeSpectrum H)] :
    IsDomain H := by
  have hp := PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp
    (irreducible_univ_of_hopf_connected (k := k) (H := H))
  rw [PrimeSpectrum.vanishingIdeal_univ, nilradical_eq_bot_iff.mpr (inferInstance : IsReduced H)] at hp
  letI : Nontrivial H := (Bialgebra.counitAlgHom k H).toRingHom.domain_nontrivial
  letI : NoZeroDivisors H := ⟨fun h => (hp.mem_or_mem (Ideal.mem_bot.mpr h)).imp
    Ideal.mem_bot.mp Ideal.mem_bot.mp⟩
  exact NoZeroDivisors.to_isDomain H

end Groups

namespace ComponentHopfPresentation

variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
variable [Algebra.FiniteType k H] [IsReduced H] (P : ComponentHopfPresentation k H)

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
/-- The identity component is reduced because its quotient is localization
at the idempotent of that component. -/
theorem identityComponent_isReduced : IsReduced P.IdentityComponent := by
  letI := P.index_finite
  let e := P.idempotent P.identityIndex
  letI : IsLocalization.Away e P.IdentityComponent :=
    IsLocalization.Away.quotient_of_isIdempotentElem (P.complete.idem P.identityIndex)
  exact isReduced_localizationPreserves (Submonoid.powers e) P.IdentityComponent inferInstance

theorem identityComponent_isDomain : IsDomain P.IdentityComponent := by
  letI := P.identityHopf
  letI := P.identityComponent_finiteType
  letI := P.identityComponent_connected
  letI := P.identityComponent_isReduced
  exact hopfDomain_of_connected_reduced (k := k)

end ComponentHopfPresentation

section OrdinaryPV

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {r : ℕ}
variable (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))

theorem ordinaryPVIdentityComponent_isDomain :
    letI := ordinaryPVHopf A
    ∀ P : ComponentHopfPresentation K (ordinaryPVGroup A), IsDomain P.IdentityComponent := by
  letI := ordinaryPVHopf A
  letI := ordinaryPVGroup_finiteType A
  letI := ordinaryPVGroup_isReduced A
  exact fun P => P.identityComponent_isDomain

end OrdinaryPV

end WideE
