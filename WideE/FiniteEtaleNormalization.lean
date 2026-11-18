import WideE.KummerFractionField
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Unramified.LocalRing

/-! A finite unramified domain over the Laurent ring is normal.
This connects a fraction-field power coordinate with the actual finite
cover, where the latter is presented over the pinned Laurent algebra. -/

noncomputable section

open LaurentPolynomial

namespace WideE

set_option maxHeartbeats 600000

/-- A finite unramified domain over a principal ideal ring is integrally
closed. At a maximal ideal, unramifiedness identifies the maximal ideal of
the localization with the extension of the principal base ideal. -/
theorem isIntegrallyClosed_of_finite_unramified_pid
    (R A : Type*) [CommRing R] [IsPrincipalIdealRing R] [CommRing A] [IsDomain A]
    [Algebra R A] [Module.Finite R A] [Algebra.FormallyUnramified R A] :
    IsIntegrallyClosed A := by
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  let B := Localization.AtPrime p
  let q := p.comap (algebraMap R A)
  letI : p.IsMaximal := hp
  letI : q.IsPrime := Ideal.IsPrime.comap (algebraMap R A)
  letI : p.LiesOver q := ⟨rfl⟩
  letI : Algebra.IsUnramifiedAt R p := by
    change Algebra.FormallyUnramified R B
    letI : Algebra.FormallyUnramified A B := Algebra.FormallyUnramified.of_isLocalization p.primeCompl
    exact Algebra.FormallyUnramified.comp R A B
  have hm : Ideal.map (algebraMap R B) q = IsLocalRing.maximalIdeal B :=
    ((Algebra.isUnramifiedAt_iff_map_eq R q p).mp inferInstance).2
  obtain ⟨x, hx⟩ := (IsPrincipalIdealRing.principal q).principal
  have hgen : Ideal.span {algebraMap R B x} = IsLocalRing.maximalIdeal B := by
    change q = Ideal.span {x} at hx
    rw [← hm, hx, Ideal.map_span, Set.image_singleton]
  have hprinc : (IsLocalRing.maximalIdeal B).IsPrincipal := ⟨⟨algebraMap R B x, hgen.symm⟩⟩
  letI : IsNoetherianRing B := IsLocalization.isNoetherianRing p.primeCompl B inferInstance
  letI : IsPrincipalIdealRing B :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain B).out 4 0).mp hprinc
  infer_instance

universe u

section FractionCoordinate

variable {K Q : Type u} [Field K] [CommRing Q] [IsDomain Q]
  [Algebra (LaurentPolynomial K) Q]

/-- The Laurent algebra action on the actual fraction field of a finite cover. -/
def laurentFractionAlgebra : Algebra (LaurentPolynomial K) (FractionRing Q) :=
  ((algebraMap Q (FractionRing Q)).comp (algebraMap (LaurentPolynomial K) Q)).toAlgebra

/-- The coefficient field acts through the given Laurent structure map. -/
def laurentFractionCoefficients :
    letI := laurentFractionAlgebra (K := K) (Q := Q)
    Algebra K (FractionRing Q) :=
  letI := laurentFractionAlgebra (K := K) (Q := Q)
  ((algebraMap (LaurentPolynomial K) (FractionRing Q)).comp
    (algebraMap K (LaurentPolynomial K))).toAlgebra

/-- The field-theoretic output of the two-branch argument for the given
cover, with its original coordinate in the fraction field. -/
def LaurentFractionPowerCoordinate : Prop :=
  letI := laurentFractionAlgebra (K := K) (Q := Q)
  letI := laurentFractionCoefficients (K := K) (Q := Q)
  ∃ q : ℕ, 0 < q ∧ ∃ t : FractionRing Q,
    t ^ q = algebraMap (LaurentPolynomial K) (FractionRing Q) (T 1) ∧
    IntermediateField.adjoin K ({t} : Set (FractionRing Q)) = ⊤

theorem exists_kummerEquiv_of_finite_etale_fractionPower [Module.Finite (LaurentPolynomial K) Q]
    [Algebra.Etale (LaurentPolynomial K) Q]
    (hBase : Function.Injective (algebraMap (LaurentPolynomial K) Q))
    (hPower : LaurentFractionPowerCoordinate (K := K) (Q := Q)) :
    ∃ q : ℕ, 0 < q ∧ q = Module.finrank (LaurentPolynomial K) Q ∧
      Nonempty (Q ≃ₐ[LaurentPolynomial K] KummerExtension K q) := by
  let R := LaurentPolynomial K
  let E := FractionRing Q
  letI : IsPrincipalIdealRing R := StrictEUnit.laurentPolynomial_isPrincipalIdealRing K
  letI : IsIntegrallyClosed Q := isIntegrallyClosed_of_finite_unramified_pid R Q
  letI := laurentFractionAlgebra (K := K) (Q := Q)
  letI := laurentFractionCoefficients (K := K) (Q := Q)
  letI : SMul Q E := Algebra.toSMul
  letI : SMul R E := Algebra.toSMul
  letI : SMul K E := Algebra.toSMul
  letI : IsScalarTower R Q E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower K R E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨q, hq, t, ht, htGen⟩ := hPower
  obtain ⟨e⟩ := kummerEquiv_of_fractionFieldPower hBase hq t ht htGen
  refine ⟨q, hq, ?_, ⟨e⟩⟩
  rw [Module.finrank_eq_card_basis ((KummerExtension.basis K q hq).map e.symm.toLinearEquiv),
    Fintype.card_fin]

end FractionCoordinate

end WideE
