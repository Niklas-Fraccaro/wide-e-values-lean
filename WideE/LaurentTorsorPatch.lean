import WideE.TensorLocalization
import WideE.TorsorTrivialization

/-! The affine coordinate algebra obtained by adjoining a trivial chart at
the origin to a torsor on the Laurent line. -/

open scoped TensorProduct

noncomputable section

namespace WideE

open LaurentPolynomial

attribute [local instance 2000] Algebra.toSMul Algebra.toModule

variable {K S H : Type*} [Field K] [CommRing S] [CommRing H] [Algebra K H]
  [Algebra (Polynomial K) S] [Algebra (LaurentPolynomial K) S]
  [IsScalarTower (Polynomial K) (LaurentPolynomial K) S]
  (p : Polynomial K)

local notation "PolyRing" => Polynomial K
local notation "LaurentRing" => LaurentPolynomial K
local notation "OpenRing" => Localization.Away p
local notation "Overlap" => Localization.Away p.toLaurent

local instance overlapCoefficientTower : IsScalarTower K PolyRing Overlap :=
  IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap LaurentRing Overlap (C x) =
      algebraMap LaurentRing Overlap (Polynomial.toLaurent (Polynomial.C x))
    rw [Polynomial.toLaurent_C]

local instance overlapTensorPolynomialAlgebra : Algebra PolyRing (Overlap ⊗[K] H) :=
  Algebra.TensorProduct.leftAlgebra (R := K)

local instance overlapTensorLaurentTower : IsScalarTower PolyRing LaurentRing (Overlap ⊗[K] H) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local notation "PatchChart" => Overlap ⊗[LaurentRing] S ≃ₐ[Overlap] Overlap ⊗[K] H

/-- Restrict the original torsor to the common open and use its trivialization there. -/
def laurentPatchLeft (chart : PatchChart) : S →ₐ[PolyRing] Overlap ⊗[K] H := by
  let i : S →ₐ[LaurentRing] Overlap ⊗[LaurentRing] S := Algebra.TensorProduct.includeRight
  let e : Overlap ⊗[LaurentRing] S →ₐ[LaurentRing] Overlap ⊗[K] H :=
    chart.toAlgHom.restrictScalars LaurentRing
  exact (e.comp i).restrictScalars PolyRing

/-- Restriction of the trivial chart centered at the origin. -/
def laurentPatchRight : OpenRing ⊗[K] H →ₐ[PolyRing] Overlap ⊗[K] H :=
  Algebra.TensorProduct.map (polynomialOpenToLaurentOpen p) (AlgHom.id K H)

/-- The ring of the scheme obtained from the two affine charts. -/
abbrev LaurentAffinePatch (chart : PatchChart) : Type _ :=
  ↥(affinePatchAlgebra (R := PolyRing) (B := S) (C := OpenRing ⊗[K] H) (E := Overlap ⊗[K] H)
    (laurentPatchLeft p chart) (laurentPatchRight (H := H) p))

/-- Away from zero the patched ring recovers the original torsor algebra. -/
theorem laurentAffinePatch_localizes_at_coordinate (chart : PatchChart) :
    letI := (affinePatchLeft (laurentPatchLeft p chart) (laurentPatchRight (H := H) p)).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap PolyRing (LaurentAffinePatch p chart) Polynomial.X) S := by
  letI : Algebra OpenRing Overlap := (polynomialOpenToLaurentOpen p).toRingHom.toAlgebra
  letI : IsScalarTower PolyRing OpenRing Overlap := IsScalarTower.of_algHom (polynomialOpenToLaurentOpen p)
  letI : IsScalarTower K OpenRing Overlap :=
    IsScalarTower.of_algHom ((polynomialOpenToLaurentOpen p).restrictScalars K)
  letI := polynomialOpen_localizationAtCoordinate p
  letI : Algebra (OpenRing ⊗[K] H) (Overlap ⊗[K] H) :=
    (laurentPatchRight (H := H) p).toRingHom.toAlgebra
  letI : IsScalarTower PolyRing (OpenRing ⊗[K] H) (Overlap ⊗[K] H) :=
    IsScalarTower.of_algHom (laurentPatchRight (H := H) p)
  letI : IsLocalization.Away (algebraMap PolyRing (OpenRing ⊗[K] H) Polynomial.X) (Overlap ⊗[K] H) :=
    constantTensor_isLocalizationAway (k := K) (A := Overlap) (H := H)
      (algebraMap PolyRing OpenRing Polynomial.X)
  have hX : IsUnit (algebraMap PolyRing S Polynomial.X) := by
    rw [IsScalarTower.algebraMap_apply PolyRing LaurentRing S]
    change IsUnit (algebraMap LaurentRing S (Polynomial.toLaurent (Polynomial.X : Polynomial K)))
    rw [Polynomial.toLaurent_X]
    exact (isUnit_T (R := K) 1).map (algebraMap LaurentRing S)
  exact affinePatch_isLocalizationAtLeft (laurentPatchLeft p chart) Polynomial.X hX

/-- On the open of the polynomial used for gluing, the patched ring recovers
the trivial chart. -/
theorem laurentAffinePatch_localizes_at_polynomial (chart : PatchChart) :
    letI := ((affinePatchLeft (laurentPatchRight (H := H) p) (laurentPatchLeft p chart)).comp
      (affinePatchSwap (laurentPatchLeft p chart) (laurentPatchRight (H := H) p)).toAlgHom).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap PolyRing (LaurentAffinePatch p chart) p) (OpenRing ⊗[K] H) := by
  letI : Algebra S (Overlap ⊗[LaurentRing] S) :=
    (Algebra.TensorProduct.includeRight : S →ₐ[LaurentRing] Overlap ⊗[LaurentRing] S).toRingHom.toAlgebra
  letI : Algebra S (Overlap ⊗[K] H) := (laurentPatchLeft p chart).toRingHom.toAlgebra
  letI : IsScalarTower PolyRing S (Overlap ⊗[K] H) := IsScalarTower.of_algHom (laurentPatchLeft p chart)
  let e : Overlap ⊗[LaurentRing] S ≃ₐ[S] Overlap ⊗[K] H :=
    { chart.toRingEquiv with commutes' := fun _ => rfl }
  letI : IsLocalization.Away (algebraMap PolyRing S p) (Overlap ⊗[LaurentRing] S) := by
    rw [IsScalarTower.algebraMap_apply PolyRing LaurentRing S]
    exact baseChange_isLocalizationAway (S := S) (T := Overlap) p.toLaurent
  letI := IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap PolyRing S p)) e
  have hP : IsUnit (algebraMap PolyRing (OpenRing ⊗[K] H) p) := by
    rw [IsScalarTower.algebraMap_apply PolyRing OpenRing (OpenRing ⊗[K] H)]
    exact (IsLocalization.Away.algebraMap_isUnit (S := OpenRing) p).map
      (algebraMap OpenRing (OpenRing ⊗[K] H))
  exact affinePatch_isLocalizationAtRight (laurentPatchRight (H := H) p) p hP

end WideE
