import WideE.GaloisTorsor
import WideE.PianzolaKummerTransport
import WideE.LaurentSectionFromGenericPoint
import WideE.TorsorBaseChange

/-! Generic Galois descent, Laurent sections, and transport to the Kummer algebras. -/

noncomputable section

open scoped TensorProduct
open StrictEUnit

namespace WideE

local notation "K" => AlgebraicComplex
local notation "R" => LaurentPolynomial AlgebraicComplex
local notation "F" => RatFunc AlgebraicComplex

section FixedGroup

variable {H S : Type} [CommRing H] [HopfAlgebra K H] [IsDomain H]
  [CommRing S] [Algebra K S] [Algebra R S] [IsScalarTower K R S]

set_option maxHeartbeats 1800000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- Coboundary triviality over the rational function field gives the section
of the given connected Laurent torsor. -/
theorem AffineHopfTorsor.nonempty_laurentSection_of_finiteGalois_coboundary
    (T : AffineHopfTorsor K R S H)
    (hC : ∀ (E : FiniteGaloisIntermediateField F (AlgebraicClosure F))
      (c : (E ≃ₐ[F] E) → H →ₐ[K] E), IsHopfPointCocycle c → IsHopfPointCoboundary c) :
    Nonempty (S →ₐ[R] R) := by
  letI := laurentRatFuncAlgebra K
  letI := laurentRatFunc_scalarTower K
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let S' := F ⊗[R] S
  let T' : AffineHopfTorsor K F S' H := T.baseChange (A := F)
  obtain ⟨p⟩ := T'.nonempty_basePoint_of_finiteGalois_cocycle_triviality
    (fun E _ _ c hc => hC (FiniteGaloisIntermediateField.mk E) c hc)
  let i : S →ₐ[R] S' := Algebra.TensorProduct.includeRight
  exact T.nonempty_laurentSection_of_genericPoint ((p.restrictScalars R).comp i)

end FixedGroup

set_option maxHeartbeats 1800000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The cocycle theorem for finite-type connected affine groups supplies
the Kummer section theorem through its Laurent generic point. -/
theorem pianzolaForKummerAlgebras_of_finiteGalois_coboundary
    (hC : ∀ (H : Type) [CommRing H] [HopfAlgebra K H] [Algebra.FiniteType K H] [IsDomain H]
      (E : FiniteGaloisIntermediateField F (AlgebraicClosure F))
      (c : (E ≃ₐ[F] E) → H →ₐ[K] E), IsHopfPointCocycle c → IsHopfPointCoboundary c) :
    PianzolaForKummerAlgebras K := by
  apply pianzolaForKummerAlgebras_of_laurentSections
  intro H _ hAlg hHopf hSmooth _ S _ _ _ _ T
  letI : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ
  have hReduced : IsReduced H := by
    letI : Algebra K H := hAlg
    letI : Algebra.Smooth K H := hSmooth
    exact isReduced_of_smooth_of_isAlgClosed K H
  letI : Algebra K H := hHopf.toBialgebra.toAlgebra
  letI : Algebra.FiniteType K H := T.group_finiteType
  letI : IsReduced H := hReduced
  letI : IsDomain H := hopfDomain_of_connected_reduced (k := K) (H := H)
  exact T.nonempty_laurentSection_of_finiteGalois_coboundary (hC H)

end WideE
