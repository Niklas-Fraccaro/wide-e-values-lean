import WideE.AffineGroupRepresentation
import WideE.BlockDiagonalGalois
import WideE.CenterBlockDiagonal
import Mathlib.FieldTheory.RatFunc.Basic

/-! Reduction of a constant group's rational-function cocycle to a reductive block quotient. -/

noncomputable section

open scoped TensorProduct
open LieAlgebra

namespace WideE

set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 240000

local notation "K" => AlgebraicComplex
local notation "F" => RatFunc AlgebraicComplex

variable (hReductive : ∀ (Q : Type) [CommRing Q] [IsDomain Q] [HopfAlgebra K Q] [Algebra.FiniteType K Q]
    (ι : Type) [Fintype ι] [DecidableEq ι] (W : (Matrix ι ι Q)ˣ),
    (∀ i j, Coalgebra.comul (R := K) (W.val i j) = ∑ l, W.val i l ⊗ₜ[K] W.val l j) →
    (∀ i j, Coalgebra.counit (R := K) (W.val i j) = if i = j then 1 else 0) →
    Algebra.adjoin K (Set.range fun ij : ι × ι => W.val ij.1 ij.2) = ⊤ →
    let L := hopfInvariantDerivations K Q
    IsKilling K (derivedSeries K L 1) →
    IsCompl (derivedSeries K L 1) (center K L) →
    (∀ D ∈ center K L, ∃ d : ι → K, hopfLieMatrix W.val D = Matrix.diagonal d) →
    (∀ D ∈ center K L, IsNilpotent (hopfLieMatrix W.val D) → D = 0) →
    ∀ (E : FiniteGaloisIntermediateField F (AlgebraicClosure F))
      (c : (E ≃ₐ[F] E) → Q →ₐ[K] E), IsHopfPointCocycle c → IsHopfPointCoboundary c)

include hReductive in
/-- Triviality for reductive block representations implies triviality for every
integral affine group, via its actual diagonal-block quotient. -/
theorem isHopfPointCoboundary_of_reductive_block_quotients {H : Type}
    [CommRing H] [IsDomain H] [HopfAlgebra K H] [Algebra.FiniteType K H]
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F)) (c : (E ≃ₐ[F] E) → H →ₐ[K] E)
    (hc : IsHopfPointCocycle c) : IsHopfPointCoboundary c := by
  letI : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨n, U, hD, he, hGen⟩ := exists_generatingHopfMatrix K H
  obtain ⟨r, b, P, hDv, hev, hUpper, hb, hGenV, hDq, heq, hGenQ, hKilling, hCompl, hDiag, hNil⟩ :=
    exists_reductiveBlockDiagonalQuotient_with_matrix U hD he hGen
  let V := conjugateMatrixUnit P U
  let Q := blockDiagonalAlgebra (k := K) b V.val
  letI : HopfAlgebra K Q := (blockDiagonalAlgebra_isHopf b V.val hDv hUpper).hopfAlgebra
  letI : IsDomain Q := Function.Injective.isDomain Q.val Subtype.val_injective
  letI : Algebra.FiniteType K Q := blockDiagonalAlgebra_finiteType b V.val
  let W := blockDiagonalQuotientGeneratingUnit b V.val hDv hUpper hev
  let j := blockDiagonalQuotientMap b V.val hDv hUpper
  apply (isHopfPointCoboundary_iff_blockDiagonal b V.val hDv hev hUpper hb hGenV E c hc).mpr
  exact hReductive Q (blockDiagonalGeneratingIndex b) W hDq heq hGenQ
    hKilling hCompl hDiag hNil E _ (hc.precompose j)

include hReductive in
/-- A reduced connected affine group has an integral coordinate ring, so the
same reduction applies directly to its cocycles. -/
theorem isHopfPointCoboundary_of_connected_reduced_reductive_block_quotients {H : Type}
    [CommRing H] [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
    [HopfAlgebra K H] [Algebra.FiniteType K H]
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F)) (c : (E ≃ₐ[F] E) → H →ₐ[K] E)
    (hc : IsHopfPointCocycle c) : IsHopfPointCoboundary c := by
  letI : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ
  letI : IsDomain H := hopfDomain_of_connected_reduced (k := K) (H := H)
  exact isHopfPointCoboundary_of_reductive_block_quotients hReductive E c hc

include hReductive in
/-- An affine torsor under a reduced connected constant group has a rational
point once the reductive block cocycles are trivial. -/
theorem AffineHopfTorsor.nonempty_basePoint_ratFunc_of_reductive_block_quotients {H S : Type}
    [CommRing H] [IsReduced H] [ConnectedSpace (PrimeSpectrum H)] [HopfAlgebra K H]
    [CommRing S] [Algebra K S] [Algebra F S] [IsScalarTower K F S]
    (T : AffineHopfTorsor K F S H) : Nonempty (S →ₐ[F] F) := by
  letI : Algebra.FiniteType K H := T.group_finiteType
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  apply T.nonempty_basePoint_of_finiteGalois_cocycle_triviality
  intro E _ _ c hc
  exact isHopfPointCoboundary_of_connected_reduced_reductive_block_quotients hReductive
    (FiniteGaloisIntermediateField.mk E) c hc

end WideE
