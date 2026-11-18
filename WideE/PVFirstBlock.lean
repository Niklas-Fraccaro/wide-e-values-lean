import WideE.PVOrbit
import WideE.SectionComparison

/-! The first summand of the normalized fundamental matrix of two systems. -/

noncomputable section

open scoped Matrix TensorProduct WideE

namespace WideE

open StrictEUnit

attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule Subalgebra.toCommRing

variable {K : Type*} [Field K] [CharZero K] {m n : ℕ}
  (BM : Matrix (Fin m) (Fin m) (LaurentPolynomial K))
  (BN : Matrix (Fin n) (Fin n) (LaurentPolynomial K))

local notation "A" => combinedLaurentSystem BM BN
local notation "S" => ordinaryPVAlgebra A
local notation "Y" => Units.val (ordinaryPVMatrix A)
local notation "e" => Equiv.symm (finSumFinEquiv (m := m) (n := n))

local instance : CommRing S := (ordinaryPVAlgebra A).toCommRing
local instance : Semiring S := (ordinaryPVAlgebra A).toSemiring
local instance : AddCommMonoid S := (ordinaryPVAlgebra A).toSemiring.toAddCommMonoid
local instance : Algebra (LaurentPolynomial K) S := (ordinaryPVAlgebra A).algebra
local instance : Algebra K S := (ordinaryPVAlgebra A).algebra'
local instance : Module (LaurentPolynomial K) S := Algebra.toModule
local instance : Module K S := Algebra.toModule

/-- The first diagonal block in the ordinary fundamental matrix of the combined system. -/
def ordinaryPVFirstBlock : Matrix (Fin m) (Fin m) S :=
  (Matrix.reindex e e Y).toBlocks₁₁

/-- The formal splitting of the system forces the off-diagonal block to vanish
already in its Picard–Vessiot algebra. -/
theorem ordinaryPVReindexedMatrix_toBlocks₁₂ :
    (Matrix.reindex e e Y).toBlocks₁₂ = 0 := by
  have hinj : Function.Injective (ordinaryPVToPowerSeries A) := by
    intro x y h
    apply Subtype.ext
    simpa only [ordinaryPVToPowerSeries_embed] using congrArg (powerSeriesInLaurent K) h
  apply Matrix.map_injective hinj
  have h := congrArg (fun M : Matrix (Fin (m + n)) (Fin (m + n)) (PowerSeries K) =>
    (Matrix.reindex e e M).toBlocks₁₂) (ordinaryPVToPowerSeries_matrix A)
  change ((Matrix.reindex e e Y).toBlocks₁₂).map (ordinaryPVToPowerSeries A) =
    (Matrix.reindex e e (formalFundamentalAtOneUnit A).val).toBlocks₁₂ at h
  rw [formalFundamentalAtOneUnit_combinedSystem, Matrix.toBlocks_fromBlocks₁₂] at h
  simpa only [Matrix.map_zero _ (map_zero _)] using h

omit [CharZero K] in
/-- The first block evaluates to the identity at the ordinary point. -/
@[simp] theorem ordinaryPVFirstBlock_atOne :
    (ordinaryPVFirstBlock BM BN).map (ordinaryPVAtOne A) = 1 := by
  have h := congrArg (Matrix.reindexAlgEquiv K K e) (ordinaryPVAtOne_matrix A)
  rw [map_one] at h
  have h₁ := congrArg Matrix.toBlocks₁₁ h
  change (ordinaryPVFirstBlock BM BN).map (ordinaryPVAtOne A) =
    (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) K).toBlocks₁₁ at h₁
  rwa [← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁] at h₁

private theorem ordinaryPVFirstBlock_map_eq_of_map_eq_mul {D J : Type*} [CommRing D]
    (ρ ψ : S → D) (β : S → J) (ι : J → D) (hψ : ψ 0 = 0)
    (h : (Y).map ρ = (Y).map ψ * ((Y).map β).map ι) :
    (ordinaryPVFirstBlock BM BN).map ρ =
      (ordinaryPVFirstBlock BM BN).map ψ * ((ordinaryPVFirstBlock BM BN).map β).map ι := by
  let eD := Matrix.reindexAlgEquiv D D e
  let L := eD ((Y).map ψ)
  let R := eD (((Y).map β).map ι)
  have heq : eD ((Y).map ρ) = L * R := (congrArg eD h).trans (map_mul eD _ _)
  have hL : L.toBlocks₁₂ = 0 := by
    change ((Matrix.reindex e e Y).toBlocks₁₂).map ψ = 0
    rw [ordinaryPVReindexedMatrix_toBlocks₁₂, Matrix.map_zero ψ hψ]
  have hmul := Matrix.fromBlocks_multiply L.toBlocks₁₁ L.toBlocks₁₂ L.toBlocks₂₁ L.toBlocks₂₂
    R.toBlocks₁₁ R.toBlocks₁₂ R.toBlocks₂₁ R.toBlocks₂₂
  rw [Matrix.fromBlocks_toBlocks, Matrix.fromBlocks_toBlocks] at hmul
  have hblock := congrArg Matrix.toBlocks₁₁ hmul
  rw [Matrix.toBlocks_fromBlocks₁₁, hL, Matrix.zero_mul, add_zero] at hblock
  exact (congrArg Matrix.toBlocks₁₁ heq).trans hblock

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- The restricted coaction on the first block is multiplication by its
orbit matrix at the normalized ordinary point. -/
theorem ordinaryPVFirstBlock_coaction {J : Type*} [CommRing J] [Algebra K J]
    (π : ordinaryPVGroup A →ₐ[K] J) :
    (ordinaryPVFirstBlock BM BN).map (ordinaryPVRestrictedCoaction A π) =
      (ordinaryPVFirstBlock BM BN).map (fun s : S => s ⊗ₜ[K] (1 : J)) *
        ((ordinaryPVFirstBlock BM BN).map (ordinaryPVOrbit A π)).map (fun j => (1 : S) ⊗ₜ[K] j) := by
  refine ordinaryPVFirstBlock_map_eq_of_map_eq_mul BM BN (ordinaryPVRestrictedCoaction A π)
    (fun s => s ⊗ₜ[K] (1 : J)) (ordinaryPVOrbit A π) (fun j => (1 : S) ⊗ₜ[K] j) (by simp) ?_
  exact ordinaryPVRestrictedCoaction_matrix A π

end WideE
