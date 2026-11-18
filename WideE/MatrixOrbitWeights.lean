import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.TensorProduct.Basic

/-! A weight at a fiber point gives a weight of the matrix orbit vector. -/

open scoped BigOperators Matrix TensorProduct

namespace WideE

variable {k S H ι : Type*} [CommRing k] [CommRing S] [CommRing H]
variable [Algebra k S] [Algebra k H] [Fintype ι]

local notation "leftFactor" => (Algebra.TensorProduct.includeLeft : S →ₐ[k] S ⊗[k] H)
local notation "rightFactor" => (Algebra.TensorProduct.includeRight : H →ₐ[k] S ⊗[k] H)

/-- The matrix orbit identity transports the fiber weight to every coordinate
of the orbit vector. -/
theorem weighted_vector_of_matrix_orbit
    (ρ : S →ₐ[k] S ⊗[k] H) (o : S →ₐ[k] H) (U : Matrix ι ι S)
    (hU : U.map ρ = U.map leftFactor * (U.map o).map rightFactor)
    (x : ι → k) (χ : H)
    (hχ : ∀ i, o ((U *ᵥ (algebraMap k S ∘ x)) i) = x i • χ) :
    ∀ i, ρ ((U *ᵥ (algebraMap k S ∘ x)) i) =
      ((U *ᵥ (algebraMap k S ∘ x)) i) ⊗ₜ[k] χ := by
  let a := algebraMap k S ∘ x
  let v := U *ᵥ a
  have hScalar : ρ ∘ a = rightFactor ∘ o ∘ a := by
    funext i
    change ρ (algebraMap k S (x i)) = rightFactor (o (algebraMap k S (x i)))
    rw [ρ.commutes, o.commutes, AlgHom.commutes]
  have hFiber : (U.map o) *ᵥ (o ∘ a) = o ∘ v := by
    funext i
    exact (RingHom.map_mulVec o.toRingHom U a i).symm
  have hRight : ((U.map o).map rightFactor) *ᵥ (rightFactor ∘ o ∘ a) = rightFactor ∘ o ∘ v := by
    funext i
    calc
      _ = rightFactor (((U.map o) *ᵥ (o ∘ a)) i) :=
        (RingHom.map_mulVec (rightFactor).toRingHom (U.map o) (o ∘ a) i).symm
      _ = _ := by rw [hFiber]; rfl
  have hOrbit (i : ι) : ρ (v i) = (U.map leftFactor *ᵥ (rightFactor ∘ o ∘ v)) i := by
    calc
      ρ (v i) = (U.map ρ *ᵥ (ρ ∘ a)) i := RingHom.map_mulVec ρ.toRingHom U a i
      _ = (U.map leftFactor *ᵥ (rightFactor ∘ o ∘ v)) i := by
        rw [hU, hScalar, ← Matrix.mulVec_mulVec, hRight]
  have hTerm (i j : ι) :
      leftFactor (U i j) * rightFactor (o (v j)) = (U i j * a j) ⊗ₜ[k] χ := by
    rw [show o (v j) = x j • χ from hχ j]
    change (U i j ⊗ₜ[k] (1 : H)) * ((1 : S) ⊗ₜ[k] (x j • χ)) =
      (U i j * algebraMap k S (x j)) ⊗ₜ[k] χ
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    calc
      _ = (x j • U i j) ⊗ₜ[k] χ := (TensorProduct.smul_tmul (x j) (U i j) χ).symm
      _ = _ := by rw [Algebra.smul_def, mul_comm (algebraMap k S (x j))]
  intro i
  change ρ (v i) = v i ⊗ₜ[k] χ
  rw [hOrbit]
  change (∑ j, leftFactor (U i j) * rightFactor (o (v j))) = v i ⊗ₜ[k] χ
  simp_rw [hTerm]
  rw [← TensorProduct.sum_tmul]
  rfl

end WideE
