import WideE.HopfSubalgebra
import WideE.LieInvariantFlag

/-! Contragradients and direct sums of actual Hopf matrix representations. -/

noncomputable section

open scoped BigOperators Matrix TensorProduct
open TensorProduct StrictEUnit

namespace WideE

section Dual

variable {k A ι : Type*} [Field k] [CommRing A] [HopfAlgebra k A] [Fintype ι] [DecidableEq ι]

local notation "ε" => Bialgebra.counitAlgHom k A
local notation "S" => hopfAntipodeAlgHom k A

theorem counit_comp_hopfAntipodeAlgHom : (ε).comp S = ε := by
  letI := hopfPointGroup (k := k) (H := A) (A := k)
  exact inv_one

/-- The matrix of the dual representation. -/
def dualHopfMatrix (U : Matrix ι ι A) : Matrix ι ι A := (U.map S).transpose

omit [DecidableEq ι] in
theorem dualHopfMatrix_comul (U : Matrix ι ι A)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U i j) = ∑ l, U i l ⊗ₜ[k] U l j) :
    ∀ i j, Coalgebra.comul (R := k) (dualHopfMatrix (k := k) U i j) =
      ∑ l, dualHopfMatrix (k := k) U i l ⊗ₜ[k] dualHopfMatrix (k := k) U l j := by
  intro i j
  have h := DFunLike.congr_fun (hopfComulAlgHom_comp_antipode (k := k) (H := A)) (U j i)
  change Coalgebra.comul (R := k) (S (U j i)) =
    Algebra.TensorProduct.comm k A A (Algebra.TensorProduct.map S S (Coalgebra.comul (R := k) (U j i))) at h
  rw [hD, map_sum, map_sum] at h
  simpa only [dualHopfMatrix, Matrix.transpose_apply, Matrix.map_apply, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.comm_tmul] using h

omit [Fintype ι] in
theorem dualHopfMatrix_counit (U : Matrix ι ι A)
    (he : ∀ i j, Coalgebra.counit (R := k) (U i j) = if i = j then 1 else 0) :
    ∀ i j, Coalgebra.counit (R := k) (dualHopfMatrix (k := k) U i j) = if i = j then 1 else 0 := by
  intro i j
  have h := DFunLike.congr_fun (counit_comp_hopfAntipodeAlgHom (k := k) (A := A)) (U j i)
  change (ε) (S (U j i)) = (ε) (U j i) at h
  change (ε) (S (U j i)) = _
  rw [h]
  simpa only [eq_comm] using he j i

/-- A matrix with the Hopf corepresentation relations is invertible. -/
def hopfMatrixUnitOfRelations (U : Matrix ι ι A)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U i j) = ∑ l, U i l ⊗ₜ[k] U l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U i j) = if i = j then 1 else 0) : (Matrix ι ι A)ˣ where
  val := U
  inv := U.map S
  val_inv := by
    ext i j
    have h := HopfAlgebra.mul_antipode_lTensor_comul_apply (R := k) (U i j)
    rw [hD i j] at h
    simpa only [map_sum, LinearMap.lTensor_tmul, LinearMap.mul'_apply, Algebra.linearMap_apply,
      he, apply_ite (algebraMap k A), map_one, map_zero, Matrix.mul_apply, Matrix.map_apply,
      Matrix.one_apply, hopfAntipodeAlgHom_apply] using h
  inv_val := by
    ext i j
    have h := HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) (U i j)
    rw [hD i j] at h
    simpa only [map_sum, LinearMap.rTensor_tmul, LinearMap.mul'_apply, Algebra.linearMap_apply,
      he, apply_ite (algebraMap k A), map_one, map_zero, Matrix.mul_apply, Matrix.map_apply,
      Matrix.one_apply, hopfAntipodeAlgHom_apply] using h

/-- On the dual, the derivative is the negative transpose of the original tangent matrix. -/
theorem hopfLieMatrix_dual (U : Matrix ι ι A)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U i j) = ∑ l, U i l ⊗ₜ[k] U l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U i j) = if i = j then 1 else 0)
    (D : hopfInvariantDerivations k A) :
    hopfLieMatrix (dualHopfMatrix (k := k) U) D = -(hopfLieMatrix U D).transpose := by
  let X := U.map S
  let φ := (ε).toRingHom.mapMatrix (m := ι)
  let P := hopfMatrixUnitOfRelations U hD he
  have hXU : X * U = 1 := P.inv_val
  have hφU : φ U = 1 := Matrix.ext fun i j => (he i j).trans Matrix.one_apply.symm
  have hφX : φ X = 1 := by
    have h := congrArg φ hXU
    rwa [map_mul, hφU, mul_one, map_one] at h
  have h := congrArg φ (matrixDerivative_mul D.val X U)
  rw [hXU, matrixDerivative_one, map_zero, map_add, map_mul, map_mul,
    hφU, hφX, mul_one, one_mul] at h
  have hNeg : φ (matrixDerivative D.val X) = -φ (matrixDerivative D.val U) :=
    add_eq_zero_iff_eq_neg.mp h.symm
  exact Matrix.ext fun i j => congrArg (fun M : Matrix ι ι k => M j i) hNeg

end Dual

section DirectSum

variable {k A T : Type*} [Field k] [CommRing A] [HopfAlgebra k A]
  [Fintype T] [DecidableEq T] {ι : T → Type*} [∀ t, Fintype (ι t)] [∀ t, DecidableEq (ι t)]

/-- A block direct sum carries the Hopf corepresentation of its summands. -/
theorem blockDiagonal_hopfMatrix_relations (U : ∀ t, Matrix (ι t) (ι t) A)
    (hD : ∀ t i j, Coalgebra.comul (R := k) (U t i j) = ∑ l, U t i l ⊗ₜ[k] U t l j)
    (he : ∀ t i j, Coalgebra.counit (R := k) (U t i j) = if i = j then 1 else 0) :
    (∀ i j, Coalgebra.comul (R := k) (Matrix.blockDiagonal' U i j) =
      ∑ l, Matrix.blockDiagonal' U i l ⊗ₜ[k] Matrix.blockDiagonal' U l j) ∧
    (∀ i j, Coalgebra.counit (R := k) (Matrix.blockDiagonal' U i j) = if i = j then 1 else 0) := by
  classical
  constructor
  · rintro ⟨t, i⟩ ⟨s, j⟩
    rcases eq_or_ne t s with rfl | hts
    · rw [Matrix.blockDiagonal'_apply_eq, hD]
      symm
      have hInj : Function.Injective (@Sigma.mk T ι t) :=
        fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2
      refine (Fintype.sum_of_injective (@Sigma.mk T ι t) hInj _ _ ?_ ?_).symm
      · rintro ⟨q, l⟩ hq
        have hne : t ≠ q := fun h => hq ⟨h.symm ▸ l, by cases h; rfl⟩
        rw [Matrix.blockDiagonal'_apply_ne U i l hne, zero_tmul]
      · intro l
        rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal'_apply_eq]
    · rw [Matrix.blockDiagonal'_apply_ne U i j hts, map_zero]
      symm
      apply Finset.sum_eq_zero
      rintro ⟨q, l⟩ _
      rcases eq_or_ne t q with rfl | htq
      · rw [Matrix.blockDiagonal'_apply_ne U l j hts, tmul_zero]
      · rw [Matrix.blockDiagonal'_apply_ne U i l htq, zero_tmul]
  · rintro ⟨t, i⟩ ⟨s, j⟩
    rcases eq_or_ne t s with rfl | hts
    · rw [Matrix.blockDiagonal'_apply_eq, he]
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
    · rw [Matrix.blockDiagonal'_apply_ne U i j hts, map_zero]
      exact (if_neg fun h => hts (congrArg Sigma.fst h)).symm

omit [Fintype T] [∀ t, Fintype (ι t)] [∀ t, DecidableEq (ι t)] in
theorem hopfLieMatrix_blockDiagonal' (U : ∀ t, Matrix (ι t) (ι t) A)
    (D : hopfInvariantDerivations k A) :
    hopfLieMatrix (Matrix.blockDiagonal' U) D =
      Matrix.blockDiagonal' (fun t => hopfLieMatrix (U t) D) :=
  Matrix.blockDiagonal'_map U (fun x => Bialgebra.counitAlgHom k A (D.val x)) (by simp)

end DirectSum

end WideE
