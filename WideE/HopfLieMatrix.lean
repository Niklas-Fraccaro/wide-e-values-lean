import WideE.HopfLieAlgebra
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The induced Lie representation on the matrices of an affine group. -/

noncomputable section

open scoped TensorProduct Matrix

namespace WideE

variable {k H ι : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [Fintype ι] [DecidableEq ι]

local notation "Δ" => (Bialgebra.comulAlgHom k H)
local notation "ε" => (Bialgebra.counitAlgHom k H)
local notation "𝔤" => hopfInvariantDerivations k H

/-- The tangent matrix is the derivative of the coefficient matrix, evaluated at the identity. -/
def hopfLieMatrix (U : Matrix ι ι H) (D : 𝔤) : Matrix ι ι k :=
  fun i j => ε (D.val (U i j))

variable (U : Matrix ι ι H)
  (hD : ∀ i j, Coalgebra.comul (R := k) (U i j) = ∑ l, U i l ⊗ₜ[k] U l j)

omit [DecidableEq ι] in
include hD in
/-- The invariant derivation differentiates the universal group matrix by right multiplication. -/
theorem hopfInvariantDerivation_matrixCoefficient (D : 𝔤) (i j : ι) :
    D.val (U i j) = ∑ l, U i l * algebraMap k H (hopfLieMatrix U D l j) := by
  let L := (TensorProduct.rid k H).toLinearMap.comp ((ε).toLinearMap.lTensor H)
  have hL (a : H) : L (Δ a) = a := by
    change TensorProduct.rid k H ((ε).toLinearMap.lTensor H (Δ a)) = a
    rw [show (ε).toLinearMap.lTensor H (Δ a) = (TensorProduct.rid k H).symm a from
      Coalgebra.lTensor_counit_comul a, LinearEquiv.apply_symm_apply]
  have h := congrArg L (D.prop (U i j))
  have hComul : Δ (U i j) = ∑ l, U i l ⊗ₜ[k] U l j := hD i j
  rw [hL, hComul, map_sum, map_sum] at h
  simpa only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lTensor_tmul,
    TensorProduct.rid_tmul, AlgHom.toLinearMap_apply, Derivation.coeFn_coe, hopfLieMatrix,
    Algebra.smul_def, mul_comm] using h

omit [DecidableEq ι] in
include hD in
private theorem hopfLieMatrix_comp_apply (D E : 𝔤) (i j : ι) :
    ε (D.val (E.val (U i j))) = (hopfLieMatrix U D * hopfLieMatrix U E) i j := by
  rw [hopfInvariantDerivation_matrixCoefficient U hD E i j, map_sum, map_sum, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro l _
  rw [D.val.leibniz, Derivation.map_algebraMap, smul_zero, zero_add, Algebra.id.smul_eq_mul,
    map_mul, AlgHom.commutes, mul_comm]
  rfl

/-- The differentiated matrix representation preserves Lie brackets. -/
def hopfLieMatrixHom : 𝔤 →ₗ⁅k⁆ Matrix ι ι k where
  toFun := hopfLieMatrix U
  map_add' D E := by
    ext i j
    change ε (D.val (U i j) + E.val (U i j)) = ε (D.val (U i j)) + ε (E.val (U i j))
    exact map_add ε _ _
  map_smul' r D := by
    ext i j
    change ε (r • D.val (U i j)) = r • ε (D.val (U i j))
    exact map_smul ε _ _
  map_lie' {D E} := by
    ext i j
    change ε (D.val (E.val (U i j)) - E.val (D.val (U i j))) =
      (hopfLieMatrix U D * hopfLieMatrix U E - hopfLieMatrix U E * hopfLieMatrix U D) i j
    rw [map_sub, Matrix.sub_apply, hopfLieMatrix_comp_apply U hD, hopfLieMatrix_comp_apply U hD]

/-- A representation whose coefficients generate the coordinate algebra has faithful differential. -/
theorem hopfLieMatrixHom_injective
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U ij.1 ij.2) = ⊤) :
    Function.Injective (hopfLieMatrixHom U hD) := by
  change Function.Injective (hopfLieMatrixHom U hD).toLinearMap
  apply (injective_iff_map_eq_zero (hopfLieMatrixHom U hD).toLinearMap).mpr
  intro D h
  change hopfLieMatrix U D = 0 at h
  apply Subtype.ext
  apply Derivation.ext_of_adjoin_eq_top _ hGen
  rintro _ ⟨⟨i, j⟩, rfl⟩
  rw [hopfInvariantDerivation_matrixCoefficient U hD, h]
  simp

end WideE
