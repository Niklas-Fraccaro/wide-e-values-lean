import WideE.HopfCotangentBaseChange
import WideE.AdjointCentralizerTangent
import Mathlib.RingTheory.Bialgebra.Equiv

/-! Direct and iterated scalar extension of Hopf coordinates agree. -/

noncomputable section

open scoped TensorProduct
open StrictEUnit

namespace WideE

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 120000

variable {k F L H : Type*} [Field k] [Field F] [Field L] [CommRing H] [HopfAlgebra k H]
  [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]

local notation "H'" => (F ⊗[k] H)
local notation "A₂" => (L ⊗[F] H')
local notation "A₁" => (L ⊗[k] H)
local notation "e" => (Algebra.TensorProduct.cancelBaseChange k F L L H)

attribute [local instance] hopfScalarExtension

private theorem cancelBaseChange_symm_tensorSquare (a : L) (z : H ⊗[k] H) :
    TensorProduct.map (e).symm.toLinearEquiv.toLinearMap (e).symm.toLinearEquiv.toLinearMap
      ((algebraTensorBaseChangeEquiv L H H).symm (a ⊗ₜ[k] z)) =
    (algebraTensorBaseChangeEquiv L H' H').symm
      (a ⊗ₜ[F] (algebraTensorBaseChangeEquiv F H H).symm ((1 : F) ⊗ₜ[k] z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul x y =>
    simp only [algebraTensorBaseChangeEquiv_symm_tmul, TensorProduct.map_tmul,
      LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply,
      Algebra.TensorProduct.cancelBaseChange_symm_tmul]

/-- The iterated and direct scalar extensions are isomorphic as bialgebras. -/
def scalarExtendBialgCancelBaseChange : A₂ ≃ₐc[L] A₁ := by
  have hε (z : A₁) : Bialgebra.counitAlgHom L A₂ ((e).symm z) = Bialgebra.counitAlgHom L A₁ z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x =>
      rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul, hopfScalarExtension_counit_tmul,
        hopfScalarExtension_counit_tmul, hopfScalarExtension_counit_tmul, one_mul,
        IsScalarTower.algebraMap_apply k F L]
  have hΔ (z : A₁) : TensorProduct.map (e).symm.toLinearEquiv.toLinearMap (e).symm.toLinearEquiv.toLinearMap
      (Coalgebra.comul (R := L) z) = Coalgebra.comul (R := L) ((e).symm z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a h =>
      rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]
      change TensorProduct.map (e).symm.toLinearEquiv.toLinearMap (e).symm.toLinearEquiv.toLinearMap
          (baseChangeComul L (a ⊗ₜ[k] h)) =
        baseChangeComul L (a ⊗ₜ[F] ((1 : F) ⊗ₜ[k] h))
      rw [baseChangeComul_tmul, baseChangeComul_tmul, cancelBaseChange_symm_tensorSquare]
      rfl
  let d : A₁ ≃ₗc[L] A₂ :=
    { (e).symm.toLinearEquiv with
      counit_comp := LinearMap.ext hε
      map_comp_comul := LinearMap.ext hΔ }
  exact ({ d, (e).symm.toMulEquiv with } : A₁ ≃ₐc[L] A₂).symm

@[simp] theorem scalarExtendBialgCancelBaseChange_symm_tmul (a : L) (h : H) :
    (scalarExtendBialgCancelBaseChange (k := k) (F := F) (L := L) (H := H)).symm (a ⊗ₜ[k] h) =
      a ⊗ₜ[F] ((1 : F) ⊗ₜ[k] h) := rfl

@[simp] theorem scalarExtendBialgCancelBaseChange_tmul (a : L) (b : F) (h : H) :
    scalarExtendBialgCancelBaseChange (a ⊗ₜ[F] (b ⊗ₜ[k] h)) = (b • a) ⊗ₜ[k] h := rfl

theorem scalarExtendPoint_cancelBaseChange (p : H →ₐ[k] L) :
    (scalarExtendPoint (A := L) (scalarExtendPoint (A := F) p)).comp
        ((scalarExtendBialgCancelBaseChange (k := k) (F := F) (L := L) (H := H)).symm.toAlgEquiv.toAlgHom) =
      scalarExtendPoint (A := L) p := by
  apply scalarExtendPoint_ext
  intro h
  change scalarExtendPoint (A := L) (scalarExtendPoint (A := F) p)
    ((scalarExtendBialgCancelBaseChange (k := k) (F := F)).symm ((1 : L) ⊗ₜ[k] h)) =
      scalarExtendPoint (A := L) p ((1 : L) ⊗ₜ[k] h)
  simp only [scalarExtendBialgCancelBaseChange_symm_tmul, scalarExtendPoint_one_tmul]

theorem hopfLieVectorBaseChange_cancel (x : HopfLieVector k H L) :
    let E : A₁ →ₐc[L] A₂ :=
      (scalarExtendBialgCancelBaseChange (k := k) (F := F) (L := L) (H := H)).symm
    hopfLiePullback (E : A₁ →ₐ[L] A₂) (BialgHomClass.counitAlgHom_comp E)
        (hopfLieVectorBaseChange (F := L) (hopfLieVectorBaseChange (F := F) x)) =
      hopfLieVectorBaseChange (F := L) x := by
  intro E
  apply hopfLieVectorBaseChange_ext
  intro h
  have hE : (E : A₁ →ₐ[L] A₂) ((1 : L) ⊗ₜ[k] h) = (1 : L) ⊗ₜ[F] ((1 : F) ⊗ₜ[k] h) :=
    scalarExtendBialgCancelBaseChange_symm_tmul 1 h
  rw [hopfLiePullback_projection, hE]
  simp only [hopfLieVectorBaseChange_projection_tmul, one_smul]

end WideE
