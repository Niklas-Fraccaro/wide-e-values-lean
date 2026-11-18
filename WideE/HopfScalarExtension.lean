import WideE.HopfLieDerivation
import BialgebraBaseChangeLaws

/-! Scalar extension of commutative Hopf algebras and their infinitesimal points. -/

noncomputable section

open scoped TensorProduct
open StrictEUnit

namespace WideE

section Hopf

variable {k H : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  (A : Type*) [CommRing A] [Algebra k A]

private def baseChangeAntipode : A ⊗[k] H →ₗ[A] A ⊗[k] H :=
  (weightBaseChangeAlgHom A (hopfAntipodeAlgHom k H)).toLinearMap

@[simp] private theorem baseChangeAntipode_tmul (a : A) (h : H) :
    baseChangeAntipode A (a ⊗ₜ[k] h) = a ⊗ₜ[k] HopfAlgebra.antipode (R := k) h := by
  rw [baseChangeAntipode, AlgHom.toLinearMap_apply, weightBaseChangeAlgHom_tmul,
    hopfAntipodeAlgHom_apply]

private theorem mul_baseChangeAntipode_rTensor (a : A) (z : H ⊗[k] H) :
    LinearMap.mul' A (A ⊗[k] H) ((baseChangeAntipode A).rTensor (A ⊗[k] H)
      ((algebraTensorBaseChangeEquiv A H H).symm (a ⊗ₜ[k] z))) =
      a ⊗ₜ[k] LinearMap.mul' k H ((HopfAlgebra.antipode (R := k)).rTensor H z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul x y =>
    simp only [algebraTensorBaseChangeEquiv_symm_tmul, LinearMap.rTensor_tmul, baseChangeAntipode_tmul,
      LinearMap.mul'_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

private theorem mul_baseChangeAntipode_lTensor (a : A) (z : H ⊗[k] H) :
    LinearMap.mul' A (A ⊗[k] H) ((baseChangeAntipode A).lTensor (A ⊗[k] H)
      ((algebraTensorBaseChangeEquiv A H H).symm (a ⊗ₜ[k] z))) =
      a ⊗ₜ[k] LinearMap.mul' k H ((HopfAlgebra.antipode (R := k)).lTensor H z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul x y =>
    simp only [algebraTensorBaseChangeEquiv_symm_tmul, LinearMap.lTensor_tmul, baseChangeAntipode_tmul,
      LinearMap.mul'_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

private theorem baseChangeAntipode_at_counit (a : A) (h : H) :
    a ⊗ₜ[k] (algebraMap k H) (Coalgebra.counit (R := k) h) =
      algebraMap A (A ⊗[k] H) (baseChangeCounit A (a ⊗ₜ[k] h)) := by
  rw [baseChangeCounit_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id,
    RingHom.id_apply, Algebra.algebraMap_eq_smul_one (R := k), TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]

/-- The scalar extension of an affine Hopf algebra, using Hatsuwr's bialgebra laws. -/
def hopfScalarExtension : HopfAlgebra A (A ⊗[k] H) where
  toBialgebra := baseChangeBialgebra A
  antipode := baseChangeAntipode A
  mul_antipode_rTensor_comul := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a h =>
      change LinearMap.mul' A (A ⊗[k] H) ((baseChangeAntipode A).rTensor (A ⊗[k] H)
        (baseChangeComul A (a ⊗ₜ[k] h))) = algebraMap A (A ⊗[k] H) (baseChangeCounit A (a ⊗ₜ[k] h))
      rw [baseChangeComul_tmul, mul_baseChangeAntipode_rTensor,
        HopfAlgebra.mul_antipode_rTensor_comul_apply, baseChangeAntipode_at_counit]
  mul_antipode_lTensor_comul := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a h =>
      change LinearMap.mul' A (A ⊗[k] H) ((baseChangeAntipode A).lTensor (A ⊗[k] H)
        (baseChangeComul A (a ⊗ₜ[k] h))) = algebraMap A (A ⊗[k] H) (baseChangeCounit A (a ⊗ₜ[k] h))
      rw [baseChangeComul_tmul, mul_baseChangeAntipode_lTensor,
        HopfAlgebra.mul_antipode_lTensor_comul_apply, baseChangeAntipode_at_counit]

end Hopf

section Points

variable {k H A B : Type*} [Field k] [CommRing H] [Algebra k H] [CommRing A] [Algebra k A]
  [CommRing B] [Algebra A B] [Algebra k B] [IsScalarTower k A B]

/-- A point with target an `A`-algebra extends to the scalar-extended coordinate algebra. -/
def scalarExtendPoint (p : H →ₐ[k] B) : A ⊗[k] H →ₐ[A] B :=
  Algebra.TensorProduct.lift (Algebra.ofId A B) p fun _ _ => Commute.all _ _

@[simp] theorem scalarExtendPoint_tmul (p : H →ₐ[k] B) (a : A) (h : H) :
    scalarExtendPoint p (a ⊗ₜ[k] h) = algebraMap A B a * p h := rfl

@[simp] theorem scalarExtendPoint_one_tmul (p : H →ₐ[k] B) (h : H) :
    scalarExtendPoint (A := A) p ((1 : A) ⊗ₜ[k] h) = p h := by
  rw [scalarExtendPoint_tmul, map_one, one_mul]

end Points

end WideE
