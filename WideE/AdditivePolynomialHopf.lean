import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.Tactic.Abel

/-! The coordinate Hopf algebra of the additive group. -/

open scoped TensorProduct

noncomputable section

namespace WideE

variable (k : Type*) [CommRing k]

local notation "P" => Polynomial k

private def additiveDelta : P →ₐ[k] P ⊗[k] P :=
  Polynomial.aeval ((1 : P) ⊗ₜ[k] (Polynomial.X : P) + (Polynomial.X : P) ⊗ₜ[k] (1 : P))

private def additiveCounit : P →ₐ[k] k := Polynomial.aeval (0 : k)

private def additiveAntipode : P →ₐ[k] P := Polynomial.aeval (-(Polynomial.X : P))

private def additiveBialgebra : Bialgebra k P :=
  Bialgebra.ofAlgHom (additiveDelta k) (additiveCounit k)
    (by
      apply Polynomial.algHom_ext
      simp [additiveDelta, TensorProduct.add_tmul, TensorProduct.tmul_add, Algebra.TensorProduct.one_def]
      abel)
    (by
      apply Polynomial.algHom_ext
      simp [additiveDelta, additiveCounit])
    (by
      apply Polynomial.algHom_ext
      simp [additiveDelta, additiveCounit])

private def polynomialTensorMultiply : P ⊗[k] P →ₐ[k] P :=
  Algebra.TensorProduct.lift (AlgHom.id k P) (AlgHom.id k P) (fun _ _ => Commute.all _ _)

private theorem additiveAntipodeContract (onLeft : Bool) :
    (polynomialTensorMultiply k).comp
        ((if onLeft then Algebra.TensorProduct.map (additiveAntipode k) (AlgHom.id k P)
          else Algebra.TensorProduct.map (AlgHom.id k P) (additiveAntipode k)).comp (additiveDelta k)) =
      (Algebra.ofId k P).comp (additiveCounit k) := by
  apply Polynomial.algHom_ext
  cases onLeft <;> simp [polynomialTensorMultiply, additiveDelta, additiveCounit, additiveAntipode]

private theorem additiveAntipodeRightLinear :
    LinearMap.mul' k P ∘ₗ (additiveAntipode k).toLinearMap.rTensor P =
      ((polynomialTensorMultiply k).comp
        (Algebra.TensorProduct.map (additiveAntipode k) (AlgHom.id k P))).toLinearMap := by
  apply TensorProduct.ext'
  intro x y
  simp [polynomialTensorMultiply]

private theorem additiveAntipodeLeftLinear :
    LinearMap.mul' k P ∘ₗ (additiveAntipode k).toLinearMap.lTensor P =
      ((polynomialTensorMultiply k).comp
        (Algebra.TensorProduct.map (AlgHom.id k P) (additiveAntipode k))).toLinearMap := by
  apply TensorProduct.ext'
  intro x y
  simp [polynomialTensorMultiply]

/-- The ordinary additive coordinate has coproduct `1 ⊗ X + X ⊗ 1`. -/
def additivePolynomialHopf : HopfAlgebra k P where
  toBialgebra := additiveBialgebra k
  antipode := (additiveAntipode k).toLinearMap
  mul_antipode_rTensor_comul := by
    apply LinearMap.ext
    intro x
    change (LinearMap.mul' k P ∘ₗ (additiveAntipode k).toLinearMap.rTensor P) (additiveDelta k x) =
      algebraMap k P (additiveCounit k x)
    rw [additiveAntipodeRightLinear]
    exact DFunLike.congr_fun (additiveAntipodeContract k true) x
  mul_antipode_lTensor_comul := by
    apply LinearMap.ext
    intro x
    change (LinearMap.mul' k P ∘ₗ (additiveAntipode k).toLinearMap.lTensor P) (additiveDelta k x) =
      algebraMap k P (additiveCounit k x)
    rw [additiveAntipodeLeftLinear]
    exact DFunLike.congr_fun (additiveAntipodeContract k false) x

@[simp] theorem additivePolynomialHopf_comul_X :
    letI := additivePolynomialHopf k
    Bialgebra.comulAlgHom k P (Polynomial.X : P) =
      (1 : P) ⊗ₜ[k] (Polynomial.X : P) + (Polynomial.X : P) ⊗ₜ[k] (1 : P) :=
  Polynomial.aeval_X _

end WideE
