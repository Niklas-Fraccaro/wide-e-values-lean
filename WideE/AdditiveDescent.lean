import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.Abel

/-! The first additive Amitsur equation for an affine faithfully flat cover. -/

open scoped TensorProduct

noncomputable section

namespace WideE

set_option synthInstance.maxHeartbeats 80000

variable (B S : Type*) [CommRing B] [CommRing S] [Algebra B S]

local notation "T2" => S ⊗[B] S
local notation "T3" => (S ⊗[B] S) ⊗[B] S

/-- Difference of the two restrictions of an additive section. -/
def additiveDescentDifference : S →ₗ[B] T2 :=
  (Algebra.TensorProduct.includeRight : S →ₐ[B] T2).toLinearMap -
    (Algebra.TensorProduct.includeLeft : S →ₐ[B] T2).toLinearMap

@[simp] theorem additiveDescentDifference_apply (x : S) :
    additiveDescentDifference B S x = 1 ⊗ₜ[B] x - x ⊗ₜ[B] 1 := rfl

/-- Alternating restrictions to the triple overlap. -/
def additiveDescentCocycle : T2 →ₗ[B] T3 :=
  ((Algebra.TensorProduct.assoc B S S S).symm.toAlgHom.comp
    (Algebra.TensorProduct.includeRight : T2 →ₐ[B] S ⊗[B] T2)).toLinearMap -
    (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : S →ₐ[B] T2)
      (AlgHom.id B S)).toLinearMap +
    (Algebra.TensorProduct.includeLeft : T2 →ₐ[B] T3).toLinearMap

@[simp] theorem additiveDescentCocycle_tmul (x y : S) :
    additiveDescentCocycle B S (x ⊗ₜ[B] y) =
      (1 ⊗ₜ[B] x) ⊗ₜ[B] y - (x ⊗ₜ[B] 1) ⊗ₜ[B] y + (x ⊗ₜ[B] y) ⊗ₜ[B] 1 := rfl

private theorem additiveDescent_comp :
    (additiveDescentCocycle B S).comp (additiveDescentDifference B S) = 0 := by
  apply LinearMap.ext
  intro x
  simp

private def multiplyFirstTwo : S ⊗[B] T2 →ₗ[B] T2 :=
  (TensorProduct.map (LinearMap.mul' B S) (LinearMap.id : S →ₗ[B] S)).comp
    (TensorProduct.assoc B S S S).symm.toLinearMap

@[simp] private theorem multiplyFirstTwo_tmul (a x y : S) :
    multiplyFirstTwo B S (a ⊗ₜ[B] (x ⊗ₜ[B] y)) = (a * x) ⊗ₜ[B] y := rfl

private def multiplyFirstTwoTriple : S ⊗[B] T3 →ₗ[B] S ⊗[B] T2 :=
  (TensorProduct.map (LinearMap.mul' B S) (LinearMap.id : T2 →ₗ[B] T2)).comp
    ((TensorProduct.assoc B S S T2).symm.toLinearMap.comp
      ((TensorProduct.assoc B S S S).toLinearMap.lTensor S))

@[simp] private theorem multiplyFirstTwoTriple_tmul (a x y z : S) :
    multiplyFirstTwoTriple B S (a ⊗ₜ[B] ((x ⊗ₜ[B] y) ⊗ₜ[B] z)) =
      (a * x) ⊗ₜ[B] (y ⊗ₜ[B] z) := rfl

private theorem additiveDescent_contraction :
    ((additiveDescentDifference B S).lTensor S).comp (multiplyFirstTwo B S) +
      (multiplyFirstTwoTriple B S).comp ((additiveDescentCocycle B S).lTensor S) =
        (LinearMap.id : S ⊗[B] T2 →ₗ[B] S ⊗[B] T2) := by
  apply TensorProduct.ext'
  intro a x
  induction x using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, LinearMap.map_zero]
  | add x y hx hy =>
    rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
  | tmul x y =>
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      multiplyFirstTwo_tmul, multiplyFirstTwoTriple_tmul, LinearMap.lTensor_tmul,
      additiveDescentDifference_apply, additiveDescentCocycle_tmul, TensorProduct.tmul_add,
      TensorProduct.tmul_sub, map_add, map_sub, mul_one]
    abel

/-- Additive cocycles on a faithfully flat affine cover are differences of
elements of the cover algebra. -/
theorem additiveDescent_exact [Module.FaithfullyFlat B S] :
    Function.Exact (additiveDescentDifference B S) (additiveDescentCocycle B S) := by
  apply (Module.FaithfullyFlat.lTensor_exact_iff_exact B S
    (additiveDescentDifference B S) (additiveDescentCocycle B S)).mp
  intro x
  constructor
  · intro hx
    refine ⟨multiplyFirstTwo B S x, ?_⟩
    have h := congrArg (fun f : S ⊗[B] T2 →ₗ[B] S ⊗[B] T2 => f x)
      (additiveDescent_contraction B S)
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, hx, map_zero,
      add_zero] using h
  · rintro ⟨y, rfl⟩
    rw [← LinearMap.lTensor_comp_apply, additiveDescent_comp]
    simp

/-- The additive cocycle equation written on the original cover. -/
theorem exists_additiveDescentPrimitive [Module.FaithfullyFlat B S] (a : T2)
    (ha : additiveDescentCocycle B S a = 0) :
    ∃ s : S, 1 ⊗ₜ[B] s - s ⊗ₜ[B] 1 = a :=
  (additiveDescent_exact B S a).mp ha

end WideE
