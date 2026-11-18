import WideE.GaloisInflation
import WideE.HopfAntipode
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Matrix.Basic

/-! The group of points of a commutative Hopf algebra and its matrix representations. -/

noncomputable section

open scoped TensorProduct Matrix

namespace WideE

variable {k H A : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H] [CommRing A] [Algebra k A]

local notation "Δ" => (Bialgebra.comulAlgHom k H)
local notation "σ" => (HopfAlgebra.antipode (R := k) (A := H))
local notation "M" => Algebra.TensorProduct.map (S := k)

theorem hopfPointMul_assoc (p q r : H →ₐ[k] A) :
    hopfPointMul (hopfPointMul p q) r = hopfPointMul p (hopfPointMul q r) := by
  have hL : tensorPoint (hopfPointMul p q) r =
      (tensorPoint (tensorPoint p q) r).comp (M Δ (AlgHom.id k H)) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [tensorPoint_tmul, hopfPointMul, AlgHom.comp_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have hR : tensorPoint p (hopfPointMul q r) =
      (tensorPoint p (tensorPoint q r)).comp (M (AlgHom.id k H) Δ) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [tensorPoint_tmul, hopfPointMul, AlgHom.comp_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  apply AlgHom.ext
  intro a
  change tensorPoint (hopfPointMul p q) r (Δ a) = tensorPoint p (hopfPointMul q r) (Δ a)
  rw [hL, hR, AlgHom.comp_apply, AlgHom.comp_apply, tensorPoint_assoc]
  exact congrArg (tensorPoint p (tensorPoint q r)) (Coalgebra.coassoc_apply (R := k) a)

@[simp] theorem hopfPointMul_inverse_left (p : H →ₐ[k] A) :
    hopfPointMul (p.comp (hopfAntipodeAlgHom k H)) p = hopfPointOne := by
  have h (z : H ⊗[k] H) : tensorPoint (p.comp (hopfAntipodeAlgHom k H)) p z =
      p (LinearMap.mul' k H ((σ).rTensor H z)) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      simp only [tensorPoint_tmul, AlgHom.comp_apply, hopfAntipodeAlgHom_apply,
        LinearMap.rTensor_tmul, LinearMap.mul'_apply, map_mul]
  apply AlgHom.ext
  intro a
  change tensorPoint (p.comp (hopfAntipodeAlgHom k H)) p (Δ a) = hopfPointOne a
  rw [h]
  change p (LinearMap.mul' k H ((σ).rTensor H (Coalgebra.comul (R := k) a))) = hopfPointOne a
  rw [HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]
  rfl

/-- Convolution gives the affine group law on algebra-valued points. -/
def hopfPointGroup : Group (H →ₐ[k] A) := by
  letI : Mul (H →ₐ[k] A) := ⟨hopfPointMul⟩
  letI : One (H →ₐ[k] A) := ⟨hopfPointOne⟩
  letI : Inv (H →ₐ[k] A) := ⟨fun p => p.comp (hopfAntipodeAlgHom k H)⟩
  exact Group.ofLeftAxioms hopfPointMul_assoc hopfPointMul_one_left hopfPointMul_inverse_left

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A matrix corepresentation evaluates to a homomorphism on affine group points. -/
def hopfPointMatrix (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0) :
    letI := hopfPointGroup (k := k) (H := H) (A := A)
    (H →ₐ[k] A) →* (Matrix ι ι A)ˣ := by
  letI := hopfPointGroup (k := k) (H := H) (A := A)
  refine { toFun := fun p => U.map p.toRingHom.mapMatrix.toMonoidHom, map_one' := ?_, map_mul' := ?_ }
  · apply Units.ext
    ext i j
    change algebraMap k A (Coalgebra.counit (R := k) (U.val i j)) = (1 : Matrix ι ι A) i j
    rw [he]
    simp only [apply_ite (algebraMap k A), map_one, map_zero, Matrix.one_apply]
  · intro p q
    apply Units.ext
    ext i j
    change tensorPoint p q (Coalgebra.comul (R := k) (U.val i j)) = ∑ l, p (U.val i l) * q (U.val l j)
    rw [hD, map_sum]
    simp only [tensorPoint_tmul]

@[simp] theorem hopfPointMatrix_apply_val (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (p : H →ₐ[k] A) : (hopfPointMatrix U hD he p).val = U.val.map p := rfl

end WideE
