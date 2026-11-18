import WideE.HopfPointGroup
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.Ring

/-! The derivative of a product of group morphisms at the identity. -/

noncomputable section

open scoped TensorProduct

namespace WideE

variable {k H A : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing A] [Algebra k A]

local notation "ε" => Bialgebra.counitAlgHom k H
local notation "Δ" => Bialgebra.comulAlgHom k H

/-- When both factors specialize to the identity, differentiation of their
product adds their evaluated derivatives. -/
theorem derivative_hopfPointMul_at_identity (D : Derivation k A A) (q : A →ₐ[k] k)
    (f g : H →ₐ[k] A) (hf : q.comp f = ε) (hg : q.comp g = ε) (a : H) :
    q (D (hopfPointMul f g a)) = q (D (f a)) + q (D (g a)) := by
  let u := q.toLinearMap.comp (D.toLinearMap.comp f.toLinearMap)
  let v := q.toLinearMap.comp (D.toLinearMap.comp g.toLinearMap)
  have hF (x : H) : q (f x) = ε x := DFunLike.congr_fun hf x
  have hG (x : H) : q (g x) = ε x := DFunLike.congr_fun hg x
  have h (z : H ⊗[k] H) :
      q (D (tensorPoint f g z)) =
        u (TensorProduct.rid k H ((ε).toLinearMap.lTensor H z)) +
          v (TensorProduct.lid k H ((ε).toLinearMap.rTensor H z)) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht =>
      simp only [map_add, hs, ht, add_add_add_comm]
    | tmul a b =>
      rw [tensorPoint_tmul, D.leibniz, Algebra.id.smul_eq_mul, Algebra.id.smul_eq_mul,
        map_add, map_mul, map_mul, hF, hG]
      simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.rid_tmul,
        TensorProduct.lid_tmul, AlgHom.toLinearMap_apply, map_smul, smul_eq_mul, add_comm]
      rfl
  change q (D (tensorPoint f g (Δ a))) = _
  rw [h, show (ε).toLinearMap.lTensor H (Δ a) = (TensorProduct.rid k H).symm a
    from Coalgebra.lTensor_counit_comul a,
    show (ε).toLinearMap.rTensor H (Δ a) = (TensorProduct.lid k H).symm a
      from Coalgebra.rTensor_counit_comul a,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- The ordered product of a list of algebra-valued group points. -/
def hopfPointListProduct (l : List (H →ₐ[k] A)) : H →ₐ[k] A :=
  letI : Group (H →ₐ[k] A) := hopfPointGroup
  l.prod

@[simp]
theorem hopfPointListProduct_nil :
    hopfPointListProduct ([] : List (H →ₐ[k] A)) = hopfPointOne := rfl

@[simp]
theorem hopfPointListProduct_cons (p : H →ₐ[k] A) (l : List (H →ₐ[k] A)) :
    hopfPointListProduct (p :: l) = hopfPointMul p (hopfPointListProduct l) := rfl

@[simp]
theorem hopfPointListProduct_append (l m : List (H →ₐ[k] A)) :
    hopfPointListProduct (l ++ m) = hopfPointMul (hopfPointListProduct l) (hopfPointListProduct m) := by
  letI : Group (H →ₐ[k] A) := hopfPointGroup
  exact List.prod_append

/-- The ordered product specializes to the identity if every factor does. -/
theorem hopfPointListProduct_at_identity (q : A →ₐ[k] k) (l : List (H →ₐ[k] A))
    (hl : ∀ p ∈ l, q.comp p = ε) :
    q.comp (hopfPointListProduct l) = ε := by
  induction l with
  | nil => exact hopfPointOne_postcompose q
  | cons p l ih =>
    rw [hopfPointListProduct_cons, hopfPointMul_postcompose, hl p List.mem_cons_self,
      ih (fun f hf => hl f (List.mem_cons_of_mem _ hf))]
    exact hopfPointMul_one_left (hopfPointOne : H →ₐ[k] k)

/-- The differential of the ordered product at the identity is the sum
of the differentials of its factors. -/
theorem derivative_hopfPointListProduct_at_identity (D : Derivation k A A) (q : A →ₐ[k] k)
    (l : List (H →ₐ[k] A)) (hl : ∀ p ∈ l, q.comp p = ε) (a : H) :
    q (D (hopfPointListProduct l a)) = (l.map (fun p => q (D (p a)))).sum := by
  induction l with
  | nil =>
    change q (D (algebraMap k A (ε a))) = 0
    rw [D.map_algebraMap, map_zero]
  | cons p l ih =>
    have ht : ∀ f ∈ l, q.comp f = ε := fun f hf => hl f (List.mem_cons_of_mem _ hf)
    rw [hopfPointListProduct_cons,
      derivative_hopfPointMul_at_identity D q p (hopfPointListProduct l)
        (hl p List.mem_cons_self) (hopfPointListProduct_at_identity q l ht) a,
      ih ht, List.map_cons, List.sum_cons]

end WideE
