import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-! Restrict a Hopf structure along a split algebra inclusion stable under
the comultiplication and antipode. -/

noncomputable section

open scoped TensorProduct

namespace WideE

section Tensor

variable {k A B C D : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k D]

local notation "M" => Algebra.TensorProduct.map (S := k)

private theorem tensorMap_leftInverse
    (i : A →ₐ[k] C) (r : C →ₐ[k] A) (j : B →ₐ[k] D) (s : D →ₐ[k] B)
    (hi : Function.LeftInverse r i) (hj : Function.LeftInverse s j) :
    Function.LeftInverse (M r s) (M i j) := by
  intro z
  change ((M r s).comp (M i j)) z = z
  rw [← Algebra.TensorProduct.map_comp, show r.comp i = AlgHom.id k A from AlgHom.ext hi,
    show s.comp j = AlgHom.id k B from AlgHom.ext hj, Algebra.TensorProduct.map_id]
  rfl

private theorem tensorAssoc_map (j : A →ₐ[k] B) (z : (A ⊗[k] A) ⊗[k] A) :
    M j (M j j) (Algebra.TensorProduct.assoc k A A A z) =
      Algebra.TensorProduct.assoc k B B B (M (M j j) j z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
    | tmul a b => rfl

end Tensor

section Restriction

variable {k J H : Type*} [CommRing k] [CommRing J] [CommRing H]
  [Algebra k J] [HopfAlgebra k H]
  (j : J →ₐ[k] H) (r : H →ₐ[k] J)

local notation "M" => Algebra.TensorProduct.map (S := k)
local notation "ΔH" => (Bialgebra.comulAlgHom k H)
local notation "εH" => (Bialgebra.counitAlgHom k H)
local notation "SH" => (HopfAlgebra.antipode (R := k) (A := H))

private def restrictedComul : J →ₐ[k] J ⊗[k] J :=
  (M r r).comp ((ΔH).comp j)

private def restrictedCounit : J →ₐ[k] k := (εH).comp j

private def restrictedAntipode : J →ₗ[k] J := r.toLinearMap.comp ((SH).comp j.toLinearMap)

local notation "ΔJ" => (restrictedComul j r)
local notation "εJ" => (restrictedCounit j)
local notation "SJ" => (restrictedAntipode j r)

variable (hj : Function.LeftInverse r j)
  (hΔ : ∀ x : J, Algebra.TensorProduct.map (S := k) j j (restrictedComul j r x) =
    Bialgebra.comulAlgHom k H (j x))
  (hS : ∀ x : J, j (restrictedAntipode j r x) = HopfAlgebra.antipode (R := k) (A := H) (j x))

include hj hΔ in
private theorem restricted_coassoc (x : J) :
    Algebra.TensorProduct.assoc k J J J (M ΔJ (AlgHom.id k J) (ΔJ x)) =
      M (AlgHom.id k J) ΔJ (ΔJ x) := by
  have hmap : (M j j).comp ΔJ = (ΔH).comp j := AlgHom.ext hΔ
  have hLeft (z : J ⊗[k] J) : M (M j j) j (M ΔJ (AlgHom.id k J) z) =
      M ΔH (AlgHom.id k H) (M j j z) := by
    change ((M (M j j) j).comp (M ΔJ (AlgHom.id k J))) z =
      ((M ΔH (AlgHom.id k H)).comp (M j j)) z
    simp only [← Algebra.TensorProduct.map_comp, hmap, AlgHom.comp_id, AlgHom.id_comp]
  have hRight (z : J ⊗[k] J) : M j (M j j) (M (AlgHom.id k J) ΔJ z) =
      M (AlgHom.id k H) ΔH (M j j z) := by
    change ((M j (M j j)).comp (M (AlgHom.id k J) ΔJ)) z =
      ((M (AlgHom.id k H) ΔH).comp (M j j)) z
    simp only [← Algebra.TensorProduct.map_comp, hmap, AlgHom.comp_id, AlgHom.id_comp]
  apply (tensorMap_leftInverse j r (M j j) (M r r) hj
    (tensorMap_leftInverse j r j r hj hj)).injective
  rw [tensorAssoc_map, hLeft, hRight, hΔ]
  exact Coalgebra.coassoc_apply (R := k) (j x)

include hj hΔ in
private theorem restricted_leftCounit (x : J) :
    M εJ (AlgHom.id k J) (ΔJ x) = (Algebra.TensorProduct.lid k J).symm x := by
  have hmap (z : J ⊗[k] J) :
      M (AlgHom.id k k) j (M εJ (AlgHom.id k J) z) = M εH (AlgHom.id k H) (M j j z) := by
    change ((M (AlgHom.id k k) j).comp (M εJ (AlgHom.id k J))) z =
      ((M εH (AlgHom.id k H)).comp (M j j)) z
    simp only [← Algebra.TensorProduct.map_comp, AlgHom.id_comp, AlgHom.comp_id, restrictedCounit]
  apply (tensorMap_leftInverse (AlgHom.id k k) (AlgHom.id k k) j r (fun _ => rfl) hj).injective
  rw [hmap, hΔ, Algebra.TensorProduct.lid_symm_apply, Algebra.TensorProduct.map_tmul]
  exact Coalgebra.rTensor_counit_comul (R := k) (j x)

include hj hΔ in
private theorem restricted_rightCounit (x : J) :
    M (AlgHom.id k J) εJ (ΔJ x) = (Algebra.TensorProduct.rid k k J).symm x := by
  have hmap (z : J ⊗[k] J) :
      M j (AlgHom.id k k) (M (AlgHom.id k J) εJ z) = M (AlgHom.id k H) εH (M j j z) := by
    change ((M j (AlgHom.id k k)).comp (M (AlgHom.id k J) εJ)) z =
      ((M (AlgHom.id k H) εH).comp (M j j)) z
    simp only [← Algebra.TensorProduct.map_comp, AlgHom.id_comp, AlgHom.comp_id, restrictedCounit]
  apply (tensorMap_leftInverse j r (AlgHom.id k k) (AlgHom.id k k) hj (fun _ => rfl)).injective
  rw [hmap, hΔ, Algebra.TensorProduct.rid_symm_apply, Algebra.TensorProduct.map_tmul]
  exact Coalgebra.lTensor_counit_comul (R := k) (j x)

include hS in
private theorem restricted_antipode_mul (z : J ⊗[k] J) :
    j (LinearMap.mul' k J ((SJ).rTensor J z)) =
      LinearMap.mul' k H ((SH).rTensor H (M j j z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    simp only [LinearMap.rTensor_tmul, LinearMap.mul'_apply, map_mul, Algebra.TensorProduct.map_tmul, hS]

include hS in
private theorem restricted_mul_antipode (z : J ⊗[k] J) :
    j (LinearMap.mul' k J ((SJ).lTensor J z)) =
      LinearMap.mul' k H ((SH).lTensor H (M j j z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    simp only [LinearMap.lTensor_tmul, LinearMap.mul'_apply, map_mul, Algebra.TensorProduct.map_tmul, hS]

/-- The induced Hopf algebra on a split subalgebra that is stable under
the original comultiplication and antipode. -/
def restrictHopfAlgebra : HopfAlgebra k J where
  toBialgebra := Bialgebra.ofAlgHom ΔJ εJ (AlgHom.ext (restricted_coassoc j r hj hΔ))
    (AlgHom.ext (restricted_leftCounit j r hj hΔ)) (AlgHom.ext (restricted_rightCounit j r hj hΔ))
  antipode := SJ
  mul_antipode_rTensor_comul := by
    apply LinearMap.ext
    intro x
    apply hj.injective
    change j (LinearMap.mul' k J ((SJ).rTensor J (ΔJ x))) =
      j (algebraMap k J (εJ x))
    rw [restricted_antipode_mul j r hS, hΔ, AlgHom.commutes]
    exact HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) (j x)
  mul_antipode_lTensor_comul := by
    apply LinearMap.ext
    intro x
    apply hj.injective
    change j (LinearMap.mul' k J ((SJ).lTensor J (ΔJ x))) =
      j (algebraMap k J (εJ x))
    rw [restricted_mul_antipode j r hS, hΔ, AlgHom.commutes]
    exact HopfAlgebra.mul_antipode_lTensor_comul_apply (R := k) (j x)

end Restriction

end WideE
