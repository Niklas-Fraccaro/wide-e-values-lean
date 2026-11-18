import Mathlib.RingTheory.HopfAlgebra.Basic

/-! The regular translation chart of a commutative Hopf algebra and its antipode. -/

noncomputable section

open scoped TensorProduct

namespace WideE

variable {k H : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H]

local notation "D" => (Coalgebra.comul (R := k) (A := H))
local notation "ε" => (Coalgebra.counit (R := k) (A := H))
local notation "σ" => (HopfAlgebra.antipode (R := k) (A := H))

private def translationLinear (d : H →ₗ[k] H ⊗[k] H) : H ⊗[k] H →ₗ[k] H ⊗[k] H :=
  (LinearMap.mul' k (H ⊗[k] H)).comp
    (TensorProduct.map (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] H).toLinearMap d)

private theorem translationLinear_tmul (d : H →ₗ[k] H ⊗[k] H) (a b : H) :
    translationLinear d (a ⊗ₜ[k] b) = (a ⊗ₜ[k] 1) * d b := rfl

private theorem translationLinear_left_mul (d : H →ₗ[k] H ⊗[k] H) (a : H) (z : H ⊗[k] H) :
    translationLinear d ((a ⊗ₜ[k] 1) * z) = (a ⊗ₜ[k] 1) * translationLinear d z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]
  | tmul x y =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, translationLinear_tmul, ← mul_assoc]

private theorem translationLinear_comul (f g : H →ₗ[k] H) (a : H) :
    translationLinear ((g.rTensor H).comp D) (f.rTensor H (D a)) =
      (((LinearMap.mul' k H).comp (TensorProduct.map f g)).rTensor H) ((D).rTensor H (D a)) := by
  have hCoassoc : (D).rTensor H (D a) =
      (TensorProduct.assoc k H H H).symm ((D).lTensor H (D a)) := by
    rw [← Coalgebra.coassoc_apply (R := k), LinearEquiv.symm_apply_apply]
  rw [hCoassoc]
  induction D a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    simp only [LinearMap.rTensor_tmul, translationLinear_tmul, LinearMap.comp_apply, LinearMap.lTensor_tmul]
    induction D y using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [TensorProduct.tmul_add, map_add, mul_add, hz, hw]
    | tmul b c => simp only [TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, LinearMap.comp_apply, TensorProduct.map_tmul,
        LinearMap.mul'_apply]

private theorem translationLinear_counit (f g : H →ₗ[k] H)
    (h : ((LinearMap.mul' k H).comp (TensorProduct.map f g)).comp D = (Algebra.linearMap k H).comp ε)
    (a : H) : translationLinear ((g.rTensor H).comp D) (f.rTensor H (D a)) = 1 ⊗ₜ[k] a := by
  rw [translationLinear_comul]
  have hRTensor := congrArg (LinearMap.rTensor H) h
  simp only [LinearMap.rTensor_comp] at hRTensor
  have hA := LinearMap.congr_fun hRTensor (D a)
  simp only [LinearMap.comp_apply] at hA
  rw [LinearMap.rTensor_comp, LinearMap.comp_apply, hA, Coalgebra.rTensor_counit_comul,
    LinearMap.rTensor_tmul,
    Algebra.linearMap_apply, map_one]

private theorem translationLinear_antipode_comul (a : H) :
    translationLinear D ((σ).rTensor H (D a)) = 1 ⊗ₜ[k] a := by
  have h := translationLinear_counit σ (LinearMap.id : H →ₗ[k] H)
    (HopfAlgebra.mul_antipode_rTensor_comul (R := k) (A := H)) a
  rwa [LinearMap.rTensor_id, LinearMap.id_comp] at h

private theorem translationLinear_comul_antipode (a : H) :
    translationLinear (((σ).rTensor H).comp D) (D a) = 1 ⊗ₜ[k] a := by
  have h := translationLinear_counit (LinearMap.id : H →ₗ[k] H) σ
    (HopfAlgebra.mul_antipode_lTensor_comul (R := k) (A := H)) a
  rwa [LinearMap.rTensor_id, LinearMap.id_apply] at h

private def translationAlgHom : H ⊗[k] H →ₐ[k] H ⊗[k] H :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft (Bialgebra.comulAlgHom k H)
    (fun _ _ => Commute.all _ _)

private theorem translationAlgHom_toLinearMap :
    (translationAlgHom (k := k) (H := H)).toLinearMap = translationLinear D := by
  ext a b
  rfl

variable (k H) in
/-- The change of coordinates `(g, h) ↦ (g, gh)` on the affine group. -/
def hopfTranslationChart : H ⊗[k] H ≃ₐ[k] H ⊗[k] H where
  toFun := translationAlgHom
  invFun := translationLinear (((σ).rTensor H).comp D)
  left_inv z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
      change translationLinear (((σ).rTensor H).comp D) ((translationAlgHom (k := k)).toLinearMap
        (a ⊗ₜ[k] b)) = a ⊗ₜ[k] b
      rw [translationAlgHom_toLinearMap, translationLinear_tmul, translationLinear_left_mul,
        translationLinear_comul_antipode, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  right_inv z := by
    change (translationAlgHom (k := k)).toLinearMap (translationLinear (((σ).rTensor H).comp D) z) = z
    rw [translationAlgHom_toLinearMap]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
      rw [translationLinear_tmul, translationLinear_left_mul, LinearMap.comp_apply,
        translationLinear_antipode_comul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  map_mul' := map_mul translationAlgHom
  map_add' := map_add translationAlgHom
  commutes' := AlgHom.commutes translationAlgHom

private theorem hopfTranslationChart_symm_tmul (a b : H) :
    (hopfTranslationChart k H).symm (a ⊗ₜ[k] b) =
      (a ⊗ₜ[k] 1) * (σ).rTensor H (D b) := rfl

variable (k H) in
/-- Inversion on an affine group, viewed as a map of coordinate algebras. -/
def hopfAntipodeAlgHom : H →ₐ[k] H :=
  (Algebra.TensorProduct.rid k k H).toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id k H) (Bialgebra.counitAlgHom k H)).comp
      ((hopfTranslationChart k H).symm.toAlgHom.comp Algebra.TensorProduct.includeRight))

@[simp] theorem hopfAntipodeAlgHom_apply (a : H) : hopfAntipodeAlgHom k H a = σ a := by
  have h (z : H ⊗[k] H) :
      (Algebra.TensorProduct.rid k k H)
        (Algebra.TensorProduct.map (AlgHom.id k H) (Bialgebra.counitAlgHom k H) ((σ).rTensor H z)) =
        σ (TensorProduct.rid k H ((ε).lTensor H z)) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b c =>
      simp only [LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.rid_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_smul]
      rfl
  change (Algebra.TensorProduct.rid k k H)
    (Algebra.TensorProduct.map (AlgHom.id k H) (Bialgebra.counitAlgHom k H)
      ((hopfTranslationChart k H).symm (1 ⊗ₜ[k] a))) = _
  rw [hopfTranslationChart_symm_tmul, ← Algebra.TensorProduct.one_def, one_mul, h,
    Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul]

@[simp] theorem hopfAntipodeAlgHom_toLinearMap :
    (hopfAntipodeAlgHom k H).toLinearMap = (σ) := LinearMap.ext hopfAntipodeAlgHom_apply

end WideE
