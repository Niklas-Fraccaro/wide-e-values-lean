import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-! A constant algebra tensored with the ring of a principal open gives the
same localization of the constant algebra over the original base. -/

open scoped TensorProduct

noncomputable section

namespace WideE

attribute [local instance 2000] Algebra.toSMul Algebra.toModule

variable {k R A H : Type*} [CommRing k] [CommRing R] [CommRing A] [CommRing H]
  [Algebra k R] [Algebra k A] [Algebra k H] [Algebra R A] [IsScalarTower k R A]

/-- Tensoring a principal localization with a constant algebra localizes by
the same scalar. -/
theorem constantTensor_isLocalizationAway (a : R) [IsLocalization.Away a A] :
    letI := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k R A)
      (AlgHom.id k H)).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R (R ⊗[k] H) a) (A ⊗[k] H) := by
  letI := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k R A)
    (AlgHom.id k H)).toRingHom.toAlgebra
  let T := R ⊗[k] H
  let U := A ⊗[k] H
  letI : IsScalarTower R T U := IsScalarTower.of_algebraMap_eq fun r => rfl
  let f := (IsScalarTower.toAlgHom R T U).toLinearMap
  have hBase : IsBaseChange A f := by
    apply IsBaseChange.of_equiv (Algebra.TensorProduct.cancelBaseChange k R A A H).toLinearEquiv
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul r h =>
      simp only [AlgEquiv.toLinearEquiv_apply, Algebra.TensorProduct.cancelBaseChange_tmul,
        smul_eq_mul, Algebra.smul_def, mul_one]
      rfl
  have hLoc := (isLocalizedModule_iff_isLocalization (S := Submonoid.powers a)).mp
    ((isLocalizedModule_iff_isBaseChange (Submonoid.powers a) A f).mpr hBase)
  simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using hLoc

/-- A principal localization pulls back to the same principal localization of
an arbitrary algebra over the base. -/
theorem baseChange_isLocalizationAway {B S T : Type*} [CommRing B] [CommRing S] [CommRing T]
    [Algebra B S] [Algebra B T] (b : B) [IsLocalization.Away b T] :
    letI := (Algebra.TensorProduct.includeRight : S →ₐ[B] T ⊗[B] S).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap B S b) (T ⊗[B] S) := by
  let i : S →ₐ[B] T ⊗[B] S := Algebra.TensorProduct.includeRight
  letI := i.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom i
  let f := (IsScalarTower.toAlgHom B S (T ⊗[B] S)).toLinearMap
  have h : IsBaseChange T f := by
    exact TensorProduct.isBaseChange B S T
  have hLoc := (isLocalizedModule_iff_isLocalization (S := Submonoid.powers b)).mp
    ((isLocalizedModule_iff_isBaseChange (Submonoid.powers b) T f).mpr h)
  simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using hLoc

end WideE
