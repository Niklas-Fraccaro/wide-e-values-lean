import WideE.HopfLieAlgebra
import Mathlib.RingTheory.Bialgebra.Hom

/-! The differential of a morphism of affine Hopf groups. -/

noncomputable section

open scoped TensorProduct

namespace WideE

section Invariant

variable {k A : Type*} [Field k] [CommRing A] [HopfAlgebra k A]

private theorem invariantDerivation_eq_tensor (D : hopfInvariantDerivations k A) (a : A) :
    D.val a = TensorProduct.rid k A
      (((Bialgebra.counitAlgHom k A).toLinearMap.comp D.val.toLinearMap).lTensor A
        (Bialgebra.comulAlgHom k A a)) := by
  let ε := Bialgebra.counitAlgHom k A
  let Δ := Bialgebra.comulAlgHom k A
  let e (z : A ⊗[k] A) := TensorProduct.rid k A (ε.toLinearMap.lTensor A z)
  have he (x : A) : e (Δ x) = x := by
    change TensorProduct.rid k A (ε.toLinearMap.lTensor A (Δ x)) = x
    rw [show ε.toLinearMap.lTensor A (Δ x) = (TensorProduct.rid k A).symm x from
      Coalgebra.lTensor_counit_comul x, LinearEquiv.apply_symm_apply]
  have h := congrArg e (D.property a)
  change e (Δ (D.val a)) = e (D.val.toLinearMap.lTensor A (Δ a)) at h
  rw [he] at h
  simpa only [e, LinearMap.lTensor_comp, LinearMap.comp_apply] using h

private theorem invariantDerivation_ext_counit (D E : hopfInvariantDerivations k A)
    (h : ∀ a, Bialgebra.counitAlgHom k A (D.val a) = Bialgebra.counitAlgHom k A (E.val a)) :
    D = E := by
  have hε : (Bialgebra.counitAlgHom k A).toLinearMap.comp D.val.toLinearMap =
      (Bialgebra.counitAlgHom k A).toLinearMap.comp E.val.toLinearMap := LinearMap.ext h
  apply Subtype.ext
  apply Derivation.ext
  intro a
  rw [invariantDerivation_eq_tensor D, invariantDerivation_eq_tensor E, hε]

end Invariant

section Descent

variable {k Q H : Type*} [Field k] [CommRing Q] [CommRing H]
  [HopfAlgebra k Q] [HopfAlgebra k H] (j : Q →ₐc[k] H)

private def restrictCounitDerivation (D : hopfInvariantDerivations k H) :
    hopfCounitDerivations k Q k := by
  let f : Q →ₐ[k] H := j
  let ε := Bialgebra.counitAlgHom k H
  have hε (a : Q) : ε (f a) = Bialgebra.counitAlgHom k Q a :=
    DFunLike.congr_fun (BialgHomClass.counitAlgHom_comp j) a
  refine ⟨ε.toLinearMap.comp (D.val.toLinearMap.comp f.toLinearMap), fun a b => ?_⟩
  change ε (D.val (f (a * b))) =
    Bialgebra.counitAlgHom k Q a • ε (D.val (f b)) +
      Bialgebra.counitAlgHom k Q b • ε (D.val (f a))
  simp only [map_mul f, D.val.leibniz, Algebra.id.smul_eq_mul, map_add, map_mul, hε, smul_eq_mul]

private def mapInvariantDerivation (D : hopfInvariantDerivations k H) : hopfInvariantDerivations k Q :=
  hopfLieVectorInvariantDerivations ((hopfLieDerivationEquiv k Q k).symm (restrictCounitDerivation j D))

private theorem mapInvariantDerivation_counit (D : hopfInvariantDerivations k H) (a : Q) :
    Bialgebra.counitAlgHom k Q ((mapInvariantDerivation j D).val a) =
      Bialgebra.counitAlgHom k H (D.val (j a)) := by
  rw [mapInvariantDerivation, hopfLieVectorInvariantDerivations_counit, hopfLieDerivationEquiv_symm_apply]
  rfl

private theorem mapInvariantDerivation_commutes (D : hopfInvariantDerivations k H) (a : Q) :
    j ((mapInvariantDerivation j D).val a) = D.val (j a) := by
  let f : Q →ₐ[k] H := j
  have hΔ : Bialgebra.comulAlgHom k H (f a) =
      Algebra.TensorProduct.map f f (Bialgebra.comulAlgHom k Q a) :=
    (DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom j) a).symm
  change f ((mapInvariantDerivation j D).val a) = D.val (f a)
  rw [invariantDerivation_eq_tensor (mapInvariantDerivation j D), invariantDerivation_eq_tensor D, hΔ]
  generalize Bialgebra.comulAlgHom k Q a = z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Algebra.TensorProduct.map_tmul,
      LinearMap.comp_apply, Derivation.coeFn_coe, AlgHom.toLinearMap_apply, map_smul,
      mapInvariantDerivation_counit]
    rfl

/-- The actual Lie algebra map induced contravariantly from the coordinate homomorphism. -/
def hopfInvariantDerivationsMap : hopfInvariantDerivations k H →ₗ⁅k⁆ hopfInvariantDerivations k Q where
  toFun := mapInvariantDerivation j
  map_add' D E := by
    apply invariantDerivation_ext_counit
    intro a
    rw [mapInvariantDerivation_counit]
    change Bialgebra.counitAlgHom k H (D.val (j a) + E.val (j a)) =
      Bialgebra.counitAlgHom k Q ((mapInvariantDerivation j D).val a + (mapInvariantDerivation j E).val a)
    simp only [map_add, mapInvariantDerivation_counit]
  map_smul' r D := by
    apply invariantDerivation_ext_counit
    intro a
    rw [mapInvariantDerivation_counit]
    change Bialgebra.counitAlgHom k H (r • D.val (j a)) =
      Bialgebra.counitAlgHom k Q (r • (mapInvariantDerivation j D).val a)
    simp only [map_smul, mapInvariantDerivation_counit]
  map_lie' {D E} := by
    apply invariantDerivation_ext_counit
    intro a
    rw [mapInvariantDerivation_counit]
    let D' := mapInvariantDerivation j D
    let E' := mapInvariantDerivation j E
    change Bialgebra.counitAlgHom k H (D.val (E.val (j a)) - E.val (D.val (j a))) =
      Bialgebra.counitAlgHom k Q (D'.val (E'.val a) - E'.val (D'.val a))
    simp only [map_sub, D', E', mapInvariantDerivation_counit, mapInvariantDerivation_commutes]

/-- The induced Lie algebra map commutes with the coordinate map. -/
theorem hopfInvariantDerivationsMap_commutes (D : hopfInvariantDerivations k H) (a : Q) :
    j (((hopfInvariantDerivationsMap j) D).val a) = D.val (j a) :=
  mapInvariantDerivation_commutes j D a

@[simp] theorem hopfInvariantDerivationsMap_counit (D : hopfInvariantDerivations k H) (a : Q) :
    Bialgebra.counitAlgHom k Q (((hopfInvariantDerivationsMap j) D).val a) =
      Bialgebra.counitAlgHom k H (D.val (j a)) :=
  mapInvariantDerivation_counit j D a

end Descent

end WideE
