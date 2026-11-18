import WideE.HopfPointBaseChange
import WideE.HopfLieMatrixAdjoint

/-! Scalar extension of the cotangent space, tangent matrices, and adjoint action. -/

noncomputable section

open scoped TensorProduct

namespace WideE

section Derivation

variable {k H M : Type*} [Field k] [CommRing H] [Bialgebra k H]
  [AddCommGroup M] [Module k M]

local notation "ε" => Bialgebra.counitAlgHom k H
local notation "I" => hopfAugmentationIdeal k H

private def liftCounitDerivation (D : H →ₗ[k] M)
    (hD : ∀ a b, D (a * b) = ε a • D b + ε b • D a) :
    HopfCotangent k H →ₗ[k] M := by
  let W := I • (⊤ : Submodule H I)
  refine (W.restrictScalars k).liftQ (D.comp ((I).restrictScalars k).subtype) ?_
  intro z hz
  change z ∈ W at hz
  change D z = 0
  refine Submodule.smul_induction_on (p := fun w : I => D w = 0) hz ?_ ?_
  · intro a ha b _
    change D (a * b) = 0
    rw [hD, show ε a = 0 from ha, show ε (b : H) = 0 from b.property,
      zero_smul, zero_smul, add_zero]
  · intro a b ha hb
    change D ((a : H) + (b : H)) = 0
    rw [map_add, ha, hb, add_zero]

private theorem liftCounitDerivation_projection (D : H →ₗ[k] M)
    (hD : ∀ a b, D (a * b) = ε a • D b + ε b • D a) (a : H) :
    liftCounitDerivation D hD (hopfCotangentProjection k H a) = D a := by
  have hOne : D 1 = 0 := by
    have h : D 1 = D 1 + D 1 := by
      simpa only [one_mul, map_one, one_smul] using hD 1 1
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  change D (a - algebraMap k H (ε a)) = D a
  rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, hOne, smul_zero, sub_zero]

end Derivation

section Cotangent

variable {k F H : Type*} [Field k] [Field F] [Algebra k F] [CommRing H] [HopfAlgebra k H]

local notation "H'" => (F ⊗[k] H)
local notation "C" => HopfCotangent k H
local notation "C'" => HopfCotangent F H'
local notation "d" => hopfCotangentProjection k H
local notation "d'" => hopfCotangentProjection F H'

attribute [local instance] hopfScalarExtension

private def rightCotangentDerivation : H →ₗ[k] C' :=
  (d').restrictScalars k ∘ₗ (Algebra.TensorProduct.includeRight : H →ₐ[k] H').toLinearMap

private theorem rightCotangentDerivation_mul (x y : H) :
    rightCotangentDerivation (k := k) (F := F) (x * y) =
      Bialgebra.counitAlgHom k H x • rightCotangentDerivation (k := k) (F := F) y +
        Bialgebra.counitAlgHom k H y • rightCotangentDerivation (k := k) (F := F) x := by
  change d' ((1 : F) ⊗ₜ[k] (x * y)) =
    Bialgebra.counitAlgHom k H x • d' ((1 : F) ⊗ₜ[k] y) +
      Bialgebra.counitAlgHom k H y • d' ((1 : F) ⊗ₜ[k] x)
  have h : (1 : F) ⊗ₜ[k] (x * y) = ((1 : F) ⊗ₜ[k] x) * ((1 : F) ⊗ₜ[k] y) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [h, hopfCotangentProjection_mul, hopfScalarExtension_counit_tmul,
    hopfScalarExtension_counit_tmul, one_mul, one_mul,
    IsScalarTower.algebraMap_smul F, IsScalarTower.algebraMap_smul F]

private def rightCotangent : C →ₗ[k] C' :=
  liftCounitDerivation rightCotangentDerivation rightCotangentDerivation_mul

private theorem rightCotangent_projection (a : H) :
    rightCotangent (F := F) (d a) = d' ((1 : F) ⊗ₜ[k] a) :=
  liftCounitDerivation_projection _ _ a

private theorem extendedCotangentDerivation_mul (x y : H') :
    (d).baseChange F (x * y) =
      Bialgebra.counitAlgHom F H' x • (d).baseChange F y +
        Bialgebra.counitAlgHom F H' y • (d).baseChange F x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [zero_mul, map_zero, zero_smul, smul_zero, add_zero]
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [add_mul, map_add, add_smul, smul_add, hx₁, hx₂]
    abel
  | tmul a x =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [mul_zero, map_zero, zero_smul, smul_zero, add_zero]
    | add y₁ y₂ hy₁ hy₂ =>
      simp only [mul_add, map_add, add_smul, smul_add, hy₁, hy₂]
      abel
    | tmul b y =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul,
        hopfScalarExtension_counit_tmul, hopfCotangentProjection_mul, TensorProduct.tmul_add,
        ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul,
        Algebra.id.map_eq_id, RingHom.id_apply]
      congr 1 <;> congr 1 <;> ring

private def extendCotangentInverse : C' →ₗ[F] F ⊗[k] C :=
  liftCounitDerivation ((d).baseChange F) extendedCotangentDerivation_mul

private theorem extendCotangentInverse_projection (z : H') :
    extendCotangentInverse (hopfCotangentProjection F H' z) = (d).baseChange F z :=
  liftCounitDerivation_projection _ _ z

/-- Cotangent space of a scalar-extended Hopf algebra at its actual counit. -/
def hopfCotangentBaseChange : F ⊗[k] C ≃ₗ[F] C' :=
  LinearEquiv.ofLinear (rightCotangent.liftBaseChange F) extendCotangentInverse (by
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := hopfCotangentProjection_surjective F H' x
    rw [LinearMap.comp_apply, LinearMap.id_apply, extendCotangentInverse_projection]
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a h =>
      rw [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, rightCotangent_projection,
        ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]) (by
    apply LinearMap.ext
    intro z
    rw [LinearMap.comp_apply, LinearMap.id_apply]
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a c =>
      obtain ⟨h, rfl⟩ := hopfCotangentProjection_surjective k H c
      rw [LinearMap.liftBaseChange_tmul, rightCotangent_projection, map_smul,
        extendCotangentInverse_projection, LinearMap.baseChange_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one])

@[simp] theorem hopfCotangentBaseChange_tmul (a : F) (h : H) :
    hopfCotangentBaseChange (a ⊗ₜ[k] d h) = d' (a ⊗ₜ[k] h) := by
  change rightCotangent.liftBaseChange F (a ⊗ₜ[k] d h) = _
  rw [LinearMap.liftBaseChange_tmul, rightCotangent_projection, ← map_smul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

@[simp] theorem hopfCotangentBaseChange_symm_projection_tmul (a : F) (h : H) :
    hopfCotangentBaseChange.symm (d' (a ⊗ₜ[k] h)) = a ⊗ₜ[k] d h :=
  (LinearEquiv.symm_apply_eq _).mpr (hopfCotangentBaseChange_tmul a h).symm

section LieVector

variable {B : Type*} [CommRing B] [Algebra k B] [Algebra F B] [IsScalarTower k F B]

/-- Tangent vectors valued in an extension algebra identify via scalar extension. -/
def hopfLieVectorBaseChange : HopfLieVector k H B ≃ₗ[F] HopfLieVector F H' B :=
  (LinearMap.liftBaseChangeEquiv F).trans
    (hopfCotangentBaseChange.arrowCongr (LinearEquiv.refl F B))

@[simp] theorem hopfLieVectorBaseChange_projection_tmul (x : HopfLieVector k H B) (a : F) (h : H) :
    hopfLieVectorBaseChange (F := F) x (d' (a ⊗ₜ[k] h)) = a • x (d h) := by
  rw [hopfLieVectorBaseChange, LinearEquiv.trans_apply, LinearEquiv.arrowCongr_apply,
    LinearEquiv.refl_apply, hopfCotangentBaseChange_symm_projection_tmul, LinearMap.liftBaseChange_tmul]

theorem hopfLieVectorBaseChange_ext {x y : HopfLieVector F H' B}
    (h : ∀ a : H, x (d' ((1 : F) ⊗ₜ[k] a)) = y (d' ((1 : F) ⊗ₜ[k] a))) : x = y := by
  apply (hopfLieVectorBaseChange (k := k) (H := H) (F := F)).symm.injective
  apply LinearMap.ext
  intro c
  obtain ⟨a, rfl⟩ := hopfCotangentProjection_surjective k H c
  simpa only [hopfLieVectorBaseChange, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearMap.liftBaseChangeEquiv_symm_apply, LinearEquiv.arrowCongr_symm_apply,
    LinearEquiv.refl_symm, LinearEquiv.refl_apply, hopfCotangentBaseChange_tmul] using h a

/-- The same matrix of coefficient differentials computes the extended tangent vector. -/
theorem hopfCotangentMatrix_baseChange {ι : Type*} (U : Matrix ι ι H) (x : HopfLieVector k H B) :
    hopfCotangentMatrix (U.map (Algebra.TensorProduct.includeRight : H →ₐ[k] H'))
        (hopfLieVectorBaseChange (F := F) x) =
      hopfCotangentMatrix U x := by
  apply Matrix.ext
  intro i j
  change hopfLieVectorBaseChange (F := F) x (d' ((1 : F) ⊗ₜ[k] U i j)) = x (d (U i j))
  rw [hopfLieVectorBaseChange_projection_tmul, one_smul]

theorem hopfLieVectorBaseChange_postcompose {D : Type*} [CommRing D]
    [Algebra k D] [Algebra F D] [IsScalarTower k F D]
    (f : B →ₐ[F] D) (x : HopfLieVector k H B) :
    hopfLieVectorBaseChange (F := F) ((f.restrictScalars k).toLinearMap.comp x) =
      f.toLinearMap.comp (hopfLieVectorBaseChange (F := F) x) := by
  apply hopfLieVectorBaseChange_ext
  intro a
  simp only [hopfLieVectorBaseChange_projection_tmul, one_smul, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rfl

theorem hopfLieInfinitesimalPoint_baseChange (x : HopfLieVector k H B) :
    hopfLieInfinitesimalPoint (hopfLieVectorBaseChange (F := F) x) =
      scalarExtendPoint (A := F) (hopfLieInfinitesimalPoint x) := by
  apply scalarExtendPoint_ext
  intro a
  rw [scalarExtendPoint_one_tmul]
  apply TrivSqZeroExt.ext
  · rw [hopfLieInfinitesimalPoint_fst, hopfLieInfinitesimalPoint_fst,
      hopfScalarExtension_counit_tmul, one_mul, IsScalarTower.algebraMap_apply k F B]
  · rw [hopfLieInfinitesimalPoint_snd, hopfLieInfinitesimalPoint_snd,
      hopfLieVectorBaseChange_projection_tmul, one_smul]

/-- The scalar-extended adjoint action is the original adjoint action on the same points. -/
theorem hopfLieVectorBaseChange_adjoint (p : H →ₐ[k] B) (x : HopfLieVector k H B) :
    hopfLieVectorBaseChange (F := F) (hopfAdjoint p x) =
      hopfAdjoint (scalarExtendPoint (A := F) p) (hopfLieVectorBaseChange (F := F) x) := by
  let p' := scalarExtendPoint (A := F) p
  let x' := hopfLieVectorBaseChange (F := F) x
  let i := TrivSqZeroExt.inlAlgHom k B B
  let i' := TrivSqZeroExt.inlAlgHom F B B
  letI := hopfPointGroup (k := k) (H := H) (A := DualNumber B)
  letI := hopfPointGroup (k := F) (H := H') (A := DualNumber B)
  have hi : i'.comp p' = scalarExtendPoint (A := F) (i.comp p) := scalarExtendPoint_postcompose i' p
  have h : hopfLieInfinitesimalPoint (hopfAdjoint p x) =
      i.comp p * hopfLieInfinitesimalPoint x * (i.comp p)⁻¹ := by
    rw [← hopfInfinitesimal_conjugation p x, hopfConjugation_eval]
  have h' : hopfLieInfinitesimalPoint (hopfAdjoint p' x') =
      i'.comp p' * hopfLieInfinitesimalPoint x' * (i'.comp p')⁻¹ := by
    rw [← hopfInfinitesimal_conjugation p' x', hopfConjugation_eval]
  apply (hopfInfinitesimalPointEquiv F H' B).injective
  apply Subtype.ext
  change hopfLieInfinitesimalPoint (hopfLieVectorBaseChange (F := F) (hopfAdjoint p x)) =
    hopfLieInfinitesimalPoint (hopfAdjoint p' x')
  rw [hopfLieInfinitesimalPoint_baseChange, h, h', hi]
  have hx : hopfLieInfinitesimalPoint x' = scalarExtendPoint (A := F) (hopfLieInfinitesimalPoint x) :=
    hopfLieInfinitesimalPoint_baseChange x
  rw [hx]
  let f := scalarExtendPointMulEquiv (k := k) (F := F) (H := H) (B := DualNumber B)
  change f (i.comp p * hopfLieInfinitesimalPoint x * (i.comp p)⁻¹) =
    f (i.comp p) * f (hopfLieInfinitesimalPoint x) * (f (i.comp p))⁻¹
  rw [map_mul, map_mul, map_inv]

end LieVector

end Cotangent

end WideE
