import WideE.HopfLieDerivation
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.RingTheory.Derivation.Lie

/-! The Lie algebra of an affine group, realized by invariant derivations. -/

noncomputable section

open scoped TensorProduct

namespace WideE

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 80000

variable {k H : Type*} [Field k] [CommRing H] [HopfAlgebra k H]

local notation "Δ" => (Bialgebra.comulAlgHom k H)
local notation "ε" => (Bialgebra.counitAlgHom k H)

private def rightEvaluation {W : Type*} [AddCommGroup W] [Module k W]
    (d : H →ₗ[k] k) : W ⊗[k] H →ₗ[k] W :=
  (TensorProduct.rid k W).toLinearMap.comp (d.lTensor W)

@[simp] private theorem rightEvaluation_tmul {W : Type*} [AddCommGroup W] [Module k W]
    (d : H →ₗ[k] k) (w : W) (a : H) : rightEvaluation d (w ⊗ₜ[k] a) = d a • w := rfl

private def invariantLinearMap (d : H →ₗ[k] k) : H →ₗ[k] H :=
  (rightEvaluation d).comp (Δ).toLinearMap

private theorem counit_invariantLinearMap (d : H →ₗ[k] k) (a : H) :
    ε (invariantLinearMap d a) = d a := by
  have he (z : H ⊗[k] H) : ε (rightEvaluation d z) =
      d (TensorProduct.lid k H ((ε).toLinearMap.rTensor H z)) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      simp only [rightEvaluation_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
        AlgHom.toLinearMap_apply, map_smul, smul_eq_mul]
      exact mul_comm _ _
  change ε (rightEvaluation d (Δ a)) = d a
  rw [he, show (ε).toLinearMap.rTensor H (Δ a) = (TensorProduct.lid k H).symm a from
    Coalgebra.rTensor_counit_comul a, LinearEquiv.apply_symm_apply]

private theorem invariantLinearMap_invariant (d : H →ₗ[k] k) (a : H) :
    Δ (invariantLinearMap d a) = (invariantLinearMap d).lTensor H (Δ a) := by
  have hD (z : H ⊗[k] H) : rightEvaluation d ((Δ).toLinearMap.rTensor H z) =
      Δ (rightEvaluation d z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => simp only [LinearMap.rTensor_tmul, rightEvaluation_tmul,
        AlgHom.toLinearMap_apply, map_smul]
  have hE (w : H) (z : H ⊗[k] H) :
      rightEvaluation d ((TensorProduct.assoc k H H H).symm (w ⊗ₜ[k] z)) =
        w ⊗ₜ[k] rightEvaluation d z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul x y => simp only [TensorProduct.assoc_symm_tmul, rightEvaluation_tmul, TensorProduct.tmul_smul]
  have hA (z : H ⊗[k] H) :
      rightEvaluation d ((TensorProduct.assoc k H H H).symm ((Δ).toLinearMap.lTensor H z)) =
        (invariantLinearMap d).lTensor H z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => simp only [LinearMap.lTensor_tmul, hE, invariantLinearMap,
        LinearMap.comp_apply]
  change Δ (rightEvaluation d (Δ a)) = _
  have h := Coalgebra.coassoc_apply (R := k) a
  change TensorProduct.assoc k H H H ((Δ).toLinearMap.rTensor H (Δ a)) =
    (Δ).toLinearMap.lTensor H (Δ a) at h
  rw [← hD, ← hA, ← h, LinearEquiv.symm_apply_apply]

private def evaluateRightCounit : H ⊗[k] H →ₐ[k] H :=
  (Algebra.TensorProduct.rid k k H).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id k H) ε)

@[simp] private theorem evaluateRightCounit_tmul (a b : H) :
    evaluateRightCounit (a ⊗ₜ[k] b) = ε b • a := rfl

@[simp] private theorem evaluateRightCounit_comul (a : H) : evaluateRightCounit (Δ a) = a := by
  change (Algebra.TensorProduct.rid k k H) ((ε).toLinearMap.lTensor H (Δ a)) = a
  rw [show (ε).toLinearMap.lTensor H (Δ a) = (Algebra.TensorProduct.rid k k H).symm a from
    Coalgebra.lTensor_counit_comul a, AlgEquiv.apply_symm_apply]

private theorem invariantLinearMap_leibniz (d : H →ₗ[k] k)
    (hd : ∀ a b, d (a * b) = ε a * d b + ε b * d a) (a b : H) :
    invariantLinearMap d (a * b) = a • invariantLinearMap d b + b • invariantLinearMap d a := by
  have h (z w : H ⊗[k] H) : rightEvaluation d (z * w) =
      evaluateRightCounit z * rightEvaluation d w + evaluateRightCounit w * rightEvaluation d z := by
    induction z using TensorProduct.induction_on generalizing w with
    | zero => simp
    | add x y hx hy =>
      simp only [add_mul, map_add, hx, hy, mul_add]
      ac_rfl
    | tmul x y =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add u v hu hv =>
        simp only [mul_add, map_add, hu, hv, add_mul]
        ac_rfl
      | tmul u v =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, rightEvaluation_tmul, hd]
        simp only [evaluateRightCounit_tmul, rightEvaluation_tmul, Algebra.smul_def, map_add, map_mul]
        ring
  change rightEvaluation d (Δ (a * b)) = a * rightEvaluation d (Δ b) + b * rightEvaluation d (Δ a)
  rw [map_mul, h, evaluateRightCounit_comul, evaluateRightCounit_comul]

/-- The invariant derivations form a Lie subalgebra of the derivations of the coordinate ring. -/
def hopfInvariantDerivations (k H : Type*) [Field k] [CommRing H] [HopfAlgebra k H] :
    LieSubalgebra k (Derivation k H H) where
  carrier := { D | ∀ a, Bialgebra.comulAlgHom k H (D a) = D.toLinearMap.lTensor H
    (Bialgebra.comulAlgHom k H a) }
  zero_mem' := by
    intro a
    change Bialgebra.comulAlgHom k H 0 = (0 : H →ₗ[k] H).lTensor H (Bialgebra.comulAlgHom k H a)
    rw [map_zero, LinearMap.lTensor_zero, LinearMap.zero_apply]
  add_mem' := by
    intro D E hD hE a
    change Bialgebra.comulAlgHom k H (D a + E a) = (D.toLinearMap + E.toLinearMap).lTensor H
      (Bialgebra.comulAlgHom k H a)
    rw [map_add, hD, hE, LinearMap.lTensor_add, LinearMap.add_apply]
  smul_mem' := by
    intro r D hD a
    change Bialgebra.comulAlgHom k H (r • D a) = (r • D.toLinearMap).lTensor H (Bialgebra.comulAlgHom k H a)
    rw [map_smul, hD, LinearMap.lTensor_smul, LinearMap.smul_apply]
  lie_mem' := by
    intro D E hD hE a
    change Bialgebra.comulAlgHom k H (D (E a) - E (D a)) =
      (D.toLinearMap.comp E.toLinearMap - E.toLinearMap.comp D.toLinearMap).lTensor H
        (Bialgebra.comulAlgHom k H a)
    rw [map_sub, hD (E a), hE (D a), hE a, hD a]
    simp only [LinearMap.lTensor_sub, LinearMap.lTensor_comp, LinearMap.comp_apply, LinearMap.sub_apply]

private def tangentToInvariantDerivation (x : HopfLieVector k H k) : hopfInvariantDerivations k H :=
  let d := x.comp (hopfCotangentProjection k H)
  let D := Derivation.mk' (invariantLinearMap d) (invariantLinearMap_leibniz d (fun a b => by
    change x (hopfCotangentProjection k H (a * b)) = _
    simp only [hopfCotangentProjection_mul, map_add, map_smul, smul_eq_mul, d, LinearMap.comp_apply]))
  ⟨D, invariantLinearMap_invariant d⟩

private theorem invariantLinearMap_add (d e : H →ₗ[k] k) (a : H) :
    invariantLinearMap (d + e) a = invariantLinearMap d a + invariantLinearMap e a := by
  simp only [invariantLinearMap, rightEvaluation, LinearMap.comp_apply, LinearMap.lTensor_add,
    LinearMap.add_apply, map_add]

private theorem invariantLinearMap_smul (r : k) (d : H →ₗ[k] k) (a : H) :
    invariantLinearMap (r • d) a = r • invariantLinearMap d a := by
  simp only [invariantLinearMap, rightEvaluation, LinearMap.comp_apply, LinearMap.lTensor_smul,
    LinearMap.smul_apply, map_smul]

/-- The invariant derivation determined by a tangent vector at the identity. -/
def tangentToInvariantDerivationLinear : HopfLieVector k H k →ₗ[k] hopfInvariantDerivations k H where
  toFun := tangentToInvariantDerivation
  map_add' x y := by
    apply Subtype.ext
    apply Derivation.ext
    intro a
    let p := hopfCotangentProjection k H
    change invariantLinearMap ((x + y).comp p) a =
      invariantLinearMap (x.comp p) a + invariantLinearMap (y.comp p) a
    rw [show (x + y).comp p = x.comp p + y.comp p from rfl]
    exact invariantLinearMap_add (x.comp p) (y.comp p) a
  map_smul' r x := by
    apply Subtype.ext
    apply Derivation.ext
    intro a
    let p := hopfCotangentProjection k H
    change invariantLinearMap ((r • x).comp p) a = r • invariantLinearMap (x.comp p) a
    rw [show (r • x).comp p = r • (x.comp p) from rfl]
    exact invariantLinearMap_smul r (x.comp p) a

private def counitOfDerivation (D : Derivation k H H) : hopfCounitDerivations k H k :=
  ⟨(ε).toLinearMap.comp D.toLinearMap, fun a b => by
    change ε (D (a * b)) = ε a • ε (D b) + ε b • ε (D a)
    simp only [D.leibniz, Algebra.id.smul_eq_mul, map_add, map_mul, smul_eq_mul]⟩

private def cotangentOfDerivation (D : Derivation k H H) : HopfLieVector k H k :=
  (hopfLieDerivationEquiv k H k).symm (counitOfDerivation D)

private theorem cotangentOfDerivation_projection (D : Derivation k H H) (a : H) :
    cotangentOfDerivation D (hopfCotangentProjection k H a) = ε (D a) :=
  hopfLieDerivationEquiv_symm_apply k H k (counitOfDerivation D) a

/-- The cotangent dual is linearly equivalent to the canonical Lie algebra of invariant derivations. -/
def hopfLieVectorInvariantDerivations : HopfLieVector k H k ≃ₗ[k] hopfInvariantDerivations k H :=
  LinearEquiv.ofBijective tangentToInvariantDerivationLinear ⟨by
    intro x y h
    apply LinearMap.ext
    intro v
    obtain ⟨a, rfl⟩ := hopfCotangentProjection_surjective k H v
    have hEval := congrArg (fun D : hopfInvariantDerivations k H => ε (D.val a)) h
    change ε (invariantLinearMap (x.comp (hopfCotangentProjection k H)) a) =
      ε (invariantLinearMap (y.comp (hopfCotangentProjection k H)) a) at hEval
    rwa [counit_invariantLinearMap, counit_invariantLinearMap] at hEval, by
    intro D
    refine ⟨cotangentOfDerivation D.val, Subtype.ext ?_⟩
    apply Derivation.ext
    intro a
    have h (z : H ⊗[k] H) : rightEvaluation (cotangentOfDerivation D.val ∘ₗ
        hopfCotangentProjection k H) z = evaluateRightCounit (D.val.toLinearMap.lTensor H z) := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x y => simp only [rightEvaluation_tmul, LinearMap.comp_apply, cotangentOfDerivation_projection,
          LinearMap.lTensor_tmul, evaluateRightCounit_tmul, Derivation.coeFn_coe]
    change rightEvaluation (cotangentOfDerivation D.val ∘ₗ hopfCotangentProjection k H) (Δ a) = D.val a
    rw [h, ← D.property a, evaluateRightCounit_comul]⟩

@[simp] theorem hopfLieVectorInvariantDerivations_counit (x : HopfLieVector k H k) (a : H) :
    ε ((hopfLieVectorInvariantDerivations x).val a) = x (hopfCotangentProjection k H a) :=
  counit_invariantLinearMap (x.comp (hopfCotangentProjection k H)) a

end WideE
