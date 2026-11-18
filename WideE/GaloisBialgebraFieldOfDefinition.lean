import WideE.GaloisFieldOfDefinition
import BialgebraBaseChangeLaws
import Mathlib.RingTheory.Bialgebra.Equiv

/-! Preservation of the bialgebra laws when an isomorphism is defined over a finite field. -/

noncomputable section

open scoped TensorProduct
open StrictEUnit

namespace WideE

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 120000
attribute [local instance 2000] Algebra.toModule

section TensorSquare

variable {F Ω H : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable [CommRing H] [Algebra F H]

/-- Inclusion of the tensor square of the scalar extension, under the change of scalars. -/
def finiteGaloisTensorSquareInclusion (H : Type*) [CommRing H] [Algebra F H]
    (L : FiniteGaloisIntermediateField F Ω) :
    (L ⊗[F] H) ⊗[L] (L ⊗[F] H) →ₐ[F] (Ω ⊗[F] H) ⊗[Ω] (Ω ⊗[F] H) :=
  ((algebraTensorBaseChangeEquiv (k := F) Ω H H).symm.toAlgHom.restrictScalars F).comp
    ((finiteGaloisTensorInclusion (H ⊗[F] H) L).comp
      ((algebraTensorBaseChangeEquiv (k := F) L H H).toAlgHom.restrictScalars F))

theorem finiteGaloisTensorSquareInclusion_injective (L : FiniteGaloisIntermediateField F Ω) :
    Function.Injective (finiteGaloisTensorSquareInclusion H L) :=
  (algebraTensorBaseChangeEquiv (k := F) Ω H H).symm.injective.comp
    ((finiteGaloisTensorInclusion_injective L).comp
      (algebraTensorBaseChangeEquiv (k := F) L H H).injective)

private theorem finiteGaloisTensorSquareInclusion_tmul (L : FiniteGaloisIntermediateField F Ω)
    (x y : L ⊗[F] H) :
    finiteGaloisTensorSquareInclusion H L (x ⊗ₜ[L] y) =
      finiteGaloisTensorInclusion H L x ⊗ₜ[Ω] finiteGaloisTensorInclusion H L y := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.zero_tmul, map_zero]
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul c d =>
      let τ := L.toIntermediateField.val
      let T := algebraTensorBaseChangeEquiv (k := F) Ω H H
      apply T.injective
      change T (T.symm (finiteGaloisTensorInclusion (H ⊗[F] H) L
        (algebraTensorBaseChangeEquiv (k := F) L H H ((a ⊗ₜ[F] b) ⊗ₜ[L] (c ⊗ₜ[F] d))))) =
          T ((τ a ⊗ₜ[F] b) ⊗ₜ[Ω] (τ c ⊗ₜ[F] d))
      rw [AlgEquiv.apply_symm_apply, algebraTensorBaseChangeEquiv_tmul]
      change (τ (a * c) ⊗ₜ[F] (b ⊗ₜ[F] d)) =
        algebraTensorBaseChangeEquiv (k := F) Ω H H ((τ a ⊗ₜ[F] b) ⊗ₜ[Ω] (τ c ⊗ₜ[F] d))
      rw [algebraTensorBaseChangeEquiv_tmul, map_mul]

end TensorSquare

section Coalgebra

variable {F Ω H J : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable [CommRing H] [Bialgebra F H] [CommRing J] [Bialgebra F J]

private theorem tensorSquareInclusion_comul (L : FiniteGaloisIntermediateField F Ω) (x : L ⊗[F] H) :
    finiteGaloisTensorSquareInclusion H L (baseChangeComul (k := F) L x) =
      baseChangeComul (k := F) Ω (finiteGaloisTensorInclusion H L x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    rw [baseChangeComul_tmul]
    change (algebraTensorBaseChangeEquiv (k := F) Ω H H).symm
      (finiteGaloisTensorInclusion (H ⊗[F] H) L
        (algebraTensorBaseChangeEquiv (k := F) L H H
          ((algebraTensorBaseChangeEquiv (k := F) L H H).symm
            (a ⊗ₜ[F] Coalgebra.comul (R := F) b)))) =
      baseChangeComul (k := F) Ω (L.toIntermediateField.val a ⊗ₜ[F] b)
    rw [AlgEquiv.apply_symm_apply, baseChangeComul_tmul]
    rfl

private theorem tensorInclusion_counit (L : FiniteGaloisIntermediateField F Ω) (x : L ⊗[F] H) :
    L.toIntermediateField.val (baseChangeCounit (k := F) L x) =
      baseChangeCounit (k := F) Ω (finiteGaloisTensorInclusion H L x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    change L.toIntermediateField.val (baseChangeCounit (k := F) L (a ⊗ₜ[F] b)) =
      baseChangeCounit (k := F) Ω (L.toIntermediateField.val a ⊗ₜ[F] b)
    rw [baseChangeCounit_tmul, baseChangeCounit_tmul, map_mul, AlgHom.commutes]

private theorem tensorSquareInclusion_natural (L : FiniteGaloisIntermediateField F Ω)
    (e : Ω ⊗[F] H →ₐ[Ω] Ω ⊗[F] J) (d : L ⊗[F] H →ₐ[L] L ⊗[F] J)
    (h : (finiteGaloisTensorInclusion J L).comp (d.restrictScalars F) =
      (e.restrictScalars F).comp (finiteGaloisTensorInclusion H L))
    (x : (L ⊗[F] H) ⊗[L] (L ⊗[F] H)) :
    finiteGaloisTensorSquareInclusion J L (Algebra.TensorProduct.map d d x) =
      Algebra.TensorProduct.map e e (finiteGaloisTensorSquareInclusion H L x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, finiteGaloisTensorSquareInclusion_tmul]
    rw [show finiteGaloisTensorInclusion J L (d a) = e (finiteGaloisTensorInclusion H L a)
      from DFunLike.congr_fun h a,
      show finiteGaloisTensorInclusion J L (d b) = e (finiteGaloisTensorInclusion H L b)
      from DFunLike.congr_fun h b]

/-- Bialgebra preservation can be verified after including the finite field of definition. -/
def bialgEquivOfFiniteGaloisModel (L : FiniteGaloisIntermediateField F Ω) :
    letI := baseChangeBialgebra (k := F) (H := H) Ω
    letI := baseChangeBialgebra (k := F) (H := J) Ω
    letI := baseChangeBialgebra (k := F) (H := H) L
    letI := baseChangeBialgebra (k := F) (H := J) L
    (e : Ω ⊗[F] H ≃ₐc[Ω] Ω ⊗[F] J) → (d : L ⊗[F] H ≃ₐ[L] L ⊗[F] J) →
    ((finiteGaloisTensorInclusion J L).comp (d.toAlgHom.restrictScalars F) =
      (e.toAlgEquiv.toAlgHom.restrictScalars F).comp (finiteGaloisTensorInclusion H L)) →
    L ⊗[F] H ≃ₐc[L] L ⊗[F] J := by
  letI := baseChangeBialgebra (k := F) (H := H) Ω
  letI := baseChangeBialgebra (k := F) (H := J) Ω
  letI := baseChangeBialgebra (k := F) (H := H) L
  letI := baseChangeBialgebra (k := F) (H := J) L
  intro e d h
  have hEval (x : L ⊗[F] H) : finiteGaloisTensorInclusion J L (d x) =
      e (finiteGaloisTensorInclusion H L x) := DFunLike.congr_fun h x
  have hc (x : L ⊗[F] H) :
      baseChangeCounit (k := F) L (d x) = baseChangeCounit (k := F) L x := by
    apply L.toIntermediateField.val.injective
    change L.toIntermediateField.val (baseChangeCounit (k := F) L (d x)) =
      L.toIntermediateField.val (baseChangeCounit (k := F) L x)
    rw [tensorInclusion_counit, tensorInclusion_counit, hEval]
    exact CoalgHomClass.counit_comp_apply (R := Ω) e (finiteGaloisTensorInclusion H L x)
  have hD (x : L ⊗[F] H) :
      Algebra.TensorProduct.map d.toAlgHom d.toAlgHom (baseChangeComul (k := F) L x) =
        baseChangeComul (k := F) L (d x) := by
    apply finiteGaloisTensorSquareInclusion_injective L
    rw [tensorSquareInclusion_natural L _ _ h, tensorSquareInclusion_comul, tensorSquareInclusion_comul, hEval]
    exact CoalgHomClass.map_comp_comul_apply (R := Ω) e (finiteGaloisTensorInclusion H L x)
  let dC : L ⊗[F] H ≃ₗc[L] L ⊗[F] J := {
    d.toLinearEquiv with
    counit_comp := LinearMap.ext hc
    map_comp_comul := LinearMap.ext hD }
  exact { dC, d.toMulEquiv with }

/-- A bialgebra isomorphism between the scalar extensions of finite-type
bialgebras is defined over a common finite Galois subfield. -/
theorem exists_finiteGalois_tensor_bialgEquiv_model [IsGalois F Ω]
    [Algebra.FiniteType F H] [Algebra.FiniteType F J]
    (E : FiniteGaloisIntermediateField F Ω) :
    letI := baseChangeBialgebra (k := F) (H := H) Ω
    letI := baseChangeBialgebra (k := F) (H := J) Ω
    ∀ e : Ω ⊗[F] H ≃ₐc[Ω] Ω ⊗[F] J,
      ∃ L : FiniteGaloisIntermediateField F Ω, E ≤ L ∧
        letI := baseChangeBialgebra (k := F) (H := H) L
        letI := baseChangeBialgebra (k := F) (H := J) L
        ∃ d : L ⊗[F] H ≃ₐc[L] L ⊗[F] J,
          (finiteGaloisTensorInclusion J L).comp (d.toAlgEquiv.toAlgHom.restrictScalars F) =
            (e.toAlgEquiv.toAlgHom.restrictScalars F).comp (finiteGaloisTensorInclusion H L) := by
  letI := baseChangeBialgebra (k := F) (H := H) Ω
  letI := baseChangeBialgebra (k := F) (H := J) Ω
  intro e
  obtain ⟨L, hEL, d, hd⟩ := exists_finiteGalois_tensor_algEquiv_model E e.toAlgEquiv
  exact ⟨L, hEL, bialgEquivOfFiniteGaloisModel L e d hd, hd⟩

end Coalgebra

end WideE
