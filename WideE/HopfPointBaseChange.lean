import WideE.HopfScalarExtension
import WideE.HopfPointGroup

/-! Scalar extension identifies the actual point groups over a scalar tower. -/

noncomputable section

open scoped TensorProduct
open StrictEUnit

namespace WideE

section Points

variable {k F H B : Type*} [Field k] [CommRing F] [Algebra k F]
  [CommRing H] [HopfAlgebra k H] [CommRing B]
  [Algebra k B] [Algebra F B] [IsScalarTower k F B]

local notation "H'" => (F ⊗[k] H)

attribute [local instance] hopfScalarExtension

/-- The extended counit at a tensor of two coordinates. -/
theorem hopfScalarExtension_counit_tmul (a : F) (h : H) :
    Bialgebra.counitAlgHom F H' (a ⊗ₜ[k] h) =
      a * algebraMap k F (Bialgebra.counitAlgHom k H h) :=
  baseChangeCounit_tmul F a h

/-- The original right-factor inclusion determines every point of the scalar extension. -/
theorem scalarExtendPoint_ext {p q : H' →ₐ[F] B}
    (h : ∀ x : H, p ((1 : F) ⊗ₜ[k] x) = q ((1 : F) ⊗ₜ[k] x)) : p = q := by
  apply Algebra.TensorProduct.ext'
  intro a x
  have he : a ⊗ₜ[k] x = a • (((1 : F) ⊗ₜ[k] x) : H') := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [he, map_smul, map_smul, h]

private theorem scalarExtendPoint_comul (p q : H →ₐ[k] B) (z : H ⊗[k] H) :
    tensorPoint (scalarExtendPoint (A := F) p) (scalarExtendPoint (A := F) q)
      ((algebraTensorBaseChangeEquiv F H H).symm ((1 : F) ⊗ₜ[k] z)) = tensorPoint p q z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul x y =>
    simp only [algebraTensorBaseChangeEquiv_symm_tmul, tensorPoint_tmul, scalarExtendPoint_one_tmul]

theorem scalarExtendPoint_mul (p q : H →ₐ[k] B) :
    scalarExtendPoint (A := F) (hopfPointMul p q) =
      hopfPointMul (scalarExtendPoint (A := F) p) (scalarExtendPoint (A := F) q) := by
  apply scalarExtendPoint_ext
  intro x
  rw [scalarExtendPoint_one_tmul]
  change tensorPoint p q (Bialgebra.comulAlgHom k H x) =
    tensorPoint (scalarExtendPoint (A := F) p) (scalarExtendPoint (A := F) q)
      (baseChangeComul F ((1 : F) ⊗ₜ[k] x))
  rw [baseChangeComul_tmul, scalarExtendPoint_comul]
  rfl

theorem scalarExtendPoint_one :
    scalarExtendPoint (A := F) (hopfPointOne : H →ₐ[k] B) = hopfPointOne := by
  apply scalarExtendPoint_ext
  intro x
  rw [scalarExtendPoint_one_tmul]
  change algebraMap k B (Bialgebra.counitAlgHom k H x) =
    algebraMap F B (Bialgebra.counitAlgHom F H' ((1 : F) ⊗ₜ[k] x))
  rw [hopfScalarExtension_counit_tmul, one_mul, IsScalarTower.algebraMap_apply k F B]

/-- The canonical restriction and extension of points preserve convolution. -/
def scalarExtendPointMulEquiv :
    letI := hopfPointGroup (k := k) (H := H) (A := B)
    letI := hopfPointGroup (k := F) (H := H') (A := B)
    (H →ₐ[k] B) ≃* (H' →ₐ[F] B) := by
  letI := hopfPointGroup (k := k) (H := H) (A := B)
  letI := hopfPointGroup (k := F) (H := H') (A := B)
  exact
    { toFun := scalarExtendPoint (A := F)
      invFun := fun p => (p.restrictScalars k).comp (Algebra.TensorProduct.includeRight : H →ₐ[k] H')
      left_inv := fun p => AlgHom.ext fun x => scalarExtendPoint_one_tmul p x
      right_inv := fun p => scalarExtendPoint_ext fun x => scalarExtendPoint_one_tmul _ x
      map_mul' := scalarExtendPoint_mul }

@[simp] theorem scalarExtendPointMulEquiv_apply (p : H →ₐ[k] B) :
    scalarExtendPointMulEquiv (F := F) p = scalarExtendPoint (A := F) p := rfl

variable {D : Type*} [CommRing D] [Algebra k D] [Algebra F D] [IsScalarTower k F D]

theorem scalarExtendPoint_postcompose (f : B →ₐ[F] D) (p : H →ₐ[k] B) :
    f.comp (scalarExtendPoint (A := F) p) =
      scalarExtendPoint (A := F) ((f.restrictScalars k).comp p) := by
  apply scalarExtendPoint_ext
  intro x
  rw [AlgHom.comp_apply, scalarExtendPoint_one_tmul, scalarExtendPoint_one_tmul]
  rfl

end Points

section Galois

variable {k F H E : Type*} [Field k] [Field F] [Field E] [CommRing H] [HopfAlgebra k H]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]

attribute [local instance] hopfScalarExtension

/-- The same Galois cocycle with its points on the scalar-extended Hopf algebra. -/
def scalarExtendHopfPointCocycle (c : (E ≃ₐ[F] E) → H →ₐ[k] E) :
    (E ≃ₐ[F] E) → (F ⊗[k] H) →ₐ[F] E :=
  fun σ => scalarExtendPoint (A := F) (c σ)

private theorem scalarExtendPoint_galois_mul (p q : H →ₐ[k] E) (σ : E ≃ₐ[F] E) :
    hopfPointMul (scalarExtendPoint (A := F) p) (σ.toAlgHom.comp (scalarExtendPoint (A := F) q)) =
      scalarExtendPoint (A := F) (hopfPointMul p ((σ.toAlgHom.restrictScalars k).comp q)) := by
  rw [scalarExtendPoint_postcompose, scalarExtendPoint_mul]

theorem isHopfPointCocycle_scalarExtend_iff (c : (E ≃ₐ[F] E) → H →ₐ[k] E) :
    IsHopfPointCocycle (scalarExtendHopfPointCocycle c) ↔ IsHopfPointCocycle c := by
  letI := hopfPointGroup (k := k) (H := H) (A := E)
  letI := hopfPointGroup (k := F) (H := F ⊗[k] H) (A := E)
  let f := scalarExtendPointMulEquiv (k := k) (F := F) (H := H) (B := E)
  have hOne : scalarExtendHopfPointCocycle c 1 = hopfPointOne ↔ c 1 = hopfPointOne := by
    rw [scalarExtendHopfPointCocycle, ← scalarExtendPoint_one (k := k) (F := F) (H := H)]
    exact f.injective.eq_iff
  unfold IsHopfPointCocycle
  refine and_congr hOne (forall_congr' fun σ => forall_congr' fun τ => ?_)
  change scalarExtendPoint (A := F) (c (σ * τ)) =
    hopfPointMul (scalarExtendPoint (A := F) (c σ))
      (σ.toAlgHom.comp (scalarExtendPoint (A := F) (c τ))) ↔ _
  rw [scalarExtendPoint_galois_mul]
  exact f.injective.eq_iff

theorem isHopfPointCoboundary_scalarExtend_iff (c : (E ≃ₐ[F] E) → H →ₐ[k] E) :
    IsHopfPointCoboundary (scalarExtendHopfPointCocycle c) ↔ IsHopfPointCoboundary c := by
  letI := hopfPointGroup (k := k) (H := H) (A := E)
  letI := hopfPointGroup (k := F) (H := F ⊗[k] H) (A := E)
  let f := scalarExtendPointMulEquiv (k := k) (F := F) (H := H) (B := E)
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨q, rfl⟩ := f.surjective b
    refine ⟨q, fun σ => f.injective ?_⟩
    have h := hb σ
    change hopfPointMul (scalarExtendPoint (A := F) (c σ))
      (σ.toAlgHom.comp (scalarExtendPoint (A := F) q)) = scalarExtendPoint (A := F) q at h
    rwa [scalarExtendPoint_galois_mul] at h
  · rintro ⟨q, hq⟩
    refine ⟨f q, fun σ => ?_⟩
    change hopfPointMul (scalarExtendPoint (A := F) (c σ))
      (σ.toAlgHom.comp (scalarExtendPoint (A := F) q)) = scalarExtendPoint (A := F) q
    rw [scalarExtendPoint_galois_mul, hq]

end Galois

end WideE
