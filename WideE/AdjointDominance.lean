import WideE.AffineDominance
import WideE.AffineDominanceExtension
import WideE.HopfLieAlgebra
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import MixedRelativeTensorDerivation

/-! A full-rank differential makes a family of actual adjoint orbits
contain a nonempty principal open. -/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

variable {k H ι τ : Type*} [Field k] [CommRing H] [HopfAlgebra k H] [Fintype ι] [Fintype τ]

local notation "C" => HopfCotangent k H
local notation "P" => MvPolynomial τ k
local notation "A" => (H ⊗[k] P)
local notation "𝔤" => HopfLieVector k H k

private def adjointParameterPolynomial (v : τ → 𝔤) (c : C) : P :=
  ∑ r, MvPolynomial.C (v r c) * MvPolynomial.X r

/-- The coordinate functions of the adjoint orbit of a linearly parameterized Lie vector. -/
def hopfAdjointFamilyCoordinate (b : Basis ι k C) (v : τ → 𝔤) (i : ι) : A :=
  ∑ j, hopfAdjointMatrix b i j ⊗ₜ[k] adjointParameterPolynomial v (b j)

private theorem adjointParameterPolynomial_apply (v : τ → 𝔤) (a : τ → k) (c : C) :
    MvPolynomial.aeval a (adjointParameterPolynomial v c) = (∑ r, a r • v r) c := by
  classical
  simp only [adjointParameterPolynomial, map_sum, map_mul, MvPolynomial.aeval_C,
    Algebra.id.map_eq_id, RingHom.id_apply, MvPolynomial.aeval_X, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, mul_comm]

/-- Evaluation at an actual group point and a parameter gives the corresponding adjoint coordinates. -/
theorem hopfAdjointFamilyCoordinate_apply
    (b : Basis ι k C) (v : τ → 𝔤) (p : H →ₐ[k] k) (a : τ → k) (i : ι) :
    tensorPoint p (MvPolynomial.aeval a) (hopfAdjointFamilyCoordinate b v i) =
      hopfAdjoint p (∑ r, a r • v r) (b i) := by
  classical
  rw [hopfAdjointFamilyCoordinate, map_sum]
  simp only [tensorPoint_tmul, adjointParameterPolynomial_apply]
  exact (congrFun (hopfAdjoint_apply_basis b p (∑ r, a r • v r)) i).symm

private theorem adjointParameterPolynomial_apply_extension {E : Type*} [CommRing E] [Algebra k E]
    (v : τ → 𝔤) (a : τ → E) (c : C) :
    MvPolynomial.aeval a (adjointParameterPolynomial v c) =
      (∑ r, a r • (Algebra.ofId k E).toLinearMap.comp (v r)) c := by
  classical
  simp only [adjointParameterPolynomial, map_sum, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, Algebra.ofId_apply, smul_eq_mul, mul_comm]

/-- The adjoint orbit coordinates evaluate over an arbitrary extension algebra. -/
theorem hopfAdjointFamilyCoordinate_apply_extension {E : Type*} [CommRing E] [Algebra k E]
    (b : Basis ι k C) (v : τ → 𝔤) (p : H →ₐ[k] E) (a : τ → E) (i : ι) :
    tensorPoint p (MvPolynomial.aeval a) (hopfAdjointFamilyCoordinate b v i) =
      hopfAdjoint p (∑ r, a r • (Algebra.ofId k E).toLinearMap.comp (v r)) (b i) := by
  classical
  rw [hopfAdjointFamilyCoordinate, map_sum]
  simp only [tensorPoint_tmul, adjointParameterPolynomial_apply_extension]
  exact (congrFun (hopfAdjoint_apply_basis b p
    (∑ r, a r • (Algebra.ofId k E).toLinearMap.comp (v r))) i).symm

omit [Fintype τ] in
private theorem tensor_parameterPoint {E : Type*} [CommRing E] [Algebra k E] (q : A →ₐ[k] E) :
    q = tensorPoint (q.comp Algebra.TensorProduct.includeLeft)
      (MvPolynomial.aeval (fun r => (q.comp Algebra.TensorProduct.includeRight) (MvPolynomial.X r))) := by
  let x : τ → E := fun r => (q.comp Algebra.TensorProduct.includeRight) (MvPolynomial.X r)
  have h : q.comp Algebra.TensorProduct.includeRight = MvPolynomial.aeval x :=
    MvPolynomial.algHom_ext fun r => (MvPolynomial.aeval_X x r).symm
  apply Algebra.TensorProduct.ext
  · exact AlgHom.ext fun a => by
      change q (a ⊗ₜ[k] (1 : P)) = _ * (MvPolynomial.aeval x) 1
      rw [map_one, mul_one]
      rfl
  · apply AlgHom.ext
    intro b
    change (q.comp Algebra.TensorProduct.includeRight) b = (q.comp Algebra.TensorProduct.includeLeft) 1 *
      (MvPolynomial.aeval x) b
    rw [map_one, one_mul, h]

private def differentiateParameter (a : τ → k) : Derivation k P P :=
  MvPolynomial.mkDerivation k (fun r => MvPolynomial.C (a r))

private theorem differentiateParameter_apply (v : τ → 𝔤) (a d : τ → k) (c : C) :
    MvPolynomial.aeval a (differentiateParameter d (adjointParameterPolynomial v c)) =
      ∑ r, d r * v r c := by
  rw [adjointParameterPolynomial, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [differentiateParameter, Derivation.leibniz, MvPolynomial.derivation_C,
    smul_zero, mul_zero, zero_add, MvPolynomial.mkDerivation_X, Algebra.id.smul_eq_mul, map_mul,
    MvPolynomial.aeval_C, Algebra.id.map_eq_id, RingHom.id_apply, mul_comm]

private def adjointFamilyDerivation (u : 𝔤) (d : τ → k) : Derivation k A A :=
  StrictEUnit.mixedRelativeTensorDerivation (0 : Derivation k k k)
    (hopfLieVectorInvariantDerivations u).val (differentiateParameter d) (by simp) (by simp)

private theorem tangentMatrix_mulVec_eq_sum (b : Basis ι k C) (x u : 𝔤) (i : ι) :
    (hopfAdjointTangentMatrix b (fun j => x (b j)) *ᵥ fun j => u (b j)) i =
      ∑ j, u (hopfCotangentProjection k H (hopfAdjointMatrix b i j)) * x (b j) := by
  classical
  rw [← hopfAdjoint_infinitesimal_snd b x u i]
  have h := congrFun (hopfAdjoint_apply_basis b (hopfLieInfinitesimalPoint u) (hopfLieVector_toDual x)) i
  change hopfAdjoint (hopfLieInfinitesimalPoint u) (hopfLieVector_toDual x) (b i) = _ at h
  rw [h]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, TrivSqZeroExt.snd_sum,
    DualNumber.snd_mul, hopfLieVector_toDual_fst, hopfLieVector_toDual_snd,
    mul_zero, zero_add, hopfLieInfinitesimalPoint_snd]

private theorem adjointFamilyDerivation_at_identity
    (b : Basis ι k C) (v : τ → 𝔤) (a d : τ → k) (u : 𝔤) (i : ι) :
    tensorPoint (Bialgebra.counitAlgHom k H) (MvPolynomial.aeval a)
      (adjointFamilyDerivation u d (hopfAdjointFamilyCoordinate b v i)) =
      (hopfAdjointTangentMatrix b (fun j => (∑ r, a r • v r) (b j)) *ᵥ fun j => u (b j)) i +
        ∑ r, d r * v r (b i) := by
  classical
  rw [hopfAdjointFamilyCoordinate, map_sum, map_sum, tangentMatrix_mulVec_eq_sum]
  simp only [adjointFamilyDerivation, StrictEUnit.mixedRelativeTensorDerivation_tmul,
    map_add, tensorPoint_tmul, hopfLieVectorInvariantDerivations_counit,
    adjointParameterPolynomial_apply, differentiateParameter_apply, Finset.sum_add_distrib]
  congr 1
  have hε (j : ι) : Bialgebra.counitAlgHom k H (hopfAdjointMatrix b i j) =
      if i = j then 1 else 0 := hopfAdjointMatrix_counit b i j
  simp only [hε, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

variable [CharZero k] [IsDomain H] [DecidableEq ι]

/-- The full differential makes the coordinate algebra of the adjoint
family contain algebraically independent orbit coordinates. -/
theorem hopfAdjointFamilyCoordinate_algIndep_of_jacobian
    (b : Basis ι k C) (v : τ → 𝔤) (a : τ → k)
    (u : ι → 𝔤) (d : ι → τ → k)
    (hJ : (Matrix.of fun r i =>
      (hopfAdjointTangentMatrix b (fun j => (∑ s, a s • v s) (b j)) *ᵥ fun j => u r (b j)) i +
        ∑ s, d r s * v s (b i)).det ≠ 0) :
    AlgebraicIndependent k (hopfAdjointFamilyCoordinate b v) := by
  classical
  let e : A ≃ₐ[H] MvPolynomial τ H := MvPolynomial.algebraTensorAlgEquiv k H
  letI : IsDomain A := Equiv.isDomain e.toRingEquiv
  let x := hopfAdjointFamilyCoordinate b v
  let D (r : ι) := adjointFamilyDerivation (u r) (d r)
  let p : A →ₐ[k] k := tensorPoint (Bialgebra.counitAlgHom k H) (MvPolynomial.aeval a)
  have h : (Matrix.of fun r i => D r (x i)).map p =
      Matrix.of (fun r i =>
        (hopfAdjointTangentMatrix b (fun j => (∑ s, a s • v s) (b j)) *ᵥ fun j => u r (b j)) i +
          ∑ s, d r s * v s (b i)) :=
    Matrix.ext fun r i => adjointFamilyDerivation_at_identity b v a (d r) (u r) i
  have hDet : (Matrix.of fun r i => D r (x i)).det ≠ 0 := by
    intro h₀
    apply hJ
    rw [← h]
    change (p.toRingHom.mapMatrix (Matrix.of fun r i => D r (x i))).det = 0
    rw [← RingHom.map_det, h₀, map_zero]
  exact algebraicIndependent_of_jacobian_det_ne_zero x D hDet

variable [Algebra.FiniteType k H]

/-- If the adjoint and parameter directions span the tangent space at one
point of the family, the family of actual conjugates contains a principal open. -/
theorem exists_hopfAdjointFamily_principal_open_of_jacobian [IsAlgClosed k]
    (b : Basis ι k C) (v : τ → 𝔤) (a : τ → k)
    (u : ι → 𝔤) (d : ι → τ → k)
    (hJ : (Matrix.of fun r i =>
      (hopfAdjointTangentMatrix b (fun j => (∑ s, a s • v s) (b j)) *ᵥ fun j => u r (b j)) i +
        ∑ s, d r s * v s (b i)).det ≠ 0) :
    ∃ f : MvPolynomial ι k, f ≠ 0 ∧ ∀ x : 𝔤, MvPolynomial.aeval (fun i => x (b i)) f ≠ 0 →
      ∃ (g : H →ₐ[k] k) (c : τ → k), x = hopfAdjoint g (∑ s, c s • v s) := by
  let e : A ≃ₐ[H] MvPolynomial τ H := MvPolynomial.algebraTensorAlgEquiv k H
  letI : IsDomain A := Equiv.isDomain e.toRingEquiv
  letI : Algebra.FiniteType H A := (Algebra.FiniteType.mvPolynomial H τ).equiv e.symm
  letI : Algebra.FiniteType k A := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType k H) (inferInstance : Algebra.FiniteType H A)
  let x := hopfAdjointFamilyCoordinate b v
  obtain ⟨f, hf, hm⟩ := exists_affine_image_principal_open x
    (hopfAdjointFamilyCoordinate_algIndep_of_jacobian b v a u d hJ)
  refine ⟨f, hf, fun y hy => ?_⟩
  obtain ⟨q, hq⟩ := hm (fun i => y (b i)) hy
  let g := q.comp (Algebra.TensorProduct.includeLeft : H →ₐ[k] A)
  let c (r : τ) := (q.comp Algebra.TensorProduct.includeRight) (MvPolynomial.X r)
  refine ⟨g, c, b.ext fun i => ?_⟩
  rw [← hopfAdjointFamilyCoordinate_apply b v g c i, ← tensor_parameterPoint q]
  exact (hq i).symm

universe uΩ

/-- A single ground-field principal open consists of geometric adjoint
conjugates of the parameter family, with the chosen parameter condition. -/
theorem exists_hopfAdjointFamily_principal_open_avoiding_to_algClosed_of_jacobian
    (b : Basis ι k C) (v : τ → 𝔤) (a : τ → k)
    (u : ι → 𝔤) (d : ι → τ → k)
    (s₀ : P) (hs₀ : s₀ ≠ 0)
    (hJ : (Matrix.of fun r i =>
      (hopfAdjointTangentMatrix b (fun j => (∑ s, a s • v s) (b j)) *ᵥ fun j => u r (b j)) i +
        ∑ s, d r s * v s (b i)).det ≠ 0) :
    ∃ f : MvPolynomial ι k, f ≠ 0 ∧ ∀ (Ω : Type uΩ) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
      (x : HopfLieVector k H Ω), MvPolynomial.aeval (fun i => x (b i)) f ≠ 0 →
      ∃ (g : H →ₐ[k] Ω) (c : τ → Ω), MvPolynomial.aeval c s₀ ≠ 0 ∧
        x = hopfAdjoint g (∑ s, c s • (Algebra.ofId k Ω).toLinearMap.comp (v s)) := by
  let e : A ≃ₐ[H] MvPolynomial τ H := MvPolynomial.algebraTensorAlgEquiv k H
  letI : IsDomain A := Equiv.isDomain e.toRingEquiv
  letI : Algebra.FiniteType H A := (Algebra.FiniteType.mvPolynomial H τ).equiv e.symm
  letI : Algebra.FiniteType k A := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType k H) (inferInstance : Algebra.FiniteType H A)
  let sA : A := Algebra.TensorProduct.includeRight s₀
  have hsA : sA ≠ 0 := by
    let p₀ : H →ₐ[k] P := (Algebra.ofId k P).comp (Bialgebra.counitAlgHom k H)
    let q₀ : A →ₐ[k] P := tensorPoint p₀ (AlgHom.id k P)
    intro h
    apply hs₀
    have h₁ : q₀ sA = s₀ := by
      change tensorPoint p₀ (AlgHom.id k P) ((1 : H) ⊗ₜ[k] s₀) = _
      rw [tensorPoint_tmul, map_one, AlgHom.id_apply, one_mul]
    rw [← h₁, h, map_zero]
  obtain ⟨f, hf, hm⟩ := exists_affine_image_principal_open_avoiding_to_algClosed
    (hopfAdjointFamilyCoordinate b v) (hopfAdjointFamilyCoordinate_algIndep_of_jacobian b v a u d hJ) sA hsA
  refine ⟨f, hf, ?_⟩
  intro Ω _ _ _ y hy
  obtain ⟨q, hq, hNonzero⟩ := hm Ω (fun i => y (b i)) hy
  let g := q.comp (Algebra.TensorProduct.includeLeft : H →ₐ[k] A)
  let c (r : τ) := (q.comp Algebra.TensorProduct.includeRight) (MvPolynomial.X r)
  have hc : q.comp Algebra.TensorProduct.includeRight = MvPolynomial.aeval c :=
    MvPolynomial.algHom_ext fun r => (MvPolynomial.aeval_X c r).symm
  refine ⟨g, c, ?_, b.ext fun i => ?_⟩
  · rw [← hc, AlgHom.comp_apply]
    exact hNonzero
  · rw [← hopfAdjointFamilyCoordinate_apply_extension b v g c i, ← tensor_parameterPoint q]
    exact (hq i).symm

end WideE
