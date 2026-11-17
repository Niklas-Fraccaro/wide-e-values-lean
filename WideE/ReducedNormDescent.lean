import WideE.MatrixDetLinearForm
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Descent of the reduced norm from a split matrix algebra

Given a splitting isomorphism over a Galois extension, each Galois-conjugate
generic matrix is related to the original by a scalar-linear automorphism.
The generic determinant therefore has coefficients in the base field.
-/

noncomputable section

open scoped Matrix TensorProduct BigOperators
open MvPolynomial

namespace WideE

section SplitMatrices

variable {K L D n : Type*} [Field K] [Field L] [Algebra K L]
variable [Ring D] [Algebra K D] [Fintype n] [DecidableEq n]

/-- Entrywise Galois conjugation on the image of the original algebra agrees
with a scalar-linear automorphism of the split matrix algebra. -/
theorem exists_algEquiv_map_splitMatrices
    (e : L ⊗[K] D ≃ₐ[L] Matrix n n L) (σ : L ≃ₐ[K] L) :
    ∃ φ : Matrix n n L ≃ₐ[L] Matrix n n L,
      ∀ x : D, φ (e (1 ⊗ₜ[K] x)) = (e (1 ⊗ₜ[K] x)).map σ := by
  let T : L ⊗[K] D ≃ₐ[K] L ⊗[K] D :=
    Algebra.TensorProduct.congr σ.symm (AlgEquiv.refl : D ≃ₐ[K] D)
  let eK := e.restrictScalars K
  let W : Matrix n n L ≃ₐ[K] Matrix n n L := ((eK.symm.trans T).trans eK).trans σ.mapMatrix
  have hT (a : L) : T (algebraMap L (L ⊗[K] D) a) = algebraMap L (L ⊗[K] D) (σ.symm a) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have hScalar (a : L) : σ.mapMatrix (algebraMap L (Matrix n n L) (σ.symm a)) =
      algebraMap L (Matrix n n L) a := by
    apply Matrix.ext
    intro i j
    simp only [AlgEquiv.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply,
      Algebra.id.map_eq_self, apply_ite σ, AlgEquiv.apply_symm_apply, map_zero]
  let φ : Matrix n n L ≃ₐ[L] Matrix n n L :=
    { W.toRingEquiv with
      commutes' := by
        intro a
        change σ.mapMatrix (e (T (e.symm (algebraMap L (Matrix n n L) a)))) = _
        rw [e.symm.commutes, hT, e.commutes, hScalar] }
  refine ⟨φ, ?_⟩
  intro x
  change σ.mapMatrix (e (T (e.symm (e (1 ⊗ₜ[K] x))))) = _
  rw [e.symm_apply_apply]
  have hx : T (1 ⊗ₜ[K] x) = 1 ⊗ₜ[K] x := by
    change σ.symm 1 ⊗ₜ[K] x = 1 ⊗ₜ[K] x
    rw [map_one]
  rw [hx, AlgEquiv.mapMatrix_apply]

end SplitMatrices

section GaloisDescent

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

private theorem homogeneous_polynomial_of_invariant
    {p : MvPolynomial ι L} {d : ℕ} (hp : p.IsHomogeneous d)
    (hFix : ∀ σ : L ≃ₐ[K] L, map σ.toRingHom p = p) :
    ∃ q : MvPolynomial ι K, q.IsHomogeneous d ∧ map (algebraMap K L) q = p := by
  classical
  have hc (s : ι →₀ ℕ) : ∃ a : K, algebraMap K L a = p.coeff s := by
    have hmem : p.coeff s ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) := by
      apply (IntermediateField.mem_fixedField_iff _ _).mpr
      intro σ _
      have h := congrArg (coeff s) (hFix σ)
      rw [coeff_map] at h
      exact h
    rw [InfiniteGalois.fixedField_bot] at hmem
    exact IntermediateField.mem_bot.mp hmem
  choose a ha using hc
  let q : MvPolynomial ι K := ∑ s ∈ p.support, monomial s (a s)
  refine ⟨q, ?_, ?_⟩
  · apply IsHomogeneous.sum
    intro s hs
    exact isHomogeneous_monomial _ ((congrFun Finsupp.degree_eq_weight_one s).trans
      (hp (mem_support_iff.mp hs)))
  · dsimp only [q]
    rw [map_sum]
    simpa only [map_monomial, ha] using p.as_sum.symm

variable {D n : Type*} [Ring D] [Algebra K D]
variable [Fintype n] [DecidableEq n] [Nonempty n] [Fintype ι]

/-- The generic determinant of a split representation descends over a Galois extension. -/
theorem exists_reducedNorm_polynomial_of_galois_splitting
    (e : L ⊗[K] D ≃ₐ[L] Matrix n n L) (b : ι → D) :
    ∃ q : MvPolynomial ι K, q.IsHomogeneous (Fintype.card n) ∧
      map (algebraMap K L) q = detMatrixLinearForm (fun i => e (1 ⊗ₜ[K] b i)) := by
  let A (i : ι) : Matrix n n L := e (1 ⊗ₜ[K] b i)
  apply homogeneous_polynomial_of_invariant (detMatrixLinearForm_homogeneous A)
  intro σ
  obtain ⟨φ, hφ⟩ := exists_algEquiv_map_splitMatrices e σ
  rw [map_detMatrixLinearForm]
  have h : (fun i => (A i).map σ.toRingHom) = fun i => φ (A i) := funext fun i => (hφ (b i)).symm
  rw [h]
  exact detMatrixLinearForm_algEquiv φ A

end GaloisDescent
end WideE
