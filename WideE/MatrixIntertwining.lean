import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Automorphisms of matrix algebras preserve the determinant

A nonzero vector in the image of one transported diagonal matrix unit yields a
common intertwiner by applying the transported column matrix units to this vector.
The intertwiner is invertible because its kernel is stable under all matrices.
-/

noncomputable section

open scoped Matrix BigOperators

namespace WideE

variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

private theorem mul_standardMatrix (A : Matrix n n F) (i j : n) :
    A * Matrix.stdBasisMatrix i j 1 = ∑ k, A k i • Matrix.stdBasisMatrix k j 1 := by
  apply Matrix.ext
  intro k l
  by_cases hl : l = j
  · subst l
    rw [Matrix.StdBasisMatrix.mul_right_apply_same, mul_one, Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.stdBasisMatrix, Matrix.of_apply,
      and_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [Matrix.StdBasisMatrix.mul_right_apply_of_ne _ _ _ _ _ hl, Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.stdBasisMatrix, Matrix.of_apply,
      Ne.symm hl, and_false, if_false, mul_zero, Finset.sum_const_zero]

/-- A single invertible matrix intertwines an algebra automorphism with the identity. -/
theorem exists_matrix_intertwiner [Nonempty n] (φ : Matrix n n F ≃ₐ[F] Matrix n n F) :
    ∃ P : Matrix n n F, P.det ≠ 0 ∧ ∀ A, φ A * P = P * A := by
  classical
  let E (i j : n) : Matrix n n F := Matrix.stdBasisMatrix i j 1
  let a : n := Classical.choice inferInstance
  have hE : E a a ≠ 0 := by
    intro h
    have hEntry := congrArg (fun A : Matrix n n F => A a a) h
    simp [E, Matrix.stdBasisMatrix] at hEntry
  have hφE : φ (E a a) ≠ 0 := fun h => hE (φ.injective (h.trans φ.map_zero.symm))
  have hEntry : ∃ i j, φ (E a a) i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφE (Matrix.ext h)
  obtain ⟨i₀, j₀, hij⟩ := hEntry
  let v : n → F := φ (E a a) *ᵥ Pi.single j₀ 1
  have hv : v ≠ 0 := by
    intro h
    exact hij (by simpa only [v, Matrix.mulVec_single_one, Matrix.transpose_apply,
      Pi.zero_apply] using congrFun h i₀)
  have hvFix : φ (E a a) *ᵥ v = v := by
    dsimp only [v]
    rw [Matrix.mulVec_mulVec, ← map_mul]
    simp only [E, Matrix.StdBasisMatrix.mul_same, one_mul]
  let P : Matrix n n F := Matrix.of fun i j => (φ (E j a) *ᵥ v) i
  let V : Matrix n n F →ₗ[F] (n → F) :=
    { toFun := fun A => φ A *ᵥ v
      map_add' A B := by rw [map_add, Matrix.add_mulVec]
      map_smul' c A := by
        change φ (c • A) *ᵥ v = c • (φ A *ᵥ v)
        rw [show φ (c • A) = c • φ A from φ.toLinearEquiv.map_smul c A,
          Matrix.smul_mulVec_assoc] }
  have hIntertwine (A : Matrix n n F) : φ A * P = P * A := by
    apply Matrix.ext
    intro i j
    have h := congrArg V (mul_standardMatrix A j a)
    simp only [map_sum, map_smul] at h
    calc
      (φ A * P) i j = (φ (A * E j a) *ᵥ v) i := by
        rw [map_mul, ← Matrix.mulVec_mulVec]
        rfl
      _ = ∑ k, A k j * P i k := by
        have hi := congrFun h i
        change (φ (A * E j a) *ᵥ v) i = (∑ k, A k j • (fun l => P l k)) i at hi
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hi
      _ = (P * A) i j := by simp only [Matrix.mul_apply, mul_comm]
  refine ⟨P, ?_, hIntertwine⟩
  intro hdet
  obtain ⟨x, hx, hPx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hNonzero : ∃ j, x j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨j, hj⟩ := hNonzero
  have h := congrArg (fun A : Matrix n n F => A *ᵥ x) (hIntertwine (E a j))
  simp only [← Matrix.mulVec_mulVec, hPx, Matrix.mulVec_zero] at h
  have hColumn : P *ᵥ (Pi.single a 1 : n → F) = v := by
    rw [Matrix.mulVec_single_one]
    exact hvFix
  have hEvec : E a j *ᵥ x = x j • (Pi.single a 1 : n → F) := by
    dsimp only [E]
    rw [Matrix.mulVec_stdBasisMatrix]
    funext i
    by_cases hi : i = a
    · subst i
      simp
    · simp [hi, Ne.symm hi, Pi.single_apply, Function.update_of_ne hi]
  rw [hEvec, Matrix.mulVec_smul, hColumn] at h
  exact (smul_eq_zero.mp h.symm).elim hj hv

/-- In particular, algebra automorphisms of a matrix algebra preserve its determinant. -/
theorem det_matrix_algEquiv [Nonempty n] (φ : Matrix n n F ≃ₐ[F] Matrix n n F) (A : Matrix n n F) :
    (φ A).det = A.det := by
  obtain ⟨P, hP, h⟩ := exists_matrix_intertwiner φ
  have hd := congrArg Matrix.det (h A)
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm P.det A.det] at hd
  exact mul_right_cancel₀ hP hd

end WideE
