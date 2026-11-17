import WideE.MatrixIntertwining
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Determinants of generic linear combinations of matrices. -/

noncomputable section

open scoped Matrix BigOperators
open MvPolynomial

namespace WideE

variable {F n ι : Type*} [Field F] [Fintype n] [DecidableEq n] [Fintype ι]

/-- A linear combination of the matrices with the corresponding formal coefficients. -/
def matrixLinearForm (A : ι → Matrix n n F) : Matrix n n (MvPolynomial ι F) :=
  ∑ i, (X i : MvPolynomial ι F) • (A i).map (C : F →+* MvPolynomial ι F)

/-- The determinant of the matrix with independent linear coefficients. -/
def detMatrixLinearForm (A : ι → Matrix n n F) : MvPolynomial ι F :=
  (matrixLinearForm A).det

theorem eval_detMatrixLinearForm (A : ι → Matrix n n F) (x : ι → F) :
    eval x (detMatrixLinearForm A) = (∑ i, x i • A i).det := by
  rw [detMatrixLinearForm, RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro j k
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, matrixLinearForm, Matrix.sum_apply,
    map_sum, Matrix.smul_apply, smul_eq_mul, map_mul, eval_X, eval_C]

theorem map_detMatrixLinearForm {L : Type*} [Field L] (σ : F →+* L)
    (A : ι → Matrix n n F) :
    map σ (detMatrixLinearForm A) = detMatrixLinearForm (fun i => (A i).map σ) := by
  rw [detMatrixLinearForm, detMatrixLinearForm, RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro j k
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, matrixLinearForm, Matrix.sum_apply,
    map_sum, Matrix.smul_apply, smul_eq_mul, map_mul, map_X, map_C]

theorem detMatrixLinearForm_homogeneous (A : ι → Matrix n n F) :
    (detMatrixLinearForm A).IsHomogeneous (Fintype.card n) := by
  have hentry (j k : n) : (matrixLinearForm A j k).IsHomogeneous 1 := by
    simp only [matrixLinearForm, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
    apply IsHomogeneous.sum
    intro i _
    simpa only [add_zero] using (isHomogeneous_X F i).mul (isHomogeneous_C ι (A i j k))
  rw [detMatrixLinearForm, Matrix.det_apply']
  apply IsHomogeneous.sum
  intro π _
  have hprod : (∏ i, matrixLinearForm A (π i) i).IsHomogeneous (Fintype.card n) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
      IsHomogeneous.prod Finset.univ (fun i => matrixLinearForm A (π i) i)
        (fun _ => 1) (fun i _ => hentry (π i) i)
  have hsign : ((Equiv.Perm.sign π : ℤ) : MvPolynomial ι F).IsHomogeneous 0 := by
    rw [← map_intCast (C : F →+* MvPolynomial ι F)]
    exact isHomogeneous_C _ _
  simpa only [zero_add] using hsign.mul hprod

/-- The generic determinant polynomial is unchanged on applying one automorphism to every matrix. -/
theorem detMatrixLinearForm_algEquiv [Nonempty n]
    (φ : Matrix n n F ≃ₐ[F] Matrix n n F) (A : ι → Matrix n n F) :
    detMatrixLinearForm (fun i => φ (A i)) = detMatrixLinearForm A := by
  obtain ⟨P, hP, h⟩ := exists_matrix_intertwiner φ
  let c : F →+* MvPolynomial ι F := C
  let Q := P.map c
  have hQ : Q.det ≠ 0 := by
    have he := c.map_det P
    change c P.det = Q.det at he
    rw [← he]
    exact fun hzero => hP (C_injective ι F (hzero.trans c.map_zero.symm))
  have hInt :
      matrixLinearForm (fun i => φ (A i)) * Q = Q * matrixLinearForm A := by
    rw [matrixLinearForm, matrixLinearForm, Matrix.sum_mul, Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.smul_mul, Matrix.mul_smul]
    change X i • ((φ (A i)).map c * P.map c) = X i • (P.map c * (A i).map c)
    simp only [← Matrix.map_mul, h (A i)]
  have hd := congrArg Matrix.det hInt
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm Q.det (matrixLinearForm A).det] at hd
  exact mul_right_cancel₀ hQ hd

end WideE
