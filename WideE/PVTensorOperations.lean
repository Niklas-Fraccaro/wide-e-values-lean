import WideE.PicardVessiot
import WideE.PVNaturality
import MatrixGeneratedChangeBasis

/-! Tensor products and duals of the ordinary normalized Laurent systems. -/

noncomputable section

open scoped WideE Matrix Kronecker

namespace WideE

open StrictEUnit

section MatrixUnits

variable {R ι κ : Type*} [CommRing R]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The tensor product of two invertible matrices is invertible. -/
def kroneckerMatrixUnit (U : (Matrix ι ι R)ˣ) (V : (Matrix κ κ R)ˣ) :
    (Matrix (ι × κ) (ι × κ) R)ˣ where
  val := U.val ⊗ₖ V.val
  inv := (↑U⁻¹ : Matrix ι ι R) ⊗ₖ (↑V⁻¹ : Matrix κ κ R)
  val_inv := by rw [← Matrix.mul_kronecker_mul, Units.mul_inv, Units.mul_inv, Matrix.one_kronecker_one]
  inv_val := by rw [← Matrix.mul_kronecker_mul, Units.inv_mul, Units.inv_mul, Matrix.one_kronecker_one]

/-- The inverse transpose of an invertible matrix acts on the dual. -/
def dualMatrixUnit (U : (Matrix ι ι R)ˣ) : (Matrix ι ι R)ˣ where
  val := (↑U⁻¹ : Matrix ι ι R).transpose
  inv := U.val.transpose
  val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

end MatrixUnits

section TensorUnits

variable {S T : Type*} [CommRing S] [CommRing T] {m n : ℕ}

/-- The tensor product of invertible matrices in the product basis indexed by `Fin (m * n)`. -/
def tensorMatrixUnit (U : (Matrix (Fin m) (Fin m) S)ˣ) (V : (Matrix (Fin n) (Fin n) S)ˣ) :
    (Matrix (Fin (m * n)) (Fin (m * n)) S)ˣ :=
  reindexMatrixUnit finProdFinEquiv (kroneckerMatrixUnit U V)

@[simp] theorem tensorMatrixUnit_val (U : (Matrix (Fin m) (Fin m) S)ˣ)
    (V : (Matrix (Fin n) (Fin n) S)ˣ) :
    (tensorMatrixUnit U V).val = Matrix.reindex finProdFinEquiv finProdFinEquiv (U.val ⊗ₖ V.val) := rfl

/-- Mapping the coefficients of a tensor unit maps both of its factors. -/
theorem map_tensorMatrixUnit (f : S →+* T) (U : (Matrix (Fin m) (Fin m) S)ˣ)
    (V : (Matrix (Fin n) (Fin n) S)ˣ) :
    Units.map f.mapMatrix.toMonoidHom (tensorMatrixUnit U V) =
      tensorMatrixUnit (Units.map f.mapMatrix.toMonoidHom U) (Units.map f.mapMatrix.toMonoidHom V) := by
  apply Units.ext
  change Matrix.reindex finProdFinEquiv finProdFinEquiv ((U.val ⊗ₖ V.val).map f) =
    Matrix.reindex finProdFinEquiv finProdFinEquiv (U.val.map f ⊗ₖ V.val.map f)
  rw [matrix_map_kronecker]

/-- Normalizing a tensor unit at the chosen point normalizes both of its factors. -/
theorem normalizeMatrixAt_tensor {k : Type*} [CommRing k] (E : S →+* k) (C : k →+* S)
    (U : (Matrix (Fin m) (Fin m) S)ˣ) (V : (Matrix (Fin n) (Fin n) S)ˣ) :
    normalizeMatrixAt E C (tensorMatrixUnit U V) =
      tensorMatrixUnit (normalizeMatrixAt E C U) (normalizeMatrixAt E C V) := by
  let e := Matrix.reindexAlgEquiv S S (finProdFinEquiv (m := m) (n := n))
  let U₀ := Units.map (C.comp E).mapMatrix.toMonoidHom U
  let V₀ := Units.map (C.comp E).mapMatrix.toMonoidHom V
  simp only [normalizeMatrixAt, map_tensorMatrixUnit]
  apply Units.ext
  change e (U.val ⊗ₖ V.val) * e ((U₀⁻¹).val ⊗ₖ (V₀⁻¹).val) =
    e ((U.val * (U₀⁻¹).val) ⊗ₖ (V.val * (V₀⁻¹).val))
  rw [← map_mul, ← Matrix.mul_kronecker_mul]

end TensorUnits

section LaurentSystems

variable {K : Type*} [Field K] {m n : ℕ}

local notation "R" => LaurentPolynomial K
local notation "P" => PowerSeries K

/-- The Laurent matrix on the tensor product, with its product basis indexed by `Fin (m * n)`. -/
def tensorLaurentSystem (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (m * n)) (Fin (m * n)) R :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (A ⊗ₖ (1 : Matrix (Fin n) (Fin n) R) + (1 : Matrix (Fin m) (Fin m) R) ⊗ₖ B)

/-- The Laurent matrix of the dual connection in the dual basis. -/
def dualLaurentSystem (A : Matrix (Fin m) (Fin m) R) : Matrix (Fin m) (Fin m) R :=
  -A.transpose

private theorem formalUnit_atOne (A : Matrix (Fin m) (Fin m) R) :
    (formalFundamentalAtOneUnit A).val.map (PowerSeries.constantCoeff K) = 1 := by
  simp only [formalFundamentalAtOneUnit_val, formalFundamentalMatrix_constantCoeff]

variable [CharZero K]

private theorem formalUnit_derivative (A : Matrix (Fin m) (Fin m) R) :
    (formalFundamentalAtOneUnit A).val.map (PowerSeries.derivative K) =
      A.map (formalAtOne K) * (formalFundamentalAtOneUnit A).val := by
  simp only [formalFundamentalAtOneUnit_val, formalFundamentalMatrix_derivative]

/-- The normalized fundamental matrix of a tensor product is the Kronecker
product of the normalized fundamental matrices of its two factors. -/
theorem formalFundamentalAtOneUnit_tensorSystem
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) :
    (formalFundamentalAtOneUnit (tensorLaurentSystem A B)).val =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((formalFundamentalAtOneUnit A).val ⊗ₖ (formalFundamentalAtOneUnit B).val) := by
  let e := finProdFinEquiv (m := m) (n := n)
  let E := Matrix.reindexAlgEquiv P P e
  let f := (formalAtOne K).toRingHom
  let A' := A.map f
  let B' := B.map f
  let C := tensorLaurentSystem A B
  let Y := (formalFundamentalAtOneUnit A).val
  let Z := (formalFundamentalAtOneUnit B).val
  let L := A' ⊗ₖ (1 : Matrix (Fin n) (Fin n) P) + (1 : Matrix (Fin m) (Fin m) P) ⊗ₖ B'
  have hC : C.map f = E L := by
    change Matrix.reindex e e
      ((A ⊗ₖ (1 : Matrix (Fin n) (Fin n) R) + (1 : Matrix (Fin m) (Fin m) R) ⊗ₖ B).map f) = E L
    simp only [Matrix.map_add f f.map_add, matrix_map_kronecker, Matrix.map_one f f.map_zero f.map_one]
    rfl
  have hY : Y.map (PowerSeries.derivative K) = A' * Y := formalUnit_derivative A
  have hZ : Z.map (PowerSeries.derivative K) = B' * Z := formalUnit_derivative B
  have hTensor : (Y ⊗ₖ Z).map (PowerSeries.derivative K) = L * (Y ⊗ₖ Z) := by
    simp only [L, matrix_deriv_kronecker, hY, hZ, Matrix.add_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have hDerivative : (E (Y ⊗ₖ Z)).map (PowerSeries.derivative K) = C.map f * E (Y ⊗ₖ Z) := by
    have h := congrArg E hTensor
    rw [map_mul, ← hC] at h
    exact h
  have hTensor₀ : (Y ⊗ₖ Z).map (PowerSeries.constantCoeff K) = 1 := by
    rw [matrix_map_kronecker, show Y.map (PowerSeries.constantCoeff K) = 1 from formalUnit_atOne A,
      show Z.map (PowerSeries.constantCoeff K) = 1 from formalUnit_atOne B, Matrix.one_kronecker_one]
  have hAtOne : (E (Y ⊗ₖ Z)).map (PowerSeries.constantCoeff K) = 1 := by
    have h := congrArg (Matrix.reindexAlgEquiv K K e) hTensor₀
    rwa [map_one] at h
  exact (normalized_fundamental_eq (formalFundamentalAtOneUnit C) (formalUnit_derivative C)
    hDerivative (formalUnit_atOne C) hAtOne).symm

/-- The normalized fundamental matrix for the dual connection is the inverse
transpose of the original normalized fundamental matrix. -/
theorem formalFundamentalAtOneUnit_dualSystem (A : Matrix (Fin m) (Fin m) R) :
    (formalFundamentalAtOneUnit (dualLaurentSystem A)).val =
      (↑(formalFundamentalAtOneUnit A)⁻¹ : Matrix (Fin m) (Fin m) P).transpose := by
  let Y := formalFundamentalAtOneUnit A
  let B := A.map (formalAtOne K)
  let C := dualLaurentSystem A
  let f := (formalAtOne K).toRingHom
  have hC : C.map f = -B.transpose := by
    apply Matrix.ext
    intro i j
    exact map_neg f (A j i)
  have hInv : (↑Y⁻¹ : Matrix (Fin m) (Fin m) P).map (PowerSeries.derivative K) =
      -((↑Y⁻¹ : Matrix (Fin m) (Fin m) P) * B) := by
    rw [matrix_deriv_inv, show Y.val.map (PowerSeries.derivative K) = B * Y.val from formalUnit_derivative A]
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hDerivative : ((↑Y⁻¹ : Matrix (Fin m) (Fin m) P).transpose).map (PowerSeries.derivative K) =
      C.map f * (↑Y⁻¹ : Matrix (Fin m) (Fin m) P).transpose := by
    change ((↑Y⁻¹ : Matrix (Fin m) (Fin m) P).map (PowerSeries.derivative K)).transpose = _
    rw [hInv, Matrix.transpose_neg, Matrix.transpose_mul, hC, Matrix.neg_mul]
  have hInv₀ : (↑Y⁻¹ : Matrix (Fin m) (Fin m) P).map (PowerSeries.constantCoeff K) = 1 := by
    have h := congrArg (PowerSeries.constantCoeff K).mapMatrix (Units.mul_inv Y)
    simpa only [map_mul, map_one, RingHom.mapMatrix_apply,
      show Y.val.map (PowerSeries.constantCoeff K) = 1 from formalUnit_atOne A, Matrix.one_mul] using h
  have hAtOne : ((↑Y⁻¹ : Matrix (Fin m) (Fin m) P).transpose).map (PowerSeries.constantCoeff K) = 1 := by
    change ((↑Y⁻¹ : Matrix (Fin m) (Fin m) P).map (PowerSeries.constantCoeff K)).transpose = 1
    rw [hInv₀, Matrix.transpose_one]
  exact (normalized_fundamental_eq (formalFundamentalAtOneUnit C) (formalUnit_derivative C)
    hDerivative (formalUnit_atOne C) hAtOne).symm

end LaurentSystems

section AmbientMatrices

variable {K : Type*} [Field K] {m n : ℕ}

local notation "R" => LaurentPolynomial K
local notation "L" => LaurentSeries K

/-- The normalized fundamental matrix as a unit over the ambient Laurent series field. -/
def ordinaryFundamentalMatrixUnit (A : Matrix (Fin m) (Fin m) R) : (Matrix (Fin m) (Fin m) L)ˣ :=
  Units.map (powerSeriesInLaurent K).toRingHom.mapMatrix.toMonoidHom (formalFundamentalAtOneUnit A)

@[simp] theorem ordinaryFundamentalMatrixUnit_val (A : Matrix (Fin m) (Fin m) R) :
    (ordinaryFundamentalMatrixUnit A).val = ordinaryFundamental A := by
  change (formalFundamentalAtOneUnit A).val.map (powerSeriesInLaurent K) = ordinaryFundamental A
  rw [formalFundamentalAtOneUnit_val]
  rfl

variable [CharZero K]

theorem ordinaryFundamental_combinedSystem (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin n) (Fin n) R) :
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (ordinaryFundamental (combinedLaurentSystem A B)) =
      Matrix.fromBlocks (ordinaryFundamental A) 0 0 (ordinaryFundamental B) := by
  let f := (powerSeriesInLaurent K).toRingHom
  let e := finSumFinEquiv (m := m) (n := n)
  have h := congrArg (fun M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) (PowerSeries K) => M.map f)
    (formalFundamentalAtOneUnit_combinedSystem A B)
  change Matrix.reindex e.symm e.symm (ordinaryFundamentalMatrixUnit (combinedLaurentSystem A B)).val =
    (Matrix.fromBlocks (formalFundamentalAtOneUnit A).val 0 0 (formalFundamentalAtOneUnit B).val).map f at h
  rw [Matrix.fromBlocks_map, Matrix.map_zero f f.map_zero, Matrix.map_zero f f.map_zero] at h
  change Matrix.reindex e.symm e.symm (ordinaryFundamentalMatrixUnit (combinedLaurentSystem A B)).val =
    Matrix.fromBlocks (ordinaryFundamentalMatrixUnit A).val 0 0 (ordinaryFundamentalMatrixUnit B).val at h
  simpa only [ordinaryFundamentalMatrixUnit_val] using h

theorem ordinaryFundamental_tensorSystem
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) :
    ordinaryFundamental (tensorLaurentSystem A B) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (ordinaryFundamental A ⊗ₖ ordinaryFundamental B) := by
  let f := (powerSeriesInLaurent K).toRingHom
  let e := finProdFinEquiv (m := m) (n := n)
  have h := congrArg (fun M : Matrix (Fin (m * n)) (Fin (m * n)) (PowerSeries K) => M.map f)
    (formalFundamentalAtOneUnit_tensorSystem A B)
  change (ordinaryFundamentalMatrixUnit (tensorLaurentSystem A B)).val =
    Matrix.reindex e e (((formalFundamentalAtOneUnit A).val ⊗ₖ (formalFundamentalAtOneUnit B).val).map f) at h
  rw [matrix_map_kronecker] at h
  change (ordinaryFundamentalMatrixUnit (tensorLaurentSystem A B)).val =
    Matrix.reindex e e ((ordinaryFundamentalMatrixUnit A).val ⊗ₖ (ordinaryFundamentalMatrixUnit B).val) at h
  simpa only [ordinaryFundamentalMatrixUnit_val] using h

theorem ordinaryFundamental_dualSystem (A : Matrix (Fin m) (Fin m) R) :
    ordinaryFundamental (dualLaurentSystem A) =
      (↑(ordinaryFundamentalMatrixUnit A)⁻¹ : Matrix (Fin m) (Fin m) L).transpose := by
  rw [← ordinaryFundamentalMatrixUnit_val (dualLaurentSystem A)]
  change (formalFundamentalAtOneUnit (dualLaurentSystem A)).val.map (powerSeriesInLaurent K) = _
  rw [formalFundamentalAtOneUnit_dualSystem, ordinaryFundamentalMatrixUnit, ← map_inv]
  rfl

end AmbientMatrices

section Subalgebras

private theorem matrixGeneratedAlgebra_le_of_unit {R L ι : Type*} [CommRing R] [Field L]
    [Algebra R L] [Fintype ι] [DecidableEq ι] (S : Subalgebra R L)
    {Z : Matrix ι ι L} (Y : (Matrix ι ι S)ˣ) (hY : Y.val.map S.val = Z) :
    matrixGeneratedAlgebra (B := R) Z ≤ S := by
  let f := S.val.toRingHom
  have hdet : Z.det = f Y.val.det := by rw [← hY]; exact (f.map_det Y.val).symm
  have hprod : Z.det * f (↑Y⁻¹ : Matrix ι ι S).det = 1 := by
    have h := congrArg Matrix.det (Units.mul_inv Y)
    simp only [Matrix.det_mul, Matrix.det_one] at h
    rw [hdet, ← map_mul, h, map_one]
  refine (matrixGeneratedAlgebra_le_iff Z S).mpr ⟨?_, fun i j => ?_⟩
  · rw [inv_eq_of_mul_eq_one_right hprod]
    exact (↑Y⁻¹ : Matrix ι ι S).det.property
  · rw [← hY]
    exact (Y.val i j).property

variable {K : Type*} [Field K] {m n : ℕ}

local notation "R" => LaurentPolynomial K
local notation "L" => LaurentSeries K

private def ordinaryPVMatrixIn (A : Matrix (Fin m) (Fin m) R) {S : Subalgebra R L}
    (h : ordinaryPVAlgebra A ≤ S) : (Matrix (Fin m) (Fin m) S)ˣ :=
  Units.map (Subalgebra.inclusion h).toRingHom.mapMatrix.toMonoidHom (ordinaryPVMatrix A)

private theorem ordinaryPVMatrixIn_val (A : Matrix (Fin m) (Fin m) R) {S : Subalgebra R L}
    (h : ordinaryPVAlgebra A ≤ S) :
    (ordinaryPVMatrixIn A h).val.map S.val = ordinaryFundamental A := by
  apply Matrix.ext
  intro i j
  change ((ordinaryPVMatrix A).val i j).val = ordinaryFundamental A i j
  rw [ordinaryPVMatrix, candidateMatrixUnit_val]
  rfl

variable [CharZero K]

/-- A Laurent subalgebra containing the two fundamental matrix units also
contains the Picard–Vessiot algebra of their tensor product. -/
theorem ordinaryPVAlgebra_tensorSystem_le (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin n) (Fin n) R) {S : Subalgebra R L}
    (hA : ordinaryPVAlgebra A ≤ S) (hB : ordinaryPVAlgebra B ≤ S) :
    ordinaryPVAlgebra (tensorLaurentSystem A B) ≤ S := by
  letI : CommRing S := S.toCommRing
  letI : Mul S := S.toCommRing.toMul
  let e := finProdFinEquiv (m := m) (n := n)
  let Y : (Matrix (Fin m) (Fin m) S)ˣ := ordinaryPVMatrixIn A hA
  let Z : (Matrix (Fin n) (Fin n) S)ˣ := ordinaryPVMatrixIn B hB
  apply matrixGeneratedAlgebra_le_of_unit S (tensorMatrixUnit Y Z)
  change Matrix.reindex e e ((Y.val ⊗ₖ Z.val).map S.val.toRingHom) = _
  rw [matrix_map_kronecker]
  change Matrix.reindex e e ((Y.val.map S.val) ⊗ₖ (Z.val.map S.val)) = _
  rw [ordinaryPVMatrixIn_val, ordinaryPVMatrixIn_val, ordinaryFundamental_tensorSystem]

/-- The tensor product algebra is contained in the join of the two factor algebras. -/
theorem ordinaryPVAlgebra_tensorSystem_le_sup (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin n) (Fin n) R) :
    ordinaryPVAlgebra (tensorLaurentSystem A B) ≤ ordinaryPVAlgebra A ⊔ ordinaryPVAlgebra B :=
  ordinaryPVAlgebra_tensorSystem_le A B le_sup_left le_sup_right

set_option maxHeartbeats 900000 in
/-- The ordinary Picard–Vessiot algebra of the direct sum is generated by both factors. -/
theorem ordinaryPVAlgebra_combinedSystem_eq_sup (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin n) (Fin n) R) :
    ordinaryPVAlgebra (combinedLaurentSystem A B) = ordinaryPVAlgebra A ⊔ ordinaryPVAlgebra B := by
  let e := finSumFinEquiv (m := m) (n := n)
  let C := combinedLaurentSystem A B
  have hBlock := ordinaryFundamental_combinedSystem A B
  apply le_antisymm
  · let S := ordinaryPVAlgebra A ⊔ ordinaryPVAlgebra B
    let YA := ordinaryPVMatrixIn A (S := S) le_sup_left
    let YB := ordinaryPVMatrixIn B (S := S) le_sup_right
    apply matrixGeneratedAlgebra_le_of_unit S (reindexMatrixUnit e (blockDiagonalMatrixUnit YA YB))
    change Matrix.reindex e e ((Matrix.fromBlocks YA.val 0 0 YB.val).map S.val) = ordinaryFundamental C
    rw [Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero S.val), Matrix.map_zero _ (map_zero S.val)]
    rw [show YA.val.map S.val = ordinaryFundamental A from ordinaryPVMatrixIn_val A le_sup_left,
      show YB.val.map S.val = ordinaryFundamental B from ordinaryPVMatrixIn_val B le_sup_right, ← hBlock]
    exact (Matrix.reindex e e).apply_symm_apply _
  · let S := ordinaryPVAlgebra C
    letI : CommRing S := S.toCommRing
    let Y : (Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) S)ˣ :=
      reindexMatrixUnit e.symm (ordinaryPVMatrixIn C (le_refl S))
    have hY : Y.val.map S.val = Matrix.fromBlocks (ordinaryFundamental A) 0 0 (ordinaryFundamental B) := by
      change Matrix.reindex e.symm e.symm ((ordinaryPVMatrixIn C (le_refl S)).val.map S.val) = _
      rw [ordinaryPVMatrixIn_val]
      exact hBlock
    have hinj : Function.Injective S.val := Subtype.val_injective
    have h₁₂ : Y.val.toBlocks₁₂ = 0 := by
      apply Matrix.map_injective hinj
      simpa only [Matrix.toBlocks_fromBlocks₁₂, Matrix.map_zero _ (map_zero S.val)] using
        congrArg Matrix.toBlocks₁₂ hY
    have h₂₁ : Y.val.toBlocks₂₁ = 0 := by
      apply Matrix.map_injective hinj
      simpa only [Matrix.toBlocks_fromBlocks₂₁, Matrix.map_zero _ (map_zero S.val)] using
        congrArg Matrix.toBlocks₂₁ hY
    apply sup_le
    · apply matrixGeneratedAlgebra_le_of_unit S (firstBlockUnit Y h₁₂ h₂₁)
      simpa only [Matrix.toBlocks_fromBlocks₁₁] using congrArg Matrix.toBlocks₁₁ hY
    · apply matrixGeneratedAlgebra_le_of_unit S (secondBlockUnit Y h₁₂ h₂₁)
      simpa only [Matrix.toBlocks_fromBlocks₂₂] using congrArg Matrix.toBlocks₂₂ hY

/-- A direct-sum Picard–Vessiot algebra provides a common algebra for the tensor system. -/
theorem ordinaryPVAlgebra_tensorSystem_le_combinedSystem (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin n) (Fin n) R) :
    ordinaryPVAlgebra (tensorLaurentSystem A B) ≤ ordinaryPVAlgebra (combinedLaurentSystem A B) := by
  rw [ordinaryPVAlgebra_combinedSystem_eq_sup]
  exact ordinaryPVAlgebra_tensorSystem_le_sup A B

/-- Forming the dual uses only the matrix unit over the original Picard–Vessiot algebra. -/
theorem ordinaryPVAlgebra_dualSystem_le (A : Matrix (Fin m) (Fin m) R) :
    ordinaryPVAlgebra (dualLaurentSystem A) ≤ ordinaryPVAlgebra A := by
  let S := ordinaryPVAlgebra A
  letI : CommRing S := S.toCommRing
  let Y := ordinaryPVMatrixIn A (le_refl S)
  let i : Matrix (Fin m) (Fin m) S →* Matrix (Fin m) (Fin m) L := S.val.toRingHom.mapMatrix.toMonoidHom
  have h : Units.map i Y = ordinaryFundamentalMatrixUnit A := by
    apply Units.ext
    rw [ordinaryFundamentalMatrixUnit_val]
    exact ordinaryPVMatrixIn_val A (le_refl S)
  apply matrixGeneratedAlgebra_le_of_unit S (dualMatrixUnit Y)
  rw [ordinaryFundamental_dualSystem]
  have hInv := congrArg (fun U : (Matrix (Fin m) (Fin m) L)ˣ => (U⁻¹).val.transpose) h
  change (↑(Units.map i Y)⁻¹ : Matrix (Fin m) (Fin m) L).transpose = _ at hInv
  rw [← map_inv] at hInv
  exact hInv

/-- The original system and its dual generate the same ordinary Picard–Vessiot algebra. -/
theorem ordinaryPVAlgebra_dualSystem_eq (A : Matrix (Fin m) (Fin m) R) :
    ordinaryPVAlgebra (dualLaurentSystem A) = ordinaryPVAlgebra A := by
  refine le_antisymm (ordinaryPVAlgebra_dualSystem_le A) ?_
  have h : dualLaurentSystem (dualLaurentSystem A) = A := by
    simp only [dualLaurentSystem, Matrix.transpose_neg, Matrix.transpose_transpose, neg_neg]
  simpa only [h] using ordinaryPVAlgebra_dualSystem_le (dualLaurentSystem A)

end Subalgebras

end WideE
