import WideE.HopfPointGroup
import Mathlib.LinearAlgebra.Matrix.Block

/-! Changing basis and restricting a matrix representation to the quotient by a line. -/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

section Basis

variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]

private def permutationMatrixUnit (e : ι ≃ ι) : (Matrix ι ι k)ˣ where
  val := (1 : Matrix ι ι k).submatrix id e
  inv := (1 : Matrix ι ι k).submatrix e id
  val_inv := by
    rw [Matrix.submatrix_mul_equiv (1 : Matrix ι ι k) 1 id e id, mul_one,
      Matrix.submatrix_id_id]
  inv_val := by
    change (1 : Matrix ι ι k).submatrix e (Equiv.refl ι) *
      (1 : Matrix ι ι k).submatrix (Equiv.refl ι) e = 1
    rw [Matrix.submatrix_mul_equiv (1 : Matrix ι ι k) 1 e (.refl ι) e, mul_one,
      Matrix.submatrix_one_equiv]

/-- A nonzero vector can be put in a specified column of an invertible constant matrix. -/
theorem exists_matrixUnit_column (v : ι → k) (pivot col : ι) (hv : v pivot ≠ 0) :
    ∃ B : (Matrix ι ι k)ˣ, ∀ i, B.val i col = v i := by
  let M := (1 : Matrix ι ι k).updateCol pivot v
  have hV : (fun a : ι => ∑ j, (v j) • (1 : Matrix ι ι k) a j) = v := by
    funext a
    simp [Matrix.one_apply, smul_eq_mul, mul_ite]
  have hDet : M.det = v pivot := by
    have h := Matrix.det_updateCol_sum (1 : Matrix ι ι k) pivot v
    rw [hV, Matrix.det_one, smul_eq_mul, mul_one] at h
    exact h
  have hM : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (hDet ▸ isUnit_iff_ne_zero.mpr hv)
  let e := Equiv.swap col pivot
  let P : (Matrix ι ι k)ˣ := permutationMatrixUnit e
  refine ⟨hM.unit * P, fun i => ?_⟩
  change ∑ j, hM.unit.val i j * (1 : Matrix ι ι k) j (e col) = v i
  rw [show e col = pivot from Equiv.swap_apply_left _ _]
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, hM.unit_spec, M, Matrix.updateCol_self]

end Basis

section Conjugation

variable {k A B ι : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Fintype ι] [DecidableEq ι]

/-- Express a matrix endomorphism in the basis whose columns are `P`. -/
def conjugateMatrixUnit (P : (Matrix ι ι k)ˣ) (U : (Matrix ι ι A)ˣ) : (Matrix ι ι A)ˣ :=
  let P' := P.map (algebraMap k A).mapMatrix.toMonoidHom
  P'⁻¹ * U * P'

theorem conjugateMatrixUnit_map (P : (Matrix ι ι k)ˣ) (U : (Matrix ι ι A)ˣ) (f : A →ₐ[k] B) :
    (conjugateMatrixUnit P U).map f.toRingHom.mapMatrix.toMonoidHom =
      conjugateMatrixUnit P (U.map f.toRingHom.mapMatrix.toMonoidHom) := by
  have h : (P.map (algebraMap k A).mapMatrix.toMonoidHom).map f.toRingHom.mapMatrix.toMonoidHom =
      P.map (algebraMap k B).mapMatrix.toMonoidHom :=
    Units.ext (Matrix.ext fun i j => f.commutes (P.val i j))
  simp only [conjugateMatrixUnit, map_mul, map_inv, h]

theorem conjugateMatrixUnit_mul (P : (Matrix ι ι k)ˣ) (U V : (Matrix ι ι A)ˣ) :
    conjugateMatrixUnit P (U * V) = conjugateMatrixUnit P U * conjugateMatrixUnit P V := by
  let C := P.map (algebraMap k A).mapMatrix.toMonoidHom
  change C⁻¹ * (U * V) * C = (C⁻¹ * U * C) * (C⁻¹ * V * C)
  rw [show (C⁻¹ * U * C) * (C⁻¹ * V * C) = (C⁻¹ * U) * (C * C⁻¹) * V * C by
    simp only [mul_assoc]]
  rw [mul_inv_cancel, mul_one, mul_assoc C⁻¹ U V]

@[simp] theorem conjugateMatrixUnit_one (P : (Matrix ι ι k)ˣ) :
    conjugateMatrixUnit P (1 : (Matrix ι ι A)ˣ) = 1 := by simp [conjugateMatrixUnit]

/-- Conjugating twice corresponds to composing the two changes of basis. -/
theorem conjugateMatrixUnit_conjugate (P Q : (Matrix ι ι k)ˣ) (U : (Matrix ι ι A)ˣ) :
    conjugateMatrixUnit Q (conjugateMatrixUnit P U) = conjugateMatrixUnit (P * Q) U := by
  simp only [conjugateMatrixUnit, map_mul, mul_inv_rev, mul_assoc]

/-- In a basis containing a vector spanning an invariant line, its column
has only the diagonal entry. -/
theorem conjugateMatrixUnit_column_zero (P : (Matrix ι ι k)ˣ) (U : (Matrix ι ι A)ˣ)
    (v : ι → k) (col : ι) (hCol : ∀ i, P.val i col = v i) (c : A)
    (hLine : U.val *ᵥ (algebraMap k A ∘ v) = c • (algebraMap k A ∘ v)) :
    ∀ i ≠ col, (conjugateMatrixUnit P U).val i col = 0 := by
  let P' := P.map (algebraMap k A).mapMatrix.toMonoidHom
  let e : ι → A := Pi.single col 1
  have hP : P'.val *ᵥ e = algebraMap k A ∘ v := by
    rw [show e = Pi.single col 1 from rfl, Matrix.mulVec_single_one]
    exact funext fun i => congrArg (algebraMap k A) (hCol i)
  have hU : (conjugateMatrixUnit P U).val *ᵥ e = c • e := by
    change (P'.inv * U.val * P'.val) *ᵥ e = c • e
    rw [← Matrix.mulVec_mulVec, hP, ← Matrix.mulVec_mulVec, hLine, Matrix.mulVec_smul,
      ← hP, Matrix.mulVec_mulVec, P'.inv_val, Matrix.one_mulVec]
  intro i hi
  have h := congrFun hU i
  simp only [e, Matrix.mulVec_single_one, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero] at h
  exact h

omit [DecidableEq ι] in
private theorem mul_mem_entrywise (S : Subalgebra k A) (M N : Matrix ι ι A)
    (hM : ∀ i j, M i j ∈ S) (hN : ∀ i j, N i j ∈ S) (i j : ι) : (M * N) i j ∈ S := by
  rw [Matrix.mul_apply]
  exact S.sum_mem fun l _ => S.mul_mem (hM i l) (hN l j)

/-- Matrix entries generate the same coefficient algebra in the new basis. -/
theorem conjugateMatrixUnit_generating (P : (Matrix ι ι k)ˣ) (U : (Matrix ι ι A)ˣ)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤) :
    Algebra.adjoin k (Set.range fun ij : ι × ι => (conjugateMatrixUnit P U).val ij.1 ij.2) = ⊤ := by
  let P' := P.map (algebraMap k A).mapMatrix.toMonoidHom
  let V := conjugateMatrixUnit P U
  let S := Algebra.adjoin k (Set.range fun ij : ι × ι => V.val ij.1 ij.2)
  have hV (i j : ι) : V.val i j ∈ S := Algebra.subset_adjoin ⟨(i, j), rfl⟩
  have hPV := mul_mem_entrywise S P'.val V.val (fun _ _ => S.algebraMap_mem _) hV
  have hU : U = P' * V * P'⁻¹ := by
    change U = P' * (P'⁻¹ * U * P') * P'⁻¹
    rw [← mul_assoc P' (P'⁻¹ * U) P', ← mul_assoc P' P'⁻¹ U,
      mul_inv_cancel, one_mul, mul_assoc U P' P'⁻¹, mul_inv_cancel, mul_one]
  apply top_unique
  rw [← hGen]
  apply Algebra.adjoin_le
  rintro _ ⟨⟨i, j⟩, rfl⟩
  change U.val i j ∈ S
  rw [hU]
  exact mul_mem_entrywise S (P'.val * V.val) P'.inv hPV (fun _ _ => S.algebraMap_mem _) i j

end Conjugation

section MatrixCoefficients

variable {k H ι : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H]
  [Fintype ι] [DecidableEq ι]

local notation "Δ" => (Bialgebra.comulAlgHom k H)
local notation "ε" => (Bialgebra.counitAlgHom k H)

/-- The matrix relations are preserved by changing basis over the coefficient ring. -/
theorem conjugateMatrixUnit_hopf (P : (Matrix ι ι k)ˣ) (U : (Matrix ι ι H)ˣ)
    (hD : ∀ a b, Coalgebra.comul (R := k) (U.val a b) = ∑ j, U.val a j ⊗ₜ[k] U.val j b)
    (he : ∀ a b, Coalgebra.counit (R := k) (U.val a b) = if a = b then 1 else 0) :
    let V := conjugateMatrixUnit P U
    (∀ a b, Coalgebra.comul (R := k) (V.val a b) = ∑ j, V.val a j ⊗ₜ[k] V.val j b) ∧
    (∀ a b, Coalgebra.counit (R := k) (V.val a b) = if a = b then 1 else 0) := by
  let V := conjugateMatrixUnit P U
  let L : H →ₐ[k] H ⊗[k] H := Algebra.TensorProduct.includeLeft
  let R : H →ₐ[k] H ⊗[k] H := Algebra.TensorProduct.includeRight
  letI : Group (H →ₐ[k] H ⊗[k] H) := hopfPointGroup
  let ρ := hopfPointMatrix U hD he (A := H ⊗[k] H)
  have hP : L * R = Δ := by
    have hT : tensorPoint L R = AlgHom.id k (H ⊗[k] H) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp only [tensorPoint_tmul, L, R, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul, AlgHom.id_apply]
    change (tensorPoint L R).comp Δ = Δ
    rw [hT, AlgHom.id_comp]
  have hU : U.map (Δ).toRingHom.mapMatrix.toMonoidHom =
      U.map L.toRingHom.mapMatrix.toMonoidHom * U.map R.toRingHom.mapMatrix.toMonoidHom := by
    change ρ Δ = ρ L * ρ R
    rw [← hP, map_mul]
  have hNew : V.map (Δ).toRingHom.mapMatrix.toMonoidHom =
      V.map L.toRingHom.mapMatrix.toMonoidHom * V.map R.toRingHom.mapMatrix.toMonoidHom := by
    simp only [V, conjugateMatrixUnit_map, hU, conjugateMatrixUnit_mul]
  have hCounit : U.map (ε).toRingHom.mapMatrix.toMonoidHom = 1 :=
    Units.ext (Matrix.ext fun i j => (he i j).trans Matrix.one_apply.symm)
  have hOne : V.map (ε).toRingHom.mapMatrix.toMonoidHom = 1 := by
    simp only [V, conjugateMatrixUnit_map, hCounit, conjugateMatrixUnit_one]
  constructor
  · intro i j
    have h := congrArg (fun U : (Matrix ι ι (H ⊗[k] H))ˣ => U.val i j) hNew
    change Coalgebra.comul (R := k) (V.val i j) =
      (V.val.map L * V.val.map R) i j at h
    simpa only [Matrix.mul_apply, Matrix.map_apply, L, R, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul] using h
  · intro i j
    have h := congrArg (fun U : (Matrix ι ι k)ˣ => U.val i j) hOne
    simpa only [Matrix.one_apply] using h

end MatrixCoefficients

section Tail

variable {A : Type*} [CommRing A] {n : ℕ}

private theorem tail_submatrix_mul (M N : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
    (hM : ∀ i : Fin n, M i.succ 0 = 0) :
    (M * N).submatrix Fin.succ Fin.succ =
      M.submatrix Fin.succ Fin.succ * N.submatrix Fin.succ Fin.succ := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_succ, hM, zero_mul, zero_add]

private theorem tail_submatrix_one :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) A).submatrix Fin.succ Fin.succ = 1 := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.one_apply, Fin.succ_inj]

private theorem tail_inv_entry_zero (U : (Matrix (Fin (n + 1)) (Fin (n + 1)) A)ˣ)
    (hU : ∀ i : Fin n, U.val i.succ 0 = 0) (i : Fin n) : U.inv i.succ 0 = 0 := by
  let b (j : Fin (n + 1)) : ℕ := if j = 0 then 0 else 1
  have hB : U.val.BlockTriangular b := by
    intro i j
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp [b, Fin.succ_ne_zero, hU]
  letI : Invertible U.val := Units.invertible U
  have h := Matrix.blockTriangular_inv_of_blockTriangular hB
  change ((U⁻¹ : (Matrix (Fin (n + 1)) (Fin (n + 1)) A)ˣ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) A) i.succ 0 = 0
  rw [Matrix.coe_units_inv]
  exact h (i := i.succ) (j := 0) (by simp [b, Fin.succ_ne_zero])

/-- The induced endomorphism on the quotient by the initial coordinate line. -/
def tailMatrixUnit (U : (Matrix (Fin (n + 1)) (Fin (n + 1)) A)ˣ)
    (hU : ∀ i : Fin n, U.val i.succ 0 = 0) : (Matrix (Fin n) (Fin n) A)ˣ where
  val := U.val.submatrix Fin.succ Fin.succ
  inv := U.inv.submatrix Fin.succ Fin.succ
  val_inv := by rw [← tail_submatrix_mul _ _ hU, U.val_inv, tail_submatrix_one]
  inv_val := by rw [← tail_submatrix_mul _ _ (tail_inv_entry_zero U hU), U.inv_val, tail_submatrix_one]

private def initialBlock (M : Matrix (Fin n) (Fin n) A) : Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
    (fun i' => Fin.cases 0 (fun j' => M i' j') j) i

private theorem initialBlock_mul (M N : Matrix (Fin n) (Fin n) A) :
    initialBlock M * initialBlock N = initialBlock (M * N) := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [initialBlock, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem initialBlock_one : initialBlock (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp [initialBlock, Matrix.one_apply]
  exact (if_neg (Fin.succ_ne_zero _).symm).symm

/-- Extend a change of basis on the quotient by fixing the initial coordinate. -/
def extendTailBasis (P : (Matrix (Fin n) (Fin n) A)ˣ) : (Matrix (Fin (n + 1)) (Fin (n + 1)) A)ˣ where
  val := initialBlock P.val
  inv := initialBlock P.inv
  val_inv := by rw [initialBlock_mul, P.val_inv, initialBlock_one]
  inv_val := by rw [initialBlock_mul, P.inv_val, initialBlock_one]

private theorem firstColumn_mul_zero (M N : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
    (hM : ∀ i : Fin n, M i.succ 0 = 0) (hN : ∀ i : Fin n, N i.succ 0 = 0) (i : Fin n) :
    (M * N) i.succ 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, hM, zero_mul, hN, mul_zero,
    Finset.sum_const_zero, zero_add]

variable {k : Type*} [CommRing k] [Algebra k A]

/-- A basis change on the quotient acts on the lower right block and leaves
the initial line invariant. -/
theorem conjugateMatrixUnit_extendTailBasis (P : (Matrix (Fin n) (Fin n) k)ˣ)
    (U : (Matrix (Fin (n + 1)) (Fin (n + 1)) A)ˣ) (hU : ∀ i : Fin n, U.val i.succ 0 = 0) :
    let V := conjugateMatrixUnit (extendTailBasis P) U
    (∀ i : Fin n, V.val i.succ 0 = 0) ∧
      V.val.submatrix Fin.succ Fin.succ = (conjugateMatrixUnit P (tailMatrixUnit U hU)).val := by
  let C := (extendTailBasis P).map (algebraMap k A).mapMatrix.toMonoidHom
  have hC (i : Fin n) : C.val i.succ 0 = 0 := map_zero (algebraMap k A)
  have hInv (i : Fin n) : C.inv i.succ 0 = 0 := map_zero (algebraMap k A)
  have hL := firstColumn_mul_zero C.inv U.val hInv hU
  constructor
  · exact firstColumn_mul_zero _ _ hL hC
  · change (C.inv * U.val * C.val).submatrix Fin.succ Fin.succ = _
    rw [tail_submatrix_mul _ _ hL, tail_submatrix_mul _ _ hInv]
    rfl

end Tail

variable {k H : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H] {n : ℕ}

theorem tailMatrixUnit_hopf (U : (Matrix (Fin (n + 1)) (Fin (n + 1)) H)ˣ)
    (hU : ∀ i : Fin n, U.val i.succ 0 = 0)
    (hD : ∀ a b, Coalgebra.comul (R := k) (U.val a b) = ∑ j, U.val a j ⊗ₜ[k] U.val j b)
    (he : ∀ a b, Coalgebra.counit (R := k) (U.val a b) = if a = b then 1 else 0) :
    let V := tailMatrixUnit U hU
    (∀ a b, Coalgebra.comul (R := k) (V.val a b) = ∑ j, V.val a j ⊗ₜ[k] V.val j b) ∧
    (∀ a b, Coalgebra.counit (R := k) (V.val a b) = if a = b then 1 else 0) := by
  constructor
  · intro a b
    change Coalgebra.comul (R := k) (U.val a.succ b.succ) =
      ∑ j : Fin n, U.val a.succ j.succ ⊗ₜ[k] U.val j.succ b.succ
    rw [hD, Fin.sum_univ_succ, hU, TensorProduct.zero_tmul, zero_add]
  · intro a b
    change Coalgebra.counit (R := k) (U.val a.succ b.succ) = if a = b then 1 else 0
    simp only [he, Fin.succ_inj]

end WideE
