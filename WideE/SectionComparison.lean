import WideE.Horizontal
import WideE.OrdinaryPoint
import FormalFundamentalMatrixUnit
import FundamentalMatrixConstants
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# From a common fundamental matrix to a comparison over the Kummer ring

The product and one are identities over the common algebra of coefficients of the
fundamental solutions. Each identity therefore survives application of a section.
-/

noncomputable section

open scoped Matrix Kronecker

namespace WideE

section BlockUnits

variable {R ι κ : Type*} [CommRing R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Combine two matrix units on the direct sum of their coordinate spaces. -/
def blockDiagonalMatrixUnit (U : (Matrix ι ι R)ˣ) (V : (Matrix κ κ R)ˣ) :
    (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ where
  val := Matrix.fromBlocks (U : Matrix ι ι R) 0 0 (V : Matrix κ κ R)
  inv := Matrix.fromBlocks (↑U⁻¹ : Matrix ι ι R) 0 0 (↑V⁻¹ : Matrix κ κ R)
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

@[simp] theorem blockDiagonalMatrixUnit_val (U : (Matrix ι ι R)ˣ) (V : (Matrix κ κ R)ˣ) :
    (blockDiagonalMatrixUnit U V : Matrix (ι ⊕ κ) (ι ⊕ κ) R) =
      Matrix.fromBlocks (U : Matrix ι ι R) 0 0 (V : Matrix κ κ R) := rfl

section BlockMultiplication

omit [DecidableEq ι] [DecidableEq κ]

private theorem toBlocks₁₁_mul (A B : Matrix (ι ⊕ κ) (ι ⊕ κ) R) :
    (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ + A.toBlocks₁₂ * B.toBlocks₂₁ := by
  have h := Matrix.fromBlocks_multiply A.toBlocks₁₁ A.toBlocks₁₂ A.toBlocks₂₁ A.toBlocks₂₂
    B.toBlocks₁₁ B.toBlocks₁₂ B.toBlocks₂₁ B.toBlocks₂₂
  rw [Matrix.fromBlocks_toBlocks, Matrix.fromBlocks_toBlocks] at h
  simpa only [Matrix.toBlocks_fromBlocks₁₁] using congrArg Matrix.toBlocks₁₁ h

private theorem toBlocks₂₂_mul (A B : Matrix (ι ⊕ κ) (ι ⊕ κ) R) :
    (A * B).toBlocks₂₂ = A.toBlocks₂₁ * B.toBlocks₁₂ + A.toBlocks₂₂ * B.toBlocks₂₂ := by
  have h := Matrix.fromBlocks_multiply A.toBlocks₁₁ A.toBlocks₁₂ A.toBlocks₂₁ A.toBlocks₂₂
    B.toBlocks₁₁ B.toBlocks₁₂ B.toBlocks₂₁ B.toBlocks₂₂
  rw [Matrix.fromBlocks_toBlocks, Matrix.fromBlocks_toBlocks] at h
  simpa only [Matrix.toBlocks_fromBlocks₂₂] using congrArg Matrix.toBlocks₂₂ h

end BlockMultiplication

omit [Fintype ι] [Fintype κ] in
private theorem toBlocks₁₁_one : (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) R).toBlocks₁₁ = 1 := by
  rw [← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]

omit [Fintype ι] [Fintype κ] in
private theorem toBlocks₂₂_one : (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) R).toBlocks₂₂ = 1 := by
  rw [← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂]

/-- The first diagonal block of a block-diagonal matrix unit is a unit. -/
def firstBlockUnit (Y : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ)
    (h₁₂ : (Y : Matrix (ι ⊕ κ) (ι ⊕ κ) R).toBlocks₁₂ = 0)
    (h₂₁ : (Y : Matrix (ι ⊕ κ) (ι ⊕ κ) R).toBlocks₂₁ = 0) : (Matrix ι ι R)ˣ where
  val := (Y : Matrix (ι ⊕ κ) (ι ⊕ κ) R).toBlocks₁₁
  inv := (↑Y⁻¹ : Matrix (ι ⊕ κ) (ι ⊕ κ) R).toBlocks₁₁
  val_inv := by
    simpa only [toBlocks₁₁_mul, h₁₂, Matrix.zero_mul, add_zero, toBlocks₁₁_one] using
      congrArg Matrix.toBlocks₁₁ (Units.mul_inv Y)
  inv_val := by
    simpa only [toBlocks₁₁_mul, h₂₁, Matrix.mul_zero, add_zero, toBlocks₁₁_one] using
      congrArg Matrix.toBlocks₁₁ (Units.inv_mul Y)

/-- The second diagonal block of a block-diagonal matrix unit is a unit. -/
def secondBlockUnit (Y : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ)
    (h₁₂ : (Y : Matrix (ι ⊕ κ) (ι ⊕ κ) R).toBlocks₁₂ = 0)
    (h₂₁ : (Y : Matrix (ι ⊕ κ) (ι ⊕ κ) R).toBlocks₂₁ = 0) : (Matrix κ κ R)ˣ where
  val := (Y : Matrix (ι ⊕ κ) (ι ⊕ κ) R).toBlocks₂₂
  inv := (↑Y⁻¹ : Matrix (ι ⊕ κ) (ι ⊕ κ) R).toBlocks₂₂
  val_inv := by
    simpa only [toBlocks₂₂_mul, h₂₁, Matrix.zero_mul, zero_add, toBlocks₂₂_one] using
      congrArg Matrix.toBlocks₂₂ (Units.mul_inv Y)
  inv_val := by
    simpa only [toBlocks₂₂_mul, h₁₂, Matrix.mul_zero, zero_add, toBlocks₂₂_one] using
      congrArg Matrix.toBlocks₂₂ (Units.inv_mul Y)

/-- Relabel the rows and columns of a matrix unit simultaneously. -/
def reindexMatrixUnit (e : ι ≃ κ) (Y : (Matrix ι ι R)ˣ) : (Matrix κ κ R)ˣ :=
  Units.map (Matrix.reindexAlgEquiv R R e).toRingEquiv.toMonoidHom Y

@[simp] theorem reindexMatrixUnit_val (e : ι ≃ κ) (Y : (Matrix ι ι R)ˣ) :
    (reindexMatrixUnit e Y : Matrix κ κ R) = Matrix.reindex e e (Y : Matrix ι ι R) := rfl

end BlockUnits

section FormalBlocks

variable {K ι κ : Type*} [CommRing K] [NoZeroSMulDivisors ℕ K]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The invertible formal fundamental matrix with identity constant term is unique. -/
theorem normalized_fundamental_eq {B Z : Matrix ι ι (PowerSeries K)}
    (Y : (Matrix ι ι (PowerSeries K))ˣ)
    (hY : (Y : Matrix ι ι (PowerSeries K)).map (PowerSeries.derivative K) =
      B * (Y : Matrix ι ι (PowerSeries K)))
    (hZ : Z.map (PowerSeries.derivative K) = B * Z)
    (hY₀ : (Y : Matrix ι ι (PowerSeries K)).map (PowerSeries.constantCoeff K) = 1)
    (hZ₀ : Z.map (PowerSeries.constantCoeff K) = 1) : Z = (Y : Matrix ι ι (PowerSeries K)) := by
  have h := horizontal_recover_of_specialized_gauge (PowerSeries.derivative K) (PowerSeries.constantCoeff K)
    (fun p hp => (powerSeries_eq_C_of_derivative_eq_zero p hp).symm)
    (1 : Matrix ι ι (PowerSeries K)) Y Z
    (by
      rw [Matrix.mul_one]
      exact StrictEUnit.fundamental_matrix_transition_constant (PowerSeries.derivative K) B Y Z hY hZ)
    (Matrix.map_one _ (map_zero _) (map_one _)) hY₀
  rw [Matrix.mul_one, hZ₀, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h
  exact h

/-- A direct sum of systems has the block-diagonal direct sum of their normalized solutions. -/
theorem normalized_block_fundamental_eq
    {BM : Matrix ι ι (PowerSeries K)} {BN : Matrix κ κ (PowerSeries K)}
    {Z : Matrix (ι ⊕ κ) (ι ⊕ κ) (PowerSeries K)}
    (YM : (Matrix ι ι (PowerSeries K))ˣ) (YN : (Matrix κ κ (PowerSeries K))ˣ)
    (hM : (YM : Matrix ι ι (PowerSeries K)).map (PowerSeries.derivative K) =
      BM * (YM : Matrix ι ι (PowerSeries K)))
    (hN : (YN : Matrix κ κ (PowerSeries K)).map (PowerSeries.derivative K) =
      BN * (YN : Matrix κ κ (PowerSeries K)))
    (hZ : Z.map (PowerSeries.derivative K) = Matrix.fromBlocks BM 0 0 BN * Z)
    (hM₀ : (YM : Matrix ι ι (PowerSeries K)).map (PowerSeries.constantCoeff K) = 1)
    (hN₀ : (YN : Matrix κ κ (PowerSeries K)).map (PowerSeries.constantCoeff K) = 1)
    (hZ₀ : Z.map (PowerSeries.constantCoeff K) = 1) :
    Z = Matrix.fromBlocks (YM : Matrix ι ι (PowerSeries K)) 0 0 (YN : Matrix κ κ (PowerSeries K)) := by
  refine normalized_fundamental_eq (B := Matrix.fromBlocks BM 0 0 BN) (Z := Z)
    (blockDiagonalMatrixUnit YM YN) ?_ hZ ?_ hZ₀
  · simp only [blockDiagonalMatrixUnit_val, Matrix.fromBlocks_map, hM, hN, Matrix.map_zero,
      map_zero, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  · simp only [blockDiagonalMatrixUnit_val, Matrix.fromBlocks_map, hM₀, hN₀,
      Matrix.map_zero, map_zero, Matrix.fromBlocks_one]

end FormalBlocks

section SectionComparison

open LaurentPolynomial

variable {K S L ι κ : Type*} [CommRing K] [CommRing S]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {q : ℕ} (base : LaurentPolynomial K →+* S) (φ : S →+* LaurentPolynomial K)
variable (hφ : φ.comp base = kummer K q)
variable {F : Matrix κ (ι × ι) (LaurentPolynomial K)} {u : κ → LaurentPolynomial K}

/-- Applying a section sends both identities over the common algebra to the Kummer ring. -/
def laurentComparison_of_section (YM : (Matrix ι ι S)ˣ) (YN : (Matrix κ κ S)ˣ)
    (hF : F.map base * ((YM : Matrix ι ι S) ⊗ₖ (YM : Matrix ι ι S)) =
      (YN : Matrix κ κ S) * ((F.map (evalAtOne K)).map C).map base)
    (hU : (YN : Matrix κ κ S) *ᵥ (base ∘ C ∘ evalAtOne K ∘ u) = base ∘ u) :
    LaurentCoordinateComparison K q (fun i j l => F l (i, j)) u := by
  have hbase (p : LaurentPolynomial K) : φ (base p) = kummer K q p := DFunLike.congr_fun hφ p
  simpa only [LaurentCoordinateComparison, Matrix.map_apply, Function.comp_apply, hbase,
    kummer_C, evalAtOne_kummer] using (CoordinateComparison.ofTensorMatrix YM YN hF hU).map φ

variable [CommRing L]

/-- An embedded common matrix supplies the product and unit comparisons over its own algebra. -/
def coordinateComparison_of_embedded
    (emb : S →+* L) (hEmb : Function.Injective emb)
    (Y : (Matrix (ι ⊕ κ) (ι ⊕ κ) S)ˣ) {YM : Matrix ι ι L} {YN : Matrix κ κ L}
    (hY : (Y : Matrix (ι ⊕ κ) (ι ⊕ κ) S).map emb = Matrix.fromBlocks YM 0 0 YN)
    (hF : F.map (emb.comp base) * (YM ⊗ₖ YM) =
      YN * ((F.map (evalAtOne K)).map C).map (emb.comp base))
    (hU : YN *ᵥ ((emb.comp base) ∘ C ∘ evalAtOne K ∘ u) = (emb.comp base) ∘ u) :
    CoordinateComparison
      (fun i j l => base (C (evalAtOne K (F l (i, j))))) (fun i j l => base (F l (i, j)))
      (base ∘ C ∘ evalAtOne K ∘ u) (base ∘ u) := by
  have h₁₂ : (Y : Matrix (ι ⊕ κ) (ι ⊕ κ) S).toBlocks₁₂ = 0 := by
    apply Matrix.map_injective hEmb
    simpa only [Matrix.toBlocks_fromBlocks₁₂, Matrix.map_zero, map_zero] using
      congrArg Matrix.toBlocks₁₂ hY
  have h₂₁ : (Y : Matrix (ι ⊕ κ) (ι ⊕ κ) S).toBlocks₂₁ = 0 := by
    apply Matrix.map_injective hEmb
    simpa only [Matrix.toBlocks_fromBlocks₂₁, Matrix.map_zero, map_zero] using
      congrArg Matrix.toBlocks₂₁ hY
  let U := firstBlockUnit Y h₁₂ h₂₁
  let V := secondBlockUnit Y h₁₂ h₂₁
  have hU' : (U : Matrix ι ι S).map emb = YM := by
    simpa only [Matrix.toBlocks_fromBlocks₁₁] using congrArg Matrix.toBlocks₁₁ hY
  have hV' : (V : Matrix κ κ S).map emb = YN := by
    simpa only [Matrix.toBlocks_fromBlocks₂₂] using congrArg Matrix.toBlocks₂₂ hY
  refine CoordinateComparison.ofTensorMatrix
    (F₀ := ((F.map (evalAtOne K)).map C).map base) (F := F.map base) U V ?_ ?_
  · apply Matrix.map_injective hEmb
    simpa only [Matrix.map_mul, matrix_map_kronecker, hU', hV', Matrix.map_map, RingHom.coe_comp] using hF
  · funext l
    apply hEmb
    rw [RingHom.map_mulVec, hV']
    exact congrFun hU l

/-- An embedded common matrix supplies the two comparison matrices over the section ring. -/
def laurentComparison_of_embedded_section
    (emb : S →+* L) (hEmb : Function.Injective emb)
    (Y : (Matrix (ι ⊕ κ) (ι ⊕ κ) S)ˣ) {YM : Matrix ι ι L} {YN : Matrix κ κ L}
    (hY : (Y : Matrix (ι ⊕ κ) (ι ⊕ κ) S).map emb = Matrix.fromBlocks YM 0 0 YN)
    (hF : F.map (emb.comp base) * (YM ⊗ₖ YM) =
      YN * ((F.map (evalAtOne K)).map C).map (emb.comp base))
    (hU : YN *ᵥ ((emb.comp base) ∘ C ∘ evalAtOne K ∘ u) = (emb.comp base) ∘ u) :
    LaurentCoordinateComparison K q (fun i j l => F l (i, j)) u := by
  have hbase (p : LaurentPolynomial K) : φ (base p) = kummer K q p := DFunLike.congr_fun hφ p
  simpa only [LaurentCoordinateComparison, Function.comp_apply, hbase, kummer_C, evalAtOne_kummer]
    using (coordinateComparison_of_embedded base emb hEmb Y hY hF hU).map φ

end SectionComparison

section LaurentSystems

open StrictEUnit LaurentPolynomial

variable {K : Type*} [Field K] {m n r : ℕ}

/-- The system on the two modules together, indexed by `Fin (m + n)`. -/
def combinedLaurentSystem (BM : Matrix (Fin m) (Fin m) (LaurentPolynomial K))
    (BN : Matrix (Fin n) (Fin n) (LaurentPolynomial K)) :
    Matrix (Fin (m + n)) (Fin (m + n)) (LaurentPolynomial K) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks BM 0 0 BN)

/-- The ordinary-point fundamental matrix, bundled as a power-series matrix unit. -/
def formalFundamentalAtOneUnit (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    (Matrix (Fin r) (Fin r) (PowerSeries K))ˣ :=
  (formalFundamentalMatrix_isUnit (A.map (formalAtOne K))).unit

@[simp] theorem formalFundamentalAtOneUnit_val (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    (formalFundamentalAtOneUnit A : Matrix (Fin r) (Fin r) (PowerSeries K)) =
      formalFundamentalMatrix (A.map (formalAtOne K)) := IsUnit.unit_spec _

private theorem matrix_reindex_map {ι κ R S : Type*} (e : ι ≃ κ) (f : R → S) (M : Matrix ι ι R) :
    ((Matrix.reindex e e) M).map f = (Matrix.reindex e e) (M.map f) := rfl

variable [CharZero K]

private theorem formalFundamentalAtOneUnit_derivative (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    (formalFundamentalAtOneUnit A : Matrix (Fin r) (Fin r) (PowerSeries K)).map (PowerSeries.derivative K) =
      A.map (formalAtOne K) * (formalFundamentalAtOneUnit A : Matrix (Fin r) (Fin r) (PowerSeries K)) := by
  simp only [formalFundamentalAtOneUnit_val, formalFundamentalMatrix_derivative]

omit [CharZero K] in
private theorem formalFundamentalAtOneUnit_atOne (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    (formalFundamentalAtOneUnit A : Matrix (Fin r) (Fin r) (PowerSeries K)).map (PowerSeries.constantCoeff K) = 1 := by
  simp only [formalFundamentalAtOneUnit_val, formalFundamentalMatrix_constantCoeff]

variable (BM : Matrix (Fin m) (Fin m) (LaurentPolynomial K))
variable (BN : Matrix (Fin n) (Fin n) (LaurentPolynomial K))

/-- The fundamental solution of the common system is the block-diagonal fundamental solution. -/
theorem formalFundamentalAtOneUnit_combinedSystem :
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
      (formalFundamentalAtOneUnit (combinedLaurentSystem BM BN) : Matrix (Fin (m + n)) (Fin (m + n)) (PowerSeries K)) =
      Matrix.fromBlocks (formalFundamentalAtOneUnit BM : Matrix (Fin m) (Fin m) (PowerSeries K)) 0 0
        (formalFundamentalAtOneUnit BN : Matrix (Fin n) (Fin n) (PowerSeries K)) := by
  let e := finSumFinEquiv (m := m) (n := n)
  let E := Matrix.reindexAlgEquiv (PowerSeries K) (PowerSeries K) e.symm
  let A := combinedLaurentSystem BM BN
  let Y : Matrix (Fin (m + n)) (Fin (m + n)) (PowerSeries K) := ↑(formalFundamentalAtOneUnit A)
  have hA : E (A.map (formalAtOne K)) =
      Matrix.fromBlocks (BM.map (formalAtOne K)) 0 0 (BN.map (formalAtOne K)) := by
    change Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (A.map (formalAtOne K)) = _
    simp only [A, combinedLaurentSystem, matrix_reindex_map, ← Matrix.reindex_symm,
      Equiv.symm_apply_apply, Matrix.fromBlocks_map, Matrix.map_zero, map_zero]
  have hY : (E Y).map (PowerSeries.derivative K) =
      Matrix.fromBlocks (BM.map (formalAtOne K)) 0 0 (BN.map (formalAtOne K)) * E Y := by
    have h := congrArg E (formalFundamentalAtOneUnit_derivative A)
    rw [map_mul, hA] at h
    exact h
  have hY₀ : (E Y).map (PowerSeries.constantCoeff K) = 1 := by
    have h := congrArg (Matrix.reindexAlgEquiv K K e.symm) (formalFundamentalAtOneUnit_atOne A)
    rw [map_one] at h
    exact h
  exact normalized_block_fundamental_eq (formalFundamentalAtOneUnit BM) (formalFundamentalAtOneUnit BN)
    (formalFundamentalAtOneUnit_derivative BM) (formalFundamentalAtOneUnit_derivative BN) hY
    (formalFundamentalAtOneUnit_atOne BM) (formalFundamentalAtOneUnit_atOne BN) hY₀

variable {F : Matrix (Fin n) (Fin m × Fin m) (LaurentPolynomial K)}
variable {u : Fin n → LaurentPolynomial K}

private theorem formalFundamentalAtOneUnit_product
    (hF : F.map laurentDerivation = BN * F - F *
      (BM ⊗ₖ (1 : Matrix (Fin m) (Fin m) (LaurentPolynomial K)) +
        (1 : Matrix (Fin m) (Fin m) (LaurentPolynomial K)) ⊗ₖ BM)) :
    F.map (formalAtOne K) * ((formalFundamentalAtOneUnit BM : Matrix (Fin m) (Fin m) (PowerSeries K)) ⊗ₖ
      (formalFundamentalAtOneUnit BM : Matrix (Fin m) (Fin m) (PowerSeries K))) =
      (formalFundamentalAtOneUnit BN : Matrix (Fin n) (Fin n) (PowerSeries K)) *
        (F.map (evalAtOne K)).map (PowerSeries.C K) := by
  let E := (formalAtOne K).toRingHom
  have hF' : (F.map (formalAtOne K)).map (PowerSeries.derivative K) =
      BN.map (formalAtOne K) * F.map (formalAtOne K) - F.map (formalAtOne K) *
        ((BM.map (formalAtOne K)) ⊗ₖ (1 : Matrix (Fin m) (Fin m) (PowerSeries K)) +
          (1 : Matrix (Fin m) (Fin m) (PowerSeries K)) ⊗ₖ (BM.map (formalAtOne K))) := by
    have h := congrArg (fun A : Matrix (Fin n) (Fin m × Fin m) (LaurentPolynomial K) => A.map E) hF
    simp only [Matrix.map_sub E E.map_sub, Matrix.map_mul, Matrix.map_add E E.map_add,
      matrix_map_kronecker, Matrix.map_one E E.map_zero E.map_one] at h
    refine Eq.trans ?_ h
    apply Matrix.ext
    intro l ij
    exact formalAtOne_derivative K (F l ij)
  have h := horizontal_mul_at_ordinary_point (formalFundamentalAtOneUnit BM) (formalFundamentalAtOneUnit BN)
    (formalFundamentalAtOneUnit_derivative BM) (formalFundamentalAtOneUnit_derivative BN) hF'
    (formalFundamentalAtOneUnit_atOne BM) (formalFundamentalAtOneUnit_atOne BN)
  have h₀ : (F.map (formalAtOne K)).map (PowerSeries.constantCoeff K) = F.map (evalAtOne K) := by
    apply Matrix.ext
    intro l ij
    exact formalAtOne_constantCoeff K (F l ij)
  rwa [h₀] at h

private theorem formalFundamentalAtOneUnit_one
    (hU : laurentDerivation ∘ u = BN *ᵥ u) :
    (formalFundamentalAtOneUnit BN : Matrix (Fin n) (Fin n) (PowerSeries K)) *ᵥ
      (PowerSeries.C K ∘ evalAtOne K ∘ u) = formalAtOne K ∘ u := by
  have hU' : PowerSeries.derivative K ∘ (formalAtOne K ∘ u) =
      BN.map (formalAtOne K) *ᵥ (formalAtOne K ∘ u) := by
    funext l
    simp only [Function.comp_apply, formalAtOne_derivative]
    have hz : laurentDerivation (u l) = (BN *ᵥ u) l := congrFun hU l
    rw [hz]
    exact RingHom.map_mulVec (formalAtOne K).toRingHom BN u l
  have h := horizontal_unit_at_ordinary_point (formalFundamentalAtOneUnit BN)
    (formalFundamentalAtOneUnit_derivative BN) hU' (formalFundamentalAtOneUnit_atOne BN)
  have h₀ : PowerSeries.C K ∘ PowerSeries.constantCoeff K ∘ (formalAtOne K ∘ u) =
      PowerSeries.C K ∘ evalAtOne K ∘ u := by
    funext l
    simp only [Function.comp_apply, formalAtOne_constantCoeff]
  rwa [h₀] at h

/-- The formal fundamental solution yields the product and unit identities in the common algebra. -/
def coordinateComparison_of_formal
    {S L : Type*} [CommRing S] [CommRing L]
    (base : LaurentPolynomial K →+* S)
    (emb : S →+* L) (hEmb : Function.Injective emb) (J : PowerSeries K →+* L)
    (hBase : emb.comp base = J.comp (formalAtOne K).toRingHom)
    (Y : (Matrix (Fin (m + n)) (Fin (m + n)) S)ˣ)
    (hY : (Y : Matrix (Fin (m + n)) (Fin (m + n)) S).map emb =
      (formalFundamentalAtOneUnit (combinedLaurentSystem BM BN) :
        Matrix (Fin (m + n)) (Fin (m + n)) (PowerSeries K)).map J)
    (hF : F.map laurentDerivation = BN * F - F *
      (BM ⊗ₖ (1 : Matrix (Fin m) (Fin m) (LaurentPolynomial K)) +
        (1 : Matrix (Fin m) (Fin m) (LaurentPolynomial K)) ⊗ₖ BM))
    (hU : laurentDerivation ∘ u = BN *ᵥ u) :
    CoordinateComparison
      (fun i j l => base (C (evalAtOne K (F l (i, j))))) (fun i j l => base (F l (i, j)))
      (base ∘ C ∘ evalAtOne K ∘ u) (base ∘ u) := by
  let e := finSumFinEquiv (m := m) (n := n)
  let YM : Matrix (Fin m) (Fin m) (PowerSeries K) := ↑(formalFundamentalAtOneUnit BM)
  let YN : Matrix (Fin n) (Fin n) (PowerSeries K) := ↑(formalFundamentalAtOneUnit BN)
  have hBase' (a : LaurentPolynomial K) : (emb.comp base) a = J (formalAtOne K a) :=
    DFunLike.congr_fun hBase a
  refine coordinateComparison_of_embedded base emb hEmb
    (reindexMatrixUnit e.symm Y) (YM := YM.map J) (YN := YN.map J) ?_ ?_ ?_
  · rw [reindexMatrixUnit_val, matrix_reindex_map, hY, ← matrix_reindex_map,
      formalFundamentalAtOneUnit_combinedSystem]
    simp only [Matrix.fromBlocks_map, Matrix.map_zero, map_zero, YM, YN]
  · have hF' := congrArg (fun A : Matrix (Fin n) (Fin m × Fin m) (PowerSeries K) => A.map J)
      (formalFundamentalAtOneUnit_product BM BN hF)
    have hmap : (F.map (formalAtOne K)).map J = F.map (emb.comp base) := by
      apply Matrix.ext
      intro l ij
      exact (hBase' (F l ij)).symm
    have hmap₀ : ((F.map (evalAtOne K)).map (PowerSeries.C K)).map J =
        ((F.map (evalAtOne K)).map C).map (emb.comp base) := by
      apply Matrix.ext
      intro l ij
      simp only [Matrix.map_apply, hBase', formalAtOne_C]
    simpa only [Matrix.map_mul, matrix_map_kronecker, hmap, hmap₀] using hF'
  · have hmap : J ∘ (PowerSeries.C K ∘ evalAtOne K ∘ u) =
        (emb.comp base) ∘ C ∘ evalAtOne K ∘ u := by
      funext l
      simp only [Function.comp_apply, hBase', formalAtOne_C]
    funext l
    have h := congrArg J (congrFun (formalFundamentalAtOneUnit_one BN hU) l)
    simpa only [RingHom.map_mulVec, hmap, Function.comp_apply, hBase'] using h

/-- A section of an algebra containing the common formal fundamental matrix gives a comparison. -/
def laurentComparison_of_formal_section
    {S L : Type*} [CommRing S] [CommRing L] {q : ℕ}
    (base : LaurentPolynomial K →+* S) (φ : S →+* LaurentPolynomial K)
    (hφ : φ.comp base = kummer K q)
    (emb : S →+* L) (hEmb : Function.Injective emb) (J : PowerSeries K →+* L)
    (hBase : emb.comp base = J.comp (formalAtOne K).toRingHom)
    (Y : (Matrix (Fin (m + n)) (Fin (m + n)) S)ˣ)
    (hY : (Y : Matrix (Fin (m + n)) (Fin (m + n)) S).map emb =
      (formalFundamentalAtOneUnit (combinedLaurentSystem BM BN) :
        Matrix (Fin (m + n)) (Fin (m + n)) (PowerSeries K)).map J)
    (hF : F.map laurentDerivation = BN * F - F *
      (BM ⊗ₖ (1 : Matrix (Fin m) (Fin m) (LaurentPolynomial K)) +
        (1 : Matrix (Fin m) (Fin m) (LaurentPolynomial K)) ⊗ₖ BM))
    (hU : laurentDerivation ∘ u = BN *ᵥ u) :
    LaurentCoordinateComparison K q (fun i j l => F l (i, j)) u := by
  have hbase (p : LaurentPolynomial K) : φ (base p) = kummer K q p := DFunLike.congr_fun hφ p
  simpa only [LaurentCoordinateComparison, Function.comp_apply, hbase, kummer_C, evalAtOne_kummer]
    using (coordinateComparison_of_formal BM BN base emb hEmb J hBase Y hY hF hU).map φ

end LaurentSystems
end WideE
