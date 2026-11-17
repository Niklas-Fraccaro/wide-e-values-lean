import WideE.PicardVessiot
import WideE.SectionComparison
import WideE.Kummer
import WideE.ModuleCoordinates

/-! The ordinary Picard–Vessiot algebra supplies the common formal matrix for the comparison. -/

noncomputable section

open scoped WideE Matrix Kronecker

namespace WideE

open StrictEUnit

section AdditiveDerivative

variable {K : Type*} [CommRing K]

local instance (priority := 3000) : Module (LaurentPolynomial K) (LaurentPolynomial K) :=
  Semiring.toModule

private def laurentDerivationAdd : LaurentPolynomial K →+ LaurentPolynomial K :=
  (laurentDerivation (K := K)).toLinearMap.toAddMonoidHom

end AdditiveDerivative

variable {K : Type*} [Field K] [CharZero K] {m n q : ℕ}
variable (BM : Matrix (Fin m) (Fin m) (LaurentPolynomial K))
variable (BN : Matrix (Fin n) (Fin n) (LaurentPolynomial K))
variable {F : Matrix (Fin n) (Fin m × Fin m) (LaurentPolynomial K)}
variable {u : Fin n → LaurentPolynomial K}

/-- The normalized product and unit comparison in the actual PV algebra. -/
def coordinateComparison_of_ordinaryPV
    (hF : F.map laurentDerivation = BN * F - F *
      (BM ⊗ₖ (1 : Matrix (Fin m) (Fin m) (LaurentPolynomial K)) +
        (1 : Matrix (Fin m) (Fin m) (LaurentPolynomial K)) ⊗ₖ BM))
    (hU : laurentDerivation ∘ u = BN *ᵥ u) :
    let A := combinedLaurentSystem BM BN
    let base := algebraMap (LaurentPolynomial K) (ordinaryPVAlgebra A)
    CoordinateComparison
      (fun i j l => base (LaurentPolynomial.C (evalAtOne K (F l (i, j)))))
      (fun i j l => base (F l (i, j)))
      (base ∘ LaurentPolynomial.C ∘ evalAtOne K ∘ u) (base ∘ u) := by
  let A := combinedLaurentSystem BM BN
  let S := ordinaryPVAlgebra A
  let emb : S →+* LaurentSeries K := (Subalgebra.val (ordinaryPVAlgebra A)).toRingHom
  let J := (powerSeriesInLaurent K).toRingHom
  refine coordinateComparison_of_formal BM BN (algebraMap (LaurentPolynomial K) S)
    emb Subtype.val_injective J ?_ (ordinaryPVMatrix A) ?_ hF hU
  · rfl
  · rw [formalFundamentalAtOneUnit_val]
    simp only [ordinaryPVMatrix, candidateMatrixUnit_val]
    rfl

/-- The first comparison matrix is the first block of the ordinary fundamental matrix. -/
theorem coordinateComparison_of_ordinaryPV_onM
    (hF : F.map laurentDerivation = BN * F - F *
      (BM ⊗ₖ (1 : Matrix (Fin m) (Fin m) (LaurentPolynomial K)) +
        (1 : Matrix (Fin m) (Fin m) (LaurentPolynomial K)) ⊗ₖ BM))
    (hU : laurentDerivation ∘ u = BN *ᵥ u) :
    (coordinateComparison_of_ordinaryPV BM BN hF hU).onM.val = Matrix.toBlocks₁₁
      (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
        (ordinaryPVMatrix (combinedLaurentSystem BM BN)).val) := rfl

/-- Apply an ordinary Picard–Vessiot section to the comparison identities. -/
def comparison_of_ordinaryPV_section
    (φ : ordinaryPVAlgebra (combinedLaurentSystem BM BN) →+* LaurentPolynomial K)
    (hφ : φ.comp (algebraMap (LaurentPolynomial K) (ordinaryPVAlgebra (combinedLaurentSystem BM BN))) =
      kummer K q)
    (hF : F.map laurentDerivation = BN * F - F *
      (BM ⊗ₖ (1 : Matrix (Fin m) (Fin m) (LaurentPolynomial K)) +
        (1 : Matrix (Fin m) (Fin m) (LaurentPolynomial K)) ⊗ₖ BM))
    (hU : laurentDerivation ∘ u = BN *ᵥ u) :
    LaurentCoordinateComparison K q (fun i j l => F l (i, j)) u := by
  have hbase (p : LaurentPolynomial K) :
      φ (algebraMap (LaurentPolynomial K) (ordinaryPVAlgebra (combinedLaurentSystem BM BN)) p) =
        kummer K q p := DFunLike.congr_fun hφ p
  simpa only [LaurentCoordinateComparison, Function.comp_apply, hbase, kummer_C, evalAtOne_kummer]
    using (coordinateComparison_of_ordinaryPV BM BN hF hU).map φ

/-- A section as an algebra map into the Kummer extension supplies the comparison. -/
def comparison_of_ordinaryPV_kummer_section
    (s : ordinaryPVAlgebra (combinedLaurentSystem BM BN) →ₐ[LaurentPolynomial K] KummerExtension K q)
    (hF : F.map laurentDerivation = BN * F - F *
      (BM ⊗ₖ (1 : Matrix (Fin m) (Fin m) (LaurentPolynomial K)) +
        (1 : Matrix (Fin m) (Fin m) (LaurentPolynomial K)) ⊗ₖ BM))
    (hU : laurentDerivation ∘ u = BN *ᵥ u) :
    LaurentCoordinateComparison K q (fun i j l => F l (i, j)) u :=
  comparison_of_ordinaryPV_section BM BN
    ((KummerExtension.toLaurent K q).toRingHom.comp s.toRingHom)
    (RingHom.ext fun p => congrArg (KummerExtension.toLaurent K q) (s.commutes p)) hF hU

section ModuleComparison

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
variable [Module (LaurentPolynomial K) M] [Module (LaurentPolynomial K) N]

/-- Compare two modules whose product and distinguished unit are horizontal. -/
def comparison_of_module_kummer_section
    (bM : Basis (Fin m) (LaurentPolynomial K) M) (bN : Basis (Fin n) (LaurentPolynomial K) N)
    (DM : M →+ M) (DN : N →+ N) (P : M →ₗ[LaurentPolynomial K] M →ₗ[LaurentPolynomial K] N)
    (one : N)
    (hDN : ∀ (a : LaurentPolynomial K) (x : N), DN (a • x) = laurentDerivation a • x + a • DN x)
    (hP : ∀ x y, DN (P x y) = P (DM x) y + P x (DM y))
    (hOne : DN one = 0)
    (s : ordinaryPVAlgebra (combinedLaurentSystem (connectionSystemMatrix bM DM)
        (connectionSystemMatrix bN DN)) →ₐ[LaurentPolynomial K] KummerExtension K q) :
    LaurentCoordinateComparison K q
      (fun i j l => productCoefficientMatrix bM bN P l (i, j)) (bN.repr one) := by
  let δ := laurentDerivationAdd (K := K)
  exact comparison_of_ordinaryPV_kummer_section (connectionSystemMatrix bM DM)
    (connectionSystemMatrix bN DN) s (productCoefficientMatrix_horizontal bM bN δ DM DN P hDN hP)
    (repr_horizontal_unit bN δ DN hDN hOne)

end ModuleComparison

section ProductSubmodule

variable {A : Type*} [CommRing A] [Algebra (LaurentPolynomial K) A]

/-- A single section supplies the comparison for a stable module and its product span. -/
def comparison_of_stable_productModule_kummer_section
    (D : A →+ A) (M : Submodule (LaurentPolynomial K) A) (hM : ∀ x ∈ M, D x ∈ M)
    (hLeib : ∀ x y : A, D (x * y) = D x * y + x * D y)
    (hD : ∀ (a : LaurentPolynomial K) (x : A), D (a • x) = laurentDerivation a • x + a • D x)
    (h1 : (1 : A) ∈ M) (hD1 : D 1 = 0)
    (bM : Basis (Fin m) (LaurentPolynomial K) M)
    (bN : Basis (Fin n) (LaurentPolynomial K) (M * M : Submodule (LaurentPolynomial K) A))
    (s : ordinaryPVAlgebra (combinedLaurentSystem (connectionSystemMatrix bM (restrictConnection D M hM))
        (connectionSystemMatrix bN (restrictConnection D (M * M) (productModule_stable D hM hLeib))))
        →ₐ[LaurentPolynomial K] KummerExtension K q) :
    LaurentCoordinateComparison K q
      (fun i j l => productCoefficientMatrix bM bN (productBilinear M) l (i, j))
      (bN.repr (productOne M h1)) :=
  comparison_of_module_kummer_section bM bN (restrictConnection D M hM)
    (restrictConnection D (M * M) (productModule_stable D hM hLeib)) (productBilinear M)
    (productOne M h1) (restrictConnection_smul D (M * M) (productModule_stable D hM hLeib)
      laurentDerivationAdd hD)
    (productBilinear_restrictConnection D M hM hLeib)
    (productOne_restrictConnection D M hM hLeib h1 hD1) s

end ProductSubmodule
end WideE
