import WideE.DiagonalDerivationTorus
import WideE.LieInvariantFlag
import WideE.SemisimpleEigenbasis
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.LinearAlgebra.Matrix.Basis

/-! The semisimple part of a tangent matrix is the tangent of a diagonal torus. -/

noncomputable section

open scoped Matrix TensorProduct
open StrictEUnit

namespace WideE

section MatrixWeights

variable {k A ι : Type*} [Field k] [CommRing A] [Algebra k A]
  [Fintype ι] [DecidableEq ι]

private theorem shifted_matrixDerivative_apply (U : Matrix ι ι A) (D : Derivation k A A)
    (d : ι → k) (W : Matrix ι ι k) (h : Commute (Matrix.diagonal d) W)
    (hD : matrixDerivative D U = U * (algebraMap k A).mapMatrix (Matrix.diagonal d + W))
    (m : ℕ) (i j : ι) :
    (D.toLinearMap - d j • (1 : Module.End k A))
      ((U * (algebraMap k A).mapMatrix (W ^ m)) i j) =
      (U * (algebraMap k A).mapMatrix (W ^ (m + 1))) i j := by
  let φ := (algebraMap k A).mapMatrix (m := ι)
  let V := U * φ (W ^ m)
  have hComm : Commute (Matrix.diagonal d + W) (W ^ m) :=
    (h.add_left (Commute.refl W)).pow_right m
  have hV : matrixDerivative D V = V * φ (Matrix.diagonal d) +
      U * φ (W ^ (m + 1)) := by
    change matrixDerivative D (U * φ (W ^ m)) = _
    rw [matrixDerivative_mul, matrixDerivative_constant, mul_zero, add_zero, hD]
    change U * φ (Matrix.diagonal d + W) * φ (W ^ m) = _
    rw [mul_assoc, ← map_mul, hComm.eq, map_mul, ← mul_assoc, map_add, mul_add]
    rw [show V * φ W = U * φ (W ^ (m + 1)) by rw [pow_succ, map_mul, ← mul_assoc]]
  have hDiag : φ (Matrix.diagonal d) = Matrix.diagonal (algebraMap k A ∘ d) := by
    ext a b
    by_cases hab : a = b <;> simp [φ, Matrix.diagonal_apply, hab]
  change D (V i j) - d j • V i j = _
  have hEntry := congrArg (fun M : Matrix ι ι A => M i j) hV
  change matrixDerivative D V i j = (V * φ (Matrix.diagonal d) + U * φ (W ^ (m + 1))) i j at hEntry
  rw [matrixDerivative_apply, Matrix.add_apply, hDiag, Matrix.mul_diagonal] at hEntry
  rw [hEntry, Function.comp_apply, Algebra.smul_def, mul_comm (V i j), add_sub_cancel_left]

private theorem matrixCoefficient_mem_derivation_maxGenEigenspace (U : Matrix ι ι A)
    (D : Derivation k A A) (d : ι → k) (W : Matrix ι ι k)
    (h : Commute (Matrix.diagonal d) W) (hW : IsNilpotent W)
    (hD : matrixDerivative D U = U * (algebraMap k A).mapMatrix (Matrix.diagonal d + W))
    (i j : ι) : U i j ∈ Module.End.maxGenEigenspace D.toLinearMap (d j) := by
  let T : Module.End k A := D.toLinearMap - d j • 1
  have hPow (m : ℕ) : (T ^ m) (U i j) = (U * (algebraMap k A).mapMatrix (W ^ m)) i j := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      exact shifted_matrixDerivative_apply U D d W h hD m i j
  obtain ⟨m, hm⟩ := hW
  refine (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨m, ?_⟩
  change (T ^ m) (U i j) = 0
  rw [hPow, hm, map_zero, mul_zero, Matrix.zero_apply]

end MatrixWeights

section Tangent

variable {k H ι : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [Fintype ι] [DecidableEq ι]

/-- For a generating group matrix, a commuting decomposition into a diagonal
matrix and a nilpotent matrix puts the diagonal part in the actual Lie algebra. -/
theorem exists_hopfLieMatrix_diagonalPart (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (D : hopfInvariantDerivations k H) (d : ι → k) (W : Matrix ι ι k)
    (h : Commute (Matrix.diagonal d) W) (hW : IsNilpotent W)
    (hD : hopfLieMatrix U.val D = Matrix.diagonal d + W) :
    ∃ Ds : hopfInvariantDerivations k H, hopfLieMatrix U.val Ds = Matrix.diagonal d := by
  have hU : matrixDerivative D.val U.val = U.val * (algebraMap k H).mapMatrix
      (Matrix.diagonal d + W) := by
    ext i j
    rw [matrixDerivative_apply, hopfInvariantDerivation_matrixCoefficient U.val hΔ D, hD]
    rfl
  obtain ⟨f, _, hf⟩ := exists_diagonalTorus_of_genEigenspace U hΔ hε hGen D.val d
    (matrixCoefficient_mem_derivation_maxGenEigenspace U.val D.val d W h hW hU)
  let q : H →ₐ[k] DualNumber k := (diagonalCharacterInfinitesimalPoint d).comp
    (f : H →ₐ[k] diagonalCharacterAlgebra d)
  have hq (a : H) : (q a).fst = algebraMap k k (Bialgebra.counitAlgHom k H a) := by
    change (diagonalCharacterInfinitesimalPoint d (f a)).fst = _
    rw [diagonalCharacterInfinitesimalPoint_fst]
    exact DFunLike.congr_fun (BialgHomClass.counitAlgHom_comp f) a
  let x := (hopfInfinitesimalPointEquiv k H k).symm ⟨q, hq⟩
  have hx (a : H) : x (hopfCotangentProjection k H a) = (q a).snd := by
    have heq : hopfLieInfinitesimalPoint x = q :=
      congrArg Subtype.val ((hopfInfinitesimalPointEquiv k H k).apply_symm_apply ⟨q, hq⟩)
    rw [← heq, hopfLieInfinitesimalPoint_snd]
  refine ⟨hopfLieVectorInvariantDerivations x, Matrix.ext fun i j => ?_⟩
  change (Bialgebra.counitAlgHom k H) ((hopfLieVectorInvariantDerivations x).val (U.val i j)) = _
  rw [hopfLieVectorInvariantDerivations_counit, hx]
  change (diagonalCharacterInfinitesimalPoint d (f (U.val i j))).snd = _
  rw [hf, Matrix.diagonal_apply]
  by_cases hij : i = j
  · simp only [if_pos hij, diagonalCharacterInfinitesimalPoint_monomial, TrivSqZeroExt.snd_mk]
  · simp only [if_neg hij, map_zero, TrivSqZeroExt.snd_zero]

end Tangent

section Jordan

variable {k H ι : Type*} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Fintype ι] [DecidableEq ι]

/-- Jordan decomposition in a faithful representation stays inside the actual Lie algebra. -/
theorem exists_hopfLieMatrix_jordanDecomposition (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (D : hopfInvariantDerivations k H) :
    ∃ (S N : hopfInvariantDerivations k H), D = S + N ∧
      Module.End.IsSemisimple (Matrix.toLinAlgEquiv' (hopfLieMatrix U.val S)) ∧
      IsNilpotent (hopfLieMatrix U.val N) ∧ ⁅S, N⁆ = 0 := by
  classical
  let E : Matrix ι ι k ≃ₐ[k] Module.End k (ι → k) := Matrix.toLinAlgEquiv'
  let M := hopfLieMatrix U.val D
  obtain ⟨n, hnA, s, hsA, hNil, hSemi, hSum⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := E M)
  have hComm : Commute s n := Algebra.commute_of_mem_adjoin_singleton_of_commute hnA
    (Algebra.commute_of_mem_adjoin_self hsA).symm
  obtain ⟨b₀, d₀, hb₀⟩ := exists_eigenbasis_of_isSemisimple s hSemi
  let std := Pi.basisFun k ι
  let re := b₀.indexEquiv std
  let b := b₀.reindex re
  let d (i : ι) := d₀ (re.symm i)
  have hb (i : ι) : s (b i) = d i • b i := by
    simpa only [b, d, Basis.reindex_apply] using hb₀ (re.symm i)
  let P : (Matrix ι ι k)ˣ :=
    ⟨std.toMatrix b, b.toMatrix std, std.toMatrix_mul_toMatrix_flip b, b.toMatrix_mul_toMatrix_flip std⟩
  let φ := LinearMap.toMatrixAlgEquiv b
  let C := E.trans φ
  have hC (X : Matrix ι ι k) : C X = P.inv * X * P.val := by
    change LinearMap.toMatrix b b (Matrix.toLin' X) = b.toMatrix std * X * std.toMatrix b
    have hx := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b std b std
      (Matrix.toLin std std X)
    rw [LinearMap.toMatrix_toLin] at hx
    simpa only [std, Matrix.toLin_eq_toLin'] using hx.symm
  have hDiag : φ s = Matrix.diagonal d := by
    ext i j
    change LinearMap.toMatrix b b s i j = Matrix.diagonal d i j
    rw [LinearMap.toMatrix_apply, hb, map_smul, Finsupp.smul_apply, Basis.repr_self,
      Finsupp.single_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij, Ne.symm hij]
  have hW : IsNilpotent (φ n) := hNil.map φ.toAlgHom
  have hC' : Commute (Matrix.diagonal d) (φ n) := hDiag ▸ hComm.map φ.toAlgHom
  let V := conjugateMatrixUnit P U
  obtain ⟨hvΔ, hvε⟩ := conjugateMatrixUnit_hopf P U hΔ hε
  have hvGen := conjugateMatrixUnit_generating P U hGen
  have hvD : hopfLieMatrix V.val D = Matrix.diagonal d + φ n := by
    rw [show hopfLieMatrix V.val D = C M from
      (hopfLieMatrix_conjugateMatrixUnit P U D).trans (hC M).symm]
    change φ (E M) = _
    rw [hSum, map_add, hDiag, add_comm]
  obtain ⟨S, hS⟩ := exists_hopfLieMatrix_diagonalPart V hvΔ hvε hvGen D d (φ n) hC' hW hvD
  have hS' : E (hopfLieMatrix U.val S) = s := by
    apply φ.injective
    change C (hopfLieMatrix U.val S) = φ s
    rw [hC, ← hopfLieMatrix_conjugateMatrixUnit P U S, hDiag]
    exact hS
  let N := D - S
  have hN' : E (hopfLieMatrix U.val N) = n := by
    change E ((hopfLieMatrixHom U.val hΔ).toLinearMap (D - S)) = n
    rw [map_sub, map_sub]
    change E M - E (hopfLieMatrix U.val S) = n
    rw [hS', hSum, add_sub_cancel_right]
  refine ⟨S, N, (add_sub_cancel S D).symm, ?_, ?_, ?_⟩
  · change (E (hopfLieMatrix U.val S)).IsSemisimple
    rw [hS']
    exact hSemi
  · rw [← IsNilpotent.map_iff (f := E.toRingHom) E.injective]
    change IsNilpotent (E (hopfLieMatrix U.val N))
    rw [hN']
    exact hNil
  · apply hopfLieMatrixHom_injective U.val hΔ hGen
    rw [LieHom.map_lie, LieHom.map_zero]
    apply E.injective
    change E (hopfLieMatrix U.val S * hopfLieMatrix U.val N -
      hopfLieMatrix U.val N * hopfLieMatrix U.val S) = E 0
    rw [map_sub, map_mul, map_mul, hS', hN', hComm.eq, sub_self, map_zero]

end Jordan

end WideE
