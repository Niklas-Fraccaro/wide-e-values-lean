import WideE.LieCompositionFlag
import WideE.LieInvariantFlag
import Mathlib.LinearAlgebra.Matrix.Basis

/-! Express a generating Hopf matrix in the basis of its Lie composition flag. -/

noncomputable section

open scoped BigOperators Matrix TensorProduct

namespace WideE

section Matrices

variable {k : Type*} [Field k] {n : ℕ}

/-- The unit whose columns are the vectors of the new basis. -/
def flagBasisMatrix (v : Basis (Fin n) k (Fin n → k)) : (Matrix (Fin n) (Fin n) k)ˣ :=
  let std := Pi.basisFun k (Fin n)
  ⟨std.toMatrix v, v.toMatrix std, std.toMatrix_mul_toMatrix_flip v, v.toMatrix_mul_toMatrix_flip std⟩

/-- Conjugation by the matrix of the new basis agrees with the linear map in that basis. -/
theorem flagBasisMatrix_conjugate_toMatrix (v : Basis (Fin n) k (Fin n → k))
    (A : Matrix (Fin n) (Fin n) k) :
    (flagBasisMatrix v).inv * A * (flagBasisMatrix v).val =
      LinearMap.toMatrix v v (Matrix.toLin' A) := by
  let std := Pi.basisFun k (Fin n)
  change v.toMatrix std * A * std.toMatrix v = _
  have h := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix v std v std (Matrix.toLin std std A)
  rw [LinearMap.toMatrix_toLin] at h
  simpa only [std, Matrix.toLin_eq_toLin'] using h

end Matrices

section HopfFlags

variable {k H : Type*} [Field k] [CommRing H] [HopfAlgebra k H] {n : ℕ}

/-- The Lie module structure induced by differentiating the actual matrix corepresentation. -/
def hopfMatrixLieAction {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι H)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U i j) = ∑ l, U i l ⊗ₜ[k] U l j) :
    hopfInvariantDerivations k H →ₗ⁅k⁆ Module.End k (ι → k) :=
  (Matrix.toLinAlgEquiv' (R := k) (n := ι)).toAlgHom.toLieHom.comp (hopfLieMatrixHom U hD)

/-- The differential of the conjugated matrix is the same Lie action in the new basis. -/
theorem hopfMatrixLieAction_toMatrix (U : (Matrix (Fin n) (Fin n) H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (v : Basis (Fin n) k (Fin n → k)) (D : hopfInvariantDerivations k H) :
    letI := LieRingModule.compLieHom (Fin n → k) (hopfMatrixLieAction U.val hD)
    letI := LieModule.compLieHom (Fin n → k) (hopfMatrixLieAction U.val hD)
    LinearMap.toMatrix v v (LieModule.toEnd k (hopfInvariantDerivations k H) (Fin n → k) D) =
      hopfLieMatrix (conjugateMatrixUnit (flagBasisMatrix v) U).val D := by
  letI := LieRingModule.compLieHom (Fin n → k) (hopfMatrixLieAction U.val hD)
  letI := LieModule.compLieHom (Fin n → k) (hopfMatrixLieAction U.val hD)
  rw [hopfLieMatrix_conjugateMatrixUnit, flagBasisMatrix_conjugate_toMatrix]
  rfl

variable [CharZero k] [IsDomain H]

/-- An adapted Lie composition flag gives a generating, block upper triangular Hopf matrix. -/
theorem exists_hopfMatrix_adapted_to_lieCompositionFlag
    (U : (Matrix (Fin n) (Fin n) H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : Fin n × Fin n => U.val ij.1 ij.2) = ⊤) :
    letI := LieRingModule.compLieHom (Fin n → k) (hopfMatrixLieAction U.val hD)
    ∃ (s : RelSeries (fun P Q : LieSubmodule k (hopfInvariantDerivations k H) (Fin n → k) => P ⋖ Q))
      (v : Basis (Fin n) k (Fin n → k)) (b : Fin n → Fin s.length),
      s.head = ⊥ ∧ s.last = ⊤ ∧ Monotone b ∧
      (∀ t : Fin (s.length + 1), Submodule.span k (v '' {i | (b i).val < t.val}) = (s t).toSubmodule) ∧
      let V := conjugateMatrixUnit (flagBasisMatrix v) U
      V.val.BlockTriangular b ∧
      (∀ i j, Coalgebra.comul (R := k) (V.val i j) = ∑ l, V.val i l ⊗ₜ[k] V.val l j) ∧
      (∀ i j, Coalgebra.counit (R := k) (V.val i j) = if i = j then 1 else 0) ∧
      Algebra.adjoin k (Set.range fun ij : Fin n × Fin n => V.val ij.1 ij.2) = ⊤ := by
  let 𝔤 := hopfInvariantDerivations k H
  letI := LieRingModule.compLieHom (Fin n → k) (hopfMatrixLieAction U.val hD)
  letI : Algebra.FiniteType k H := ⟨Subalgebra.fg_def.mpr ⟨_, Set.finite_range _, hGen⟩⟩
  have h := exists_lieCompositionBasis (k := k) (L := 𝔤) (V := Fin n → k)
  rw [Module.finrank_fin_fun] at h
  obtain ⟨s, v, b, hBot, hTop, hb, hv⟩ := h
  let P := flagBasisMatrix v
  let V := conjugateMatrixUnit P U
  obtain ⟨hΔ', hε'⟩ := conjugateMatrixUnit_hopf P U hD he
  have hLie (D : 𝔤) : (hopfLieMatrix V.val D).BlockTriangular b := by
    change (hopfLieMatrix (conjugateMatrixUnit P U).val D).BlockTriangular b
    rw [hopfLieMatrix_conjugateMatrixUnit, flagBasisMatrix_conjugate_toMatrix]
    apply toMatrix_blockTriangular_of_preserves_flag v b (fun t => (s t).toSubmodule) hv
    intro t x hx
    exact (s t).lie_mem (x := D) hx
  have hUpper : V.val.BlockTriangular b := by
    intro i j hij
    let t := (b j).succ
    let A : Set (Fin n) := { l | (b l).val < t.val }
    have hLieZero (D : 𝔤) (a c : Fin n) (ha : a ∉ A) (hc : c ∈ A) :
        hopfLieMatrix V.val D a c = 0 := by
      have hlt : (b c).val < (b a).val := lt_of_lt_of_le hc (Nat.le_of_not_lt ha)
      exact hLie D hlt
    exact matrixCoefficient_eq_zero_of_lieInvariantSubspace V.val hΔ' hε' A hLieZero i j
      (Nat.not_lt_of_ge (Nat.succ_le_iff.mpr hij)) (Nat.lt_succ_self _)
  exact ⟨s, v, b, hBot, hTop, hb, hv, hUpper, hΔ', hε', conjugateMatrixUnit_generating P U hGen⟩

end HopfFlags

end WideE
