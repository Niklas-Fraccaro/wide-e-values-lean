import WideE.LieMatrixCentralizer

/-! The actual orbit differential is the Lie bracket of invariant
derivations, computed via dual-number conjugation. -/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

variable {k H ι η : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [Fintype ι] [DecidableEq ι] [Fintype η]

set_option maxHeartbeats 800000 in
/-- The infinitesimal adjoint action agrees with the bracket on invariant
derivations. The varying group direction is the first argument of the bracket. -/
theorem hopfAdjointTangentMatrix_mulVec_eq_lieBracket
    (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (b : Basis η k (HopfCotangent k H)) (x y : HopfLieVector k H k) :
    hopfAdjointTangentMatrix b (fun i => x (b i)) *ᵥ (fun i => y (b i)) =
      fun i => (hopfLieVectorInvariantDerivations (k := k) (H := H)).symm
        ⁅hopfLieVectorInvariantDerivations y, hopfLieVectorInvariantDerivations x⁆ (b i) := by
  let θ := hopfLieVectorInvariantDerivations (k := k) (H := H)
  let q := hopfLieInfinitesimalPoint y
  let M := hopfPointMatrix U hΔ hε q
  let s := hopfAdjoint q (hopfLieVector_toDual x)
  let z := (TrivSqZeroExt.sndHom k k).comp s
  let X := hopfCotangentMatrix U.val x
  let Y := hopfCotangentMatrix U.val y
  let T := hopfCotangentMatrix U.val (hopfLieVector_toDual x)
  let fst : Matrix ι ι (DualNumber k) →+* Matrix ι ι k :=
    (TrivSqZeroExt.fstHom k k k).toRingHom.mapMatrix
  have hF : fst M.val = 1 := by
    apply Matrix.ext
    intro i j
    change (q (U.val i j)).fst = (1 : Matrix ι ι k) i j
    rw [hopfLieInfinitesimalPoint_fst, Algebra.id.map_eq_id, RingHom.id_apply]
    exact (hε i j).trans (Matrix.one_apply (i := i) (j := j)).symm
  have hFI : fst M.inv = 1 := by
    have h := congrArg fst M.val_inv
    rwa [map_mul, hF, Matrix.one_mul, map_one] at h
  have hS : M.val.map TrivSqZeroExt.snd = Y := rfl
  have hSZ : (1 : Matrix ι ι (DualNumber k)).map TrivSqZeroExt.snd = (0 : Matrix ι ι k) := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.map_apply, Matrix.one_apply_eq, TrivSqZeroExt.snd_one, Matrix.zero_apply]
    · simp only [Matrix.map_apply, Matrix.one_apply_ne hij, TrivSqZeroExt.snd_zero, Matrix.zero_apply]
  have hSI : M.inv.map TrivSqZeroExt.snd = -Y := by
    apply eq_neg_iff_add_eq_zero.mpr
    have h := matrix_snd_mul M.val M.inv
    change (M.val * M.inv).map TrivSqZeroExt.snd =
      fst M.val * M.inv.map TrivSqZeroExt.snd + M.val.map TrivSqZeroExt.snd * fst M.inv at h
    rw [M.val_inv, hSZ, hF, hFI, Matrix.one_mul, Matrix.mul_one, hS] at h
    exact h.symm
  have hTX : fst T = X := rfl
  have hTZ : T.map TrivSqZeroExt.snd = (0 : Matrix ι ι k) := rfl
  have hFT : fst (M.val * T) = X := by rw [map_mul, hF, hTX, Matrix.one_mul]
  have hST : (M.val * T).map TrivSqZeroExt.snd = Y * X := by
    have h := matrix_snd_mul M.val T
    change _ = fst M.val * T.map TrivSqZeroExt.snd + M.val.map TrivSqZeroExt.snd * fst T at h
    simpa only [hF, hTX, hTZ, hS, Matrix.mul_zero, zero_add] using h
  have hMat : hopfCotangentMatrix U.val z = Y * X - X * Y := by
    have h := congrArg (fun R : Matrix ι ι (DualNumber k) => R.map TrivSqZeroExt.snd)
      (hopfCotangentMatrix_adjoint U hΔ hε q (hopfLieVector_toDual x))
    change hopfCotangentMatrix U.val z = (M.val * T * M.inv).map TrivSqZeroExt.snd at h
    rw [h, matrix_snd_mul]
    change fst (M.val * T) * M.inv.map TrivSqZeroExt.snd +
      (M.val * T).map TrivSqZeroExt.snd * fst M.inv = Y * X - X * Y
    rw [hFT, hSI, hST, hFI, Matrix.mul_neg, Matrix.mul_one, sub_eq_add_neg, add_comm]
  have hBr : hopfCotangentMatrix U.val (θ.symm ⁅θ y, θ x⁆) = Y * X - X * Y := by
    rw [← hopfLieMatrix_invariantDerivations, LinearEquiv.apply_symm_apply]
    change hopfLieMatrixHom U.val hΔ ⁅θ y, θ x⁆ = _
    rw [LieHom.map_lie]
    change hopfLieMatrix U.val (θ y) * hopfLieMatrix U.val (θ x) -
      hopfLieMatrix U.val (θ x) * hopfLieMatrix U.val (θ y) = _
    rw [hopfLieMatrix_invariantDerivations, hopfLieMatrix_invariantDerivations]
  have hZ : z = θ.symm ⁅θ y, θ x⁆ :=
    hopfCotangentMatrix_injective U.val hGen (hMat.trans hBr.symm)
  funext i
  rw [← hZ, ← hopfAdjoint_infinitesimal_snd b x y i]
  rfl

end WideE
