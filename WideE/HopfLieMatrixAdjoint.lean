import WideE.AdjointCovariance
import WideE.HopfLieMatrix

/-! Adjoint action on tangent matrices in an affine group representation. -/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

section DualMatrices

variable {A ι : Type*} [CommRing A] [Fintype ι]

/-- The first-order coefficient of a matrix product over the dual numbers. -/
theorem matrix_snd_mul (X Y : Matrix ι ι (DualNumber A)) :
    (X * Y).map TrivSqZeroExt.snd = X.map TrivSqZeroExt.fst * Y.map TrivSqZeroExt.snd +
      X.map TrivSqZeroExt.snd * Y.map TrivSqZeroExt.fst := by
  ext i j
  change (TrivSqZeroExt.sndHom A A) (∑ l, X i l * Y l j) =
    (∑ l, (X i l).fst * (Y l j).snd) + (∑ l, (X i l).snd * (Y l j).fst)
  rw [map_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => DualNumber.snd_mul _ _

private theorem matrix_snd_inl_mul (X : Matrix ι ι A) (Y : Matrix ι ι (DualNumber A)) :
    (X.map TrivSqZeroExt.inl * Y).map TrivSqZeroExt.snd = X * Y.map TrivSqZeroExt.snd := by
  rw [matrix_snd_mul]
  have hF : (X.map (TrivSqZeroExt.inl : A → DualNumber A)).map TrivSqZeroExt.fst = X := rfl
  have hS : (X.map (TrivSqZeroExt.inl : A → DualNumber A)).map TrivSqZeroExt.snd = 0 := rfl
  rw [hF, hS, Matrix.zero_mul, add_zero]

private theorem matrix_snd_mul_inl (X : Matrix ι ι (DualNumber A)) (Y : Matrix ι ι A) :
    (X * Y.map TrivSqZeroExt.inl).map TrivSqZeroExt.snd = X.map TrivSqZeroExt.snd * Y := by
  rw [matrix_snd_mul]
  have hF : (Y.map (TrivSqZeroExt.inl : A → DualNumber A)).map TrivSqZeroExt.fst = Y := rfl
  have hS : (Y.map (TrivSqZeroExt.inl : A → DualNumber A)).map TrivSqZeroExt.snd = 0 := rfl
  rw [hF, hS, Matrix.mul_zero, zero_add]

end DualMatrices

variable {k H A ι : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing A] [Algebra k A] [Fintype ι] [DecidableEq ι]

/-- Matrix of the differential on coefficient functions for an algebra-valued tangent vector. -/
def hopfCotangentMatrix (U : Matrix ι ι H) (x : HopfLieVector k H A) : Matrix ι ι A :=
  fun i j => x (hopfCotangentProjection k H (U i j))

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem hopfLieMatrix_invariantDerivations (U : Matrix ι ι H) (x : HopfLieVector k H k) :
    hopfLieMatrix U (hopfLieVectorInvariantDerivations x) = hopfCotangentMatrix U x :=
  Matrix.ext fun _ _ => hopfLieVectorInvariantDerivations_counit _ _

/-- On tangent matrices, the adjoint action is conjugation by the group matrix. -/
theorem hopfCotangentMatrix_adjoint (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (g : H →ₐ[k] A) (x : HopfLieVector k H A) :
    let M := hopfPointMatrix U hD he g
    hopfCotangentMatrix U.val (hopfAdjoint g x) = M.val * hopfCotangentMatrix U.val x * M.inv := by
  let e := TrivSqZeroExt.inlAlgHom k A A
  letI : Group (H →ₐ[k] DualNumber A) := hopfPointGroup
  let ρ := hopfPointMatrix (A := DualNumber A) U hD he
  let M := hopfPointMatrix U hD he g
  have hC : hopfLieInfinitesimalPoint (hopfAdjoint g x) =
      (e.comp g) * hopfLieInfinitesimalPoint x * (e.comp g)⁻¹ := by
    rw [← hopfInfinitesimal_conjugation g x, hopfConjugation_eval]
  have hE : ρ (e.comp g) = M.map e.toRingHom.mapMatrix.toMonoidHom :=
    Units.ext (Matrix.ext fun _ _ => rfl)
  have hM := congrArg ρ hC
  rw [map_mul, map_mul, map_inv, hE, ← map_inv] at hM
  have hS := congrArg (fun X : (Matrix ι ι (DualNumber A))ˣ => X.val.map TrivSqZeroExt.snd) hM
  change ((U.val.map (hopfLieInfinitesimalPoint (hopfAdjoint g x))).map TrivSqZeroExt.snd) =
    ((M.val.map TrivSqZeroExt.inl) * (U.val.map (hopfLieInfinitesimalPoint x)) *
      (M.inv.map TrivSqZeroExt.inl)).map TrivSqZeroExt.snd at hS
  rw [matrix_snd_mul_inl, matrix_snd_inl_mul] at hS
  exact hS

end WideE
