import WideE.LieInvariantFlag
import WideE.UpperTriangularCocycle

/-! Diagonal tangent matrices give a triangular group for Galois descent. -/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

local notation "k" => AlgebraicComplex

variable {F H : Type} {ι : Type*} [Field F] [Algebra k F]
  [CommRing H] [IsDomain H] [HopfAlgebra k H] [Fintype ι] [DecidableEq ι]

/-- For a connected affine group over the algebraic numbers, if every tangent
matrix of a generating representation is diagonal, its cocycles are coboundaries. -/
theorem isHopfPointCoboundary_of_diagonal_tangents (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (hDiag : ∀ D : hopfInvariantDerivations k H, ∃ d : ι → k,
      hopfLieMatrix U.val D = Matrix.diagonal d)
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (c : (E ≃ₐ[F] E) → H →ₐ[k] E) (hc : IsHopfPointCocycle c) :
    IsHopfPointCoboundary c := by
  classical
  letI : Algebra.FiniteType k H := ⟨Subalgebra.fg_def.mpr ⟨_, Set.finite_range _, hGen⟩⟩
  have hOffdiag (i j : ι) (hij : i ≠ j) : U.val i j = 0 := by
    apply matrixCoefficient_eq_zero_of_lieInvariantSubspace U.val hD he {j} ?_ i j
      (by simpa using hij) (by simp)
    intro D a b ha hb
    have hab : a ≠ b := fun h => ha (h ▸ hb)
    obtain ⟨d, hd⟩ := hDiag D
    rw [hd, Matrix.diagonal_apply_ne _ hab]
  let e := Fintype.equivFin ι
  let M : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) H :=
    U.val.submatrix e.symm e.symm
  have hDM (i j : Fin (Fintype.card ι)) :
      Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j := by
    change Coalgebra.comul (R := k) (U.val (e.symm i) (e.symm j)) =
      ∑ l, U.val (e.symm i) (e.symm l) ⊗ₜ[k] U.val (e.symm l) (e.symm j)
    rw [hD]
    exact Fintype.sum_equiv e _ _ (fun x => by simp)
  have heM (i j : Fin (Fintype.card ι)) :
      Coalgebra.counit (R := k) (M i j) = if i = j then 1 else 0 := by
    change Coalgebra.counit (R := k) (U.val (e.symm i) (e.symm j)) = _
    simp only [he, e.symm.injective.eq_iff]
  have hUpper : M.BlockTriangular id := by
    intro i j hij
    exact hOffdiag _ _ (fun h => (ne_of_gt hij) (e.symm.injective h))
  have hRange : Set.range (fun ij : Fin (Fintype.card ι) × Fin (Fintype.card ι) => M ij.1 ij.2) =
      Set.range (fun ij : ι × ι => U.val ij.1 ij.2) := by
    ext x
    constructor
    · rintro ⟨⟨i, j⟩, rfl⟩
      exact ⟨(e.symm i, e.symm j), rfl⟩
    · rintro ⟨⟨i, j⟩, rfl⟩
      exact ⟨(e i, e j), by simp [M]⟩
  have hGenM : Algebra.adjoin k (Set.range fun ij : Fin (Fintype.card ι) × Fin (Fintype.card ι) =>
      M ij.1 ij.2) = ⊤ := by rwa [hRange]
  exact upperTriangular_isHopfPointCoboundary M hDM heM hUpper hGenM E c hc

end WideE
