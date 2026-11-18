import WideE.BlockDiagonalLieRepresentation
import WideE.HopfMatrixBlocks

/-! One generating matrix for the actual quotient, including the dual block representations. -/

noncomputable section

open scoped BigOperators Matrix TensorProduct

namespace WideE

universe u

variable {k H : Type u} {β : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [LinearOrder β] [DecidableEq β] {n : ℕ} (b : Fin n → β) (M : Matrix (Fin n) (Fin n) H)
  (hD : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
  (hUpper : M.BlockTriangular b)

local notation "Q" => blockDiagonalAlgebra (k := k) b M

/-- Each diagonal block contributes a block and its contragredient. -/
abbrev blockDiagonalGeneratingIndex : Type _ :=
  Σ t : β × Bool, diagonalBlockIndices b t.1

def blockDiagonalGeneratingSummand (t : β × Bool) :
    Matrix (diagonalBlockIndices b t.1) (diagonalBlockIndices b t.1) Q := by
  letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
  let U := blockDiagonalQuotientMatrix (k := k) b M t.1
  exact if t.2 then dualHopfMatrix (k := k) U else U

/-- The direct sum of the blocks and their duals presents the actual quotient. -/
def blockDiagonalQuotientGeneratingMatrix :
    Matrix (blockDiagonalGeneratingIndex b) (blockDiagonalGeneratingIndex b) Q :=
  Matrix.blockDiagonal' (blockDiagonalGeneratingSummand b M hD hUpper)

theorem blockDiagonalQuotientGeneratingMatrix_generates :
    Algebra.adjoin k (Set.range fun ij : blockDiagonalGeneratingIndex b × blockDiagonalGeneratingIndex b =>
      blockDiagonalQuotientGeneratingMatrix b M hD hUpper ij.1 ij.2) = ⊤ := by
  letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
  let I := blockDiagonalGeneratingIndex b
  let A := Algebra.adjoin k (Set.range fun ij : I × I =>
    blockDiagonalQuotientGeneratingMatrix b M hD hUpper ij.1 ij.2)
  change A = ⊤
  apply top_unique
  rw [← blockDiagonalAlgebra_adjoin_self b M hD hUpper]
  apply Algebra.adjoin_le
  intro q hq
  rcases hq with ⟨⟨⟨i, j⟩, hij⟩, rfl⟩ | ⟨_, ⟨⟨⟨i, j⟩, hij⟩, rfl⟩, rfl⟩
  · let t : β × Bool := (b i, false)
    let x : diagonalBlockIndices b t.1 := ⟨i, rfl⟩
    let y : diagonalBlockIndices b t.1 := ⟨j, hij.symm⟩
    apply Algebra.subset_adjoin
    refine ⟨(⟨t, x⟩, ⟨t, y⟩), ?_⟩
    change blockDiagonalQuotientGeneratingMatrix b M hD hUpper ⟨t, x⟩ ⟨t, y⟩ = _
    rw [blockDiagonalQuotientGeneratingMatrix, Matrix.blockDiagonal'_apply_eq]
    rfl
  · let t : β × Bool := (b i, true)
    let x : diagonalBlockIndices b t.1 := ⟨i, rfl⟩
    let y : diagonalBlockIndices b t.1 := ⟨j, hij.symm⟩
    apply Algebra.subset_adjoin
    refine ⟨(⟨t, y⟩, ⟨t, x⟩), ?_⟩
    change blockDiagonalQuotientGeneratingMatrix b M hD hUpper ⟨t, y⟩ ⟨t, x⟩ = _
    rw [blockDiagonalQuotientGeneratingMatrix, Matrix.blockDiagonal'_apply_eq]
    rfl

variable (he : ∀ i j, Coalgebra.counit (R := k) (M i j) = if i = j then 1 else 0)

omit [DecidableEq β] in
include he in
theorem blockDiagonalQuotientMatrix_counit (t : β) (i j : diagonalBlockIndices b t) :
    letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
    Coalgebra.counit (R := k) (blockDiagonalQuotientMatrix (k := k) b M t i j) =
      if i = j then 1 else 0 := by
  letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
  change Coalgebra.counit (R := k) (M i.val j.val) = _
  rw [he]
  simp only [Subtype.val_inj]

variable [Fintype β]

include he in
theorem blockDiagonalQuotientGeneratingMatrix_relations :
    letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
    let U := blockDiagonalQuotientGeneratingMatrix b M hD hUpper
    (∀ i j : blockDiagonalGeneratingIndex b, Coalgebra.comul (R := k) (U i j) =
      ∑ l : blockDiagonalGeneratingIndex b, U i l ⊗ₜ[k] U l j) ∧
    (∀ i j : blockDiagonalGeneratingIndex b, Coalgebra.counit (R := k) (U i j) =
      if i = j then 1 else 0) := by
  letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
  let U := blockDiagonalGeneratingSummand b M hD hUpper
  apply blockDiagonal_hopfMatrix_relations U
  · rintro ⟨t, d⟩
    cases d
    · exact blockDiagonalQuotientMatrix_comul b M hD hUpper t
    · exact dualHopfMatrix_comul _
        (blockDiagonalQuotientMatrix_comul b M hD hUpper t)
  · rintro ⟨t, d⟩
    cases d
    · exact blockDiagonalQuotientMatrix_counit b M hD hUpper he t
    · exact dualHopfMatrix_counit _
        (blockDiagonalQuotientMatrix_counit b M hD hUpper he t)

include he in
/-- The chosen generating matrix of the quotient is a unit. -/
def blockDiagonalQuotientGeneratingUnit :
    (Matrix (blockDiagonalGeneratingIndex b) (blockDiagonalGeneratingIndex b) Q)ˣ := by
  letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
  let h := blockDiagonalQuotientGeneratingMatrix_relations b M hD hUpper he
  exact hopfMatrixUnitOfRelations (blockDiagonalQuotientGeneratingMatrix b M hD hUpper) h.1 h.2

@[simp] theorem blockDiagonalQuotientGeneratingUnit_val :
    (blockDiagonalQuotientGeneratingUnit b M hD hUpper he).val =
      blockDiagonalQuotientGeneratingMatrix b M hD hUpper := rfl

end WideE
