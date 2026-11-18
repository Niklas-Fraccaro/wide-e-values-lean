import WideE.BlockDiagonalHopfQuotient
import WideE.FlagQuotientBasis
import WideE.HopfLieMap
import WideE.LieFlagHopfMatrix

/-! The Lie representations of the actual diagonal blocks are the composition factors. -/

noncomputable section

open scoped BigOperators Matrix TensorProduct
open TensorProduct

namespace WideE

section Blocks

universe u

variable {k H : Type u} {β : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  {n : ℕ} (b : Fin n → β) (M : Matrix (Fin n) (Fin n) H)

local notation "Q" => blockDiagonalAlgebra (k := k) b M

/-- The row and column indices belonging to a single block. -/
abbrev diagonalBlockIndices (t : β) := {i : Fin n // b i = t}

/-- The representation matrix of one block, with coefficients in the actual quotient ring. -/
def blockDiagonalQuotientMatrix (t : β) : Matrix (diagonalBlockIndices b t) (diagonalBlockIndices b t) Q :=
  fun i j => ⟨M i.val j.val, diagonalBlockEntry_mem b M (i.property.trans j.property.symm)⟩

variable [LinearOrder β] [DecidableEq β]
  (hD : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
  (hUpper : M.BlockTriangular b)

/-- The comultiplication of one block is the matrix product on its own index set. -/
theorem blockDiagonalQuotientMatrix_comul (t : β) :
    letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
    let U := blockDiagonalQuotientMatrix (k := k) b M t
    ∀ i j : diagonalBlockIndices b t, Coalgebra.comul (R := k) (U i j) =
      ∑ l : diagonalBlockIndices b t, U i l ⊗ₜ[k] U l j := by
  letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
  let p := blockDiagonalQuotientMap b M hD hUpper
  let f : Q →ₐ[k] H := p
  intro U i j
  apply tensorAlgHom_injective f f Subtype.val_injective Subtype.val_injective
  have hMap := DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom p) (U i j)
  change Algebra.TensorProduct.map f f (Bialgebra.comulAlgHom k Q (U i j)) =
    Coalgebra.comul (R := k) (M i.val j.val) at hMap
  change Algebra.TensorProduct.map f f (Bialgebra.comulAlgHom k Q (U i j)) =
    Algebra.TensorProduct.map f f (∑ l, U i l ⊗ₜ[k] U l j)
  rw [hMap, hD, map_sum]
  simp only [Algebra.TensorProduct.map_tmul]
  change (∑ l, M i.val l ⊗ₜ[k] M l j.val) =
    ∑ l : diagonalBlockIndices b t, M i.val l.val ⊗ₜ[k] M l.val j.val
  symm
  refine Fintype.sum_of_injective (fun l : diagonalBlockIndices b t => l.val)
    Subtype.val_injective _ _ ?_ (fun _ => rfl)
  intro l hl
  have hne : b l ≠ t := fun h => hl ⟨⟨l, h⟩, rfl⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [hUpper (i := i.val) (j := l) (i.property.symm ▸ hlt), zero_tmul]
  · rw [hUpper (i := l) (j := j.val) (j.property.symm ▸ hgt), tmul_zero]

/-- The differentiated quotient action on one actual diagonal block. -/
def blockDiagonalQuotientLieAction (t : β) :
    letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
    hopfInvariantDerivations k Q →ₗ⁅k⁆ Module.End k (diagonalBlockIndices b t → k) := by
  letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
  exact hopfMatrixLieAction (blockDiagonalQuotientMatrix (k := k) b M t)
    (blockDiagonalQuotientMatrix_comul b M hD hUpper t)

theorem blockDiagonalQuotientLieAction_apply (t : β)
    (x : diagonalBlockIndices b t → k) :
    letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
    ∀ D : hopfInvariantDerivations k Q, blockDiagonalQuotientLieAction b M hD hUpper t D x =
      hopfLieMatrix (blockDiagonalQuotientMatrix (k := k) b M t) D *ᵥ x := by
  letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
  intro D
  exact Matrix.toLinAlgEquiv'_apply _ _

omit [DecidableEq β] in
/-- The derivative of the group quotient gives the original diagonal block of the derivative. -/
theorem blockDiagonalQuotientMatrix_lie (t : β) (D : hopfInvariantDerivations k H) :
    letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
    let j := blockDiagonalQuotientMap b M hD hUpper
    hopfLieMatrix (blockDiagonalQuotientMatrix (k := k) b M t) (hopfInvariantDerivationsMap j D) =
      (hopfLieMatrix M D).submatrix (fun i : diagonalBlockIndices b t => i.val)
        (fun i : diagonalBlockIndices b t => i.val) := by
  letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
  let j := blockDiagonalQuotientMap b M hD hUpper
  apply Matrix.ext
  intro i l
  exact hopfInvariantDerivationsMap_counit j D (blockDiagonalQuotientMatrix (k := k) b M t i l)

end Blocks

section Irreducible

universe u

variable {k H : Type u} {V : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup V] [Module k V]

local notation "𝔤" => hopfInvariantDerivations k H

variable [LieRingModule (hopfInvariantDerivations k H) V]
  [LieModule k (hopfInvariantDerivations k H) V] {n : ℕ}

set_option maxHeartbeats 1000000 in
/-- Each diagonal block of the quotient acts irreducibly when the original
matrix is written in the basis of its Lie composition flag. -/
theorem blockDiagonalQuotientLieAction_irreducible
    (s : RelSeries (fun P Q : LieSubmodule k 𝔤 V => P ⋖ Q))
    (v : Basis (Fin n) k V) (b : Fin n → Fin s.length)
    (hSpan : ∀ t : Fin (s.length + 1),
      Submodule.span k (v '' {i | (b i).val < t.val}) = (s t).toSubmodule)
    (M : Matrix (Fin n) (Fin n) H)
    (hD : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (hUpper : M.BlockTriangular b)
    (hLie : ∀ D : 𝔤, LinearMap.toMatrix v v (LieModule.toEnd k 𝔤 V D) = hopfLieMatrix M D)
    (t : Fin s.length) :
    let Q := blockDiagonalAlgebra (k := k) b M
    letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
    let A := {i : Fin n // b i = t} → k
    letI := LieRingModule.compLieHom A (blockDiagonalQuotientLieAction b M hD hUpper t)
    LieModule.IsIrreducible k (hopfInvariantDerivations k Q) A := by
  let Q := blockDiagonalAlgebra (k := k) b M
  letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
  let A := {i : Fin n // b i = t} → k
  letI := LieRingModule.compLieHom A (blockDiagonalQuotientLieAction b M hD hUpper t)
  let j := blockDiagonalQuotientMap b M hD hUpper
  let P := (s t.castSucc).comap (s t.succ).incl
  let W (i : Fin (s.length + 1)) := (s i).toSubmodule
  let e : ((s t.succ) ⧸ P) ≃ₗ[k] A := flagSubquotientCoordinates v b W hSpan t
  letI : LieModule.IsIrreducible k 𝔤 ((s t.succ) ⧸ P) :=
    lieSubmodule_quotient_isIrreducible_of_covBy _ _ (s.step t)
  refine lieModule_isIrreducible_of_equivariant_equiv (hopfInvariantDerivationsMap j) e ?_
  intro D x
  obtain ⟨y, rfl⟩ := LieSubmodule.Quotient.surjective_mk' P x
  let f := LieModule.toEnd k 𝔤 V D
  have hf (i : Fin (s.length + 1)) : W i ≤ (W i).comap f :=
    fun _ hx => (s i).lie_mem (x := D) hx
  have h := flagSubquotientCoordinates_apply_map v b W hSpan t f hf y
  rw [show LinearMap.toMatrix v v f = hopfLieMatrix M D from hLie D,
    ← blockDiagonalQuotientMatrix_lie b M hD hUpper t D] at h
  have hAct (a : A) : ⁅hopfInvariantDerivationsMap j D, a⁆ =
      hopfLieMatrix (blockDiagonalQuotientMatrix (k := k) b M t)
        (hopfInvariantDerivationsMap j D) *ᵥ a := by
    rw [LieRingModule.compLieHom_apply A (blockDiagonalQuotientLieAction b M hD hUpper t)]
    change blockDiagonalQuotientLieAction b M hD hUpper t (hopfInvariantDerivationsMap j D) a = _
    exact blockDiagonalQuotientLieAction_apply b M hD hUpper t a _
  rw [← (LieSubmodule.Quotient.mk' P).map_lie]
  rw [hAct]
  exact h

end Irreducible

end WideE
