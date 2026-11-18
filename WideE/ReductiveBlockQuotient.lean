import WideE.BlockDiagonalLieRepresentation
import WideE.ReductiveLieAlgebra

/-! The actual diagonal-block quotient has a Lie algebra that splits into its center
and an ideal with nondegenerate Killing form. -/

noncomputable section

open scoped BigOperators Matrix TensorProduct
open LieAlgebra StrictEUnit

namespace WideE

section Faithfulness

variable {k A ι : Type*} [Field k] [CommRing A] [HopfAlgebra k A] [Fintype ι] [DecidableEq ι]

private theorem matrixAntipode_derivative_zero (U : Matrix ι ι A)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U i j) = ∑ l, U i l ⊗ₜ[k] U l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U i j) = if i = j then 1 else 0)
    (D : Derivation k A A) (hZero : ∀ i j, D (U i j) = 0) :
    ∀ i j, D (hopfAntipodeAlgHom k A (U i j)) = 0 := by
  let V := U.map (hopfAntipodeAlgHom k A)
  have hVU : V * U = 1 := by
    ext i j
    have h := HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) (U i j)
    rw [hD i j] at h
    simpa only [map_sum, LinearMap.rTensor_tmul, LinearMap.mul'_apply, Algebra.linearMap_apply,
      hε, apply_ite (algebraMap k A), map_one, map_zero, Matrix.mul_apply, Matrix.map_apply,
      Matrix.one_apply, V, hopfAntipodeAlgHom_apply] using h
  have hUV : U * V = 1 := by
    ext i j
    have h := HopfAlgebra.mul_antipode_lTensor_comul_apply (R := k) (U i j)
    rw [hD i j] at h
    simpa only [map_sum, LinearMap.lTensor_tmul, LinearMap.mul'_apply, Algebra.linearMap_apply,
      hε, apply_ite (algebraMap k A), map_one, map_zero, Matrix.mul_apply, Matrix.map_apply,
      Matrix.one_apply, V, hopfAntipodeAlgHom_apply] using h
  have hU : matrixDerivative D U = 0 := Matrix.ext hZero
  have h := matrixDerivative_mul D V U
  rw [hVU, matrixDerivative_one, hU, mul_zero, add_zero] at h
  have hV : matrixDerivative D V = 0 := by
    calc
      _ = matrixDerivative D V * (U * V) := by rw [hUV, mul_one]
      _ = _ := by rw [← mul_assoc, ← h, zero_mul]
  intro i j
  exact congrArg (fun M : Matrix ι ι A => M i j) hV

universe u

variable {k₀ H : Type u} {β : Type*} [Field k₀] [CommRing H] [HopfAlgebra k₀ H]
  [LinearOrder β] [DecidableEq β] {n : ℕ} (b : Fin n → β) (M : Matrix (Fin n) (Fin n) H)
  (hD : ∀ i j, Coalgebra.comul (R := k₀) (M i j) = ∑ l, M i l ⊗ₜ[k₀] M l j)
  (he : ∀ i j, Coalgebra.counit (R := k₀) (M i j) = if i = j then 1 else 0)
  (hUpper : M.BlockTriangular b)

include he in
/-- The derivative of the family of actual quotient representations is faithful. -/
theorem blockDiagonalQuotientLieActions_faithful :
    let Q := blockDiagonalAlgebra (k := k₀) b M
    letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
    ∀ D : hopfInvariantDerivations k₀ Q,
      (∀ t (x : diagonalBlockIndices b t → k₀),
        blockDiagonalQuotientLieAction b M hD hUpper t D x = 0) → D = 0 := by
  letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
  intro Q D hZero
  let U (t : β) := blockDiagonalQuotientMatrix (k := k₀) b M t
  have hLie (t : β) : hopfLieMatrix (k := k₀) (U t) D = 0 := by
    ext i j
    have h := congrFun (hZero t (Pi.single j 1)) i
    change (hopfLieMatrix (U t) D *ᵥ Pi.single j 1) i = 0 at h
    rwa [Matrix.mulVec_single_one] at h
  have hEntries (t : β) (i j : diagonalBlockIndices b t) : D.val (U t i j) = 0 := by
    rw [hopfInvariantDerivation_matrixCoefficient (U t) (blockDiagonalQuotientMatrix_comul b M hD hUpper t),
      hLie t]
    simp only [Matrix.zero_apply, map_zero, mul_zero, Finset.sum_const_zero]
  have hCounit (t : β) (i j : diagonalBlockIndices b t) :
      Coalgebra.counit (R := k₀) (U t i j) = if i = j then 1 else 0 := by
    change Coalgebra.counit (R := k₀) (M i.val j.val) = _
    rw [he]
    simp only [Subtype.val_inj]
  have hInv (t : β) (i j : diagonalBlockIndices b t) :
      D.val (hopfAntipodeAlgHom k₀ Q (U t i j)) = 0 :=
    matrixAntipode_derivative_zero (U t) (blockDiagonalQuotientMatrix_comul b M hD hUpper t)
      (hCounit t) D.val (hEntries t) i j
  apply Subtype.ext
  apply Derivation.ext_of_adjoin_eq_top _ (blockDiagonalAlgebra_adjoin_self b M hD hUpper)
  intro q hq
  change D.val q = 0
  rcases hq with ⟨⟨⟨i, j⟩, hij⟩, rfl⟩ | ⟨_, ⟨⟨⟨i, j⟩, hij⟩, rfl⟩, rfl⟩
  · exact hEntries (b i) ⟨i, rfl⟩ ⟨j, hij.symm⟩
  · exact hInv (b i) ⟨i, rfl⟩ ⟨j, hij.symm⟩

end Faithfulness

section KillingComplement

universe u

variable {k H : Type u} {V : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing H] [HopfAlgebra k H] [AddCommGroup V] [Module k V]

local notation "𝔤" => hopfInvariantDerivations k H

/-- On the actual diagonal quotient, the Lie algebra splits as its center
and an ideal with nondegenerate Killing form. -/
theorem blockDiagonalQuotient_derived_isKilling_and_isCompl_center
    [LieRingModule (hopfInvariantDerivations k H) V] [LieModule k (hopfInvariantDerivations k H) V]
    {n : ℕ} (s : RelSeries (fun P Q : LieSubmodule k 𝔤 V => P ⋖ Q))
    (v : Basis (Fin n) k V) (b : Fin n → Fin s.length)
    (hSpan : ∀ t : Fin (s.length + 1),
      Submodule.span k (v '' {i | (b i).val < t.val}) = (s t).toSubmodule)
    (M : Matrix (Fin n) (Fin n) H)
    (hD : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (M i j) = if i = j then 1 else 0)
    (hUpper : M.BlockTriangular b)
    (hLie : ∀ D : 𝔤, LinearMap.toMatrix v v (LieModule.toEnd k 𝔤 V D) = hopfLieMatrix M D) :
    let Q := blockDiagonalAlgebra (k := k) b M
    letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
    let L := hopfInvariantDerivations k Q
    IsKilling k (derivedSeries k L 1) ∧ IsCompl (derivedSeries k L 1) (center k L) := by
  let Q := blockDiagonalAlgebra (k := k) b M
  letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
  let L := hopfInvariantDerivations k Q
  letI : Algebra.FiniteType k Q := blockDiagonalAlgebra_finiteType b M
  letI : FiniteDimensional k (HopfCotangent k Q) := hopfCotangent_finiteDimensional k Q
  letI : FiniteDimensional k (HopfLieVector k Q k) := inferInstance
  letI : FiniteDimensional k L := (hopfLieVectorInvariantDerivations (k := k) (H := Q)).finiteDimensional
  let A (t : Fin s.length) := diagonalBlockIndices b t → k
  let ρ (t : Fin s.length) := blockDiagonalQuotientLieAction b M hD hUpper t
  letI : ∀ t, LieRingModule L (A t) := fun t => LieRingModule.compLieHom (A t) (ρ t)
  letI : ∀ t, LieModule k L (A t) := fun t => LieModule.compLieHom (A t) (ρ t)
  letI : ∀ t, FiniteDimensional k (A t) := fun t => by
    change FiniteDimensional k (diagonalBlockIndices b t → k)
    infer_instance
  letI : ∀ t, LieModule.IsIrreducible k L (A t) := fun t =>
    blockDiagonalQuotientLieAction_irreducible s v b hSpan M hD hUpper hLie t
  exact derived_isKilling_and_isCompl_center_of_faithful_family A
    (blockDiagonalQuotientLieActions_faithful b M hD he hUpper)

end KillingComplement


section ActualQuotient

universe u

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing H] [IsDomain H] [HopfAlgebra k H] {n : ℕ}

/-- A generating representation of an integral group gives an actual
diagonal-block quotient with reductive Lie algebra. -/
theorem exists_reductiveBlockDiagonalQuotient
    (U : (Matrix (Fin n) (Fin n) H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : Fin n × Fin n => U.val ij.1 ij.2) = ⊤) :
    ∃ (r : ℕ) (b : Fin n → Fin r) (P : (Matrix (Fin n) (Fin n) k)ˣ),
      let V := conjugateMatrixUnit P U
      ∃ (hDv : ∀ i j, Coalgebra.comul (R := k) (V.val i j) = ∑ l, V.val i l ⊗ₜ[k] V.val l j)
        (hUpper : V.val.BlockTriangular b),
        Monotone b ∧
        (∀ i j, Coalgebra.counit (R := k) (V.val i j) = if i = j then 1 else 0) ∧
        Algebra.adjoin k (Set.range fun ij : Fin n × Fin n => V.val ij.1 ij.2) = ⊤ ∧
        let Q := blockDiagonalAlgebra (k := k) b V.val
        letI := (blockDiagonalAlgebra_isHopf b V.val hDv hUpper).hopfAlgebra
        let L := hopfInvariantDerivations k Q
        IsKilling k (derivedSeries k L 1) ∧ IsCompl (derivedSeries k L 1) (center k L) := by
  letI := LieRingModule.compLieHom (Fin n → k) (hopfMatrixLieAction U.val hD)
  letI := LieModule.compLieHom (Fin n → k) (hopfMatrixLieAction U.val hD)
  obtain ⟨s, v, b, _, _, hb, hv, hUpper, hDv, hev, hGenv⟩ :=
    exists_hopfMatrix_adapted_to_lieCompositionFlag U hD he hGen
  let V := conjugateMatrixUnit (flagBasisMatrix v) U
  refine ⟨s.length, b, flagBasisMatrix v, hDv, hUpper, hb, hev, hGenv, ?_⟩
  exact blockDiagonalQuotient_derived_isKilling_and_isCompl_center s v b hv V.val hDv hev hUpper
    (hopfMatrixLieAction_toMatrix U hD v)

end ActualQuotient

end WideE
