import WideE.BlockDiagonalGeneratingMatrix
import WideE.ReductiveBlockQuotient

/-! Central tangents are diagonal on the chosen generating matrix of the actual quotient. -/

noncomputable section

open scoped BigOperators Matrix TensorProduct
open LieAlgebra

namespace WideE

section Center

universe u

variable {k H : Type u} {V : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing H] [HopfAlgebra k H] [AddCommGroup V] [Module k V]
  [LieRingModule (hopfInvariantDerivations k H) V] [LieModule k (hopfInvariantDerivations k H) V]

local notation "𝔤" => hopfInvariantDerivations k H

set_option maxHeartbeats 1900000 in
/-- All central tangents are diagonal in the chosen direct sum of the actual blocks and their duals. -/
theorem blockDiagonalQuotientGeneratingMatrix_center_diagonal
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
    ∀ D ∈ center k L, ∃ d : blockDiagonalGeneratingIndex b → k,
      hopfLieMatrix (blockDiagonalQuotientGeneratingMatrix b M hD hUpper) D = Matrix.diagonal d := by
  letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
  intro Q L D hDcenter
  letI : Algebra.FiniteType k Q := blockDiagonalAlgebra_finiteType b M
  letI : FiniteDimensional k (HopfCotangent k Q) := hopfCotangent_finiteDimensional k Q
  letI : FiniteDimensional k (HopfLieVector k Q k) := inferInstance
  letI : FiniteDimensional k L := (hopfLieVectorInvariantDerivations (k := k) (H := Q)).finiteDimensional
  let U (t : Fin s.length) := blockDiagonalQuotientMatrix (k := k) b M t
  have hScalar (t : Fin s.length) :
      ∃ c : k, hopfLieMatrix (U t) D = Matrix.diagonal (fun _ => c) := by
    let A := diagonalBlockIndices b t → k
    let ρ := blockDiagonalQuotientLieAction b M hD hUpper t
    letI := LieRingModule.compLieHom A ρ
    letI := LieModule.compLieHom A ρ
    letI : FiniteDimensional k A := by
      change FiniteDimensional k (diagonalBlockIndices b t → k)
      infer_instance
    letI : LieModule.IsIrreducible k L A :=
      blockDiagonalQuotientLieAction_irreducible s v b hSpan M hD hUpper hLie t
    obtain ⟨c, hc⟩ := exists_radical_toEnd_eq_smul (k := k) (L := L) (V := A)
      ⟨D, center_le_radical k L hDcenter⟩
    refine ⟨c, Matrix.ext fun i j => ?_⟩
    have h := LinearMap.congr_fun hc (Pi.single j 1)
    change ρ D (Pi.single j 1) = (c • LinearMap.id) (Pi.single j 1) at h
    rw [show ρ D (Pi.single j 1) = hopfLieMatrix (U t) D *ᵥ Pi.single j 1 from
      blockDiagonalQuotientLieAction_apply b M hD hUpper t _ D] at h
    have hij := congrFun h i
    rw [Matrix.mulVec_single_one] at hij
    by_cases hn : i = j
    · subst j
      simpa only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, Pi.single_eq_same,
        smul_eq_mul, mul_one, Matrix.diagonal_apply, if_pos rfl, if_true] using hij
    · simpa only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, Pi.single_eq_of_ne hn,
        smul_zero, Matrix.diagonal_apply, if_neg hn] using hij
  classical
  choose c hc using hScalar
  let d (t : Fin s.length × Bool) : diagonalBlockIndices b t.1 → k :=
    fun _ => if t.2 then -(c t.1) else c t.1
  refine ⟨fun p => d p.1 p.2, ?_⟩
  rw [blockDiagonalQuotientGeneratingMatrix, hopfLieMatrix_blockDiagonal', ← Matrix.blockDiagonal'_diagonal d]
  apply congrArg Matrix.blockDiagonal'
  funext t
  rcases t with ⟨t, tag⟩
  cases tag
  · exact hc t
  · change hopfLieMatrix (dualHopfMatrix (k := k) (U t)) D = Matrix.diagonal (fun _ => -(c t))
    rw [hopfLieMatrix_dual _ (blockDiagonalQuotientMatrix_comul b M hD hUpper t)
      (blockDiagonalQuotientMatrix_counit b M hD hUpper he t), hc, Matrix.diagonal_transpose,
      ← Matrix.diagonal_neg]

end Center

section Nilpotence

variable {k A ι : Type*} [Field k] [CommRing A] [HopfAlgebra k A] [Fintype ι] [DecidableEq ι]

/-- A diagonal tangent on a generating representation is zero if it is nilpotent. -/
theorem hopfLie_eq_zero_of_diagonal_nilpotent (U : Matrix ι ι A)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U i j) = ∑ l, U i l ⊗ₜ[k] U l j)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U ij.1 ij.2) = ⊤)
    (D : hopfInvariantDerivations k A) (d : ι → k)
    (hDiag : hopfLieMatrix U D = Matrix.diagonal d)
    (hNil : IsNilpotent (hopfLieMatrix U D)) : D = 0 := by
  obtain ⟨m, hm⟩ := hNil
  rw [hDiag, Matrix.diagonal_pow] at hm
  have hd (i : ι) : d i = 0 := by
    have hi := congrArg (fun M : Matrix ι ι k => M i i) hm
    have hz : d i ^ m = 0 := by simpa only [Matrix.diagonal_apply_eq, Matrix.zero_apply] using hi
    by_contra h
    exact pow_ne_zero m h hz
  apply (hopfLieMatrixHom_injective U hD hGen)
  change hopfLieMatrix U D = (hopfLieMatrixHom U hD).toLinearMap 0
  rw [map_zero, hDiag, show d = 0 from funext hd]
  exact Matrix.diagonal_zero

end Nilpotence

section ActualQuotient

universe u

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing H] [IsDomain H] [HopfAlgebra k H] {n : ℕ}

set_option maxHeartbeats 2000000 in
/-- The actual diagonal-block quotient, with one generating matrix on which
all central tangents are diagonal and have trivial nilpotent part. -/
theorem exists_reductiveBlockDiagonalQuotient_with_matrix
    (U : (Matrix (Fin n) (Fin n) H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : Fin n × Fin n => U.val ij.1 ij.2) = ⊤) :
    ∃ (r : ℕ) (b : Fin n → Fin r) (P : (Matrix (Fin n) (Fin n) k)ˣ),
      let V := conjugateMatrixUnit P U
      ∃ (hDv : ∀ i j, Coalgebra.comul (R := k) (V.val i j) = ∑ l, V.val i l ⊗ₜ[k] V.val l j)
        (hev : ∀ i j, Coalgebra.counit (R := k) (V.val i j) = if i = j then 1 else 0)
        (hUpper : V.val.BlockTriangular b),
        Monotone b ∧
        Algebra.adjoin k (Set.range fun ij : Fin n × Fin n => V.val ij.1 ij.2) = ⊤ ∧
        let Q := blockDiagonalAlgebra (k := k) b V.val
        letI := (blockDiagonalAlgebra_isHopf b V.val hDv hUpper).hopfAlgebra
        let L := hopfInvariantDerivations k Q
        let I := blockDiagonalGeneratingIndex b
        let W := blockDiagonalQuotientGeneratingUnit b V.val hDv hUpper hev
        (∀ i j : I, Coalgebra.comul (R := k) (W.val i j) =
          ∑ l : I, W.val i l ⊗ₜ[k] W.val l j) ∧
        (∀ i j : I, Coalgebra.counit (R := k) (W.val i j) = if i = j then 1 else 0) ∧
        Algebra.adjoin k (Set.range fun ij : I × I => W.val ij.1 ij.2) = ⊤ ∧
        IsKilling k (derivedSeries k L 1) ∧ IsCompl (derivedSeries k L 1) (center k L) ∧
        (∀ D ∈ center k L, ∃ d : I → k, hopfLieMatrix W.val D = Matrix.diagonal d) ∧
        (∀ D ∈ center k L, IsNilpotent (hopfLieMatrix W.val D) → D = 0) := by
  letI := LieRingModule.compLieHom (Fin n → k) (hopfMatrixLieAction U.val hD)
  letI := LieModule.compLieHom (Fin n → k) (hopfMatrixLieAction U.val hD)
  obtain ⟨s, v, b, _, _, hb, hv, hUpper, hDv, hev, hGenv⟩ :=
    exists_hopfMatrix_adapted_to_lieCompositionFlag U hD he hGen
  let V := conjugateMatrixUnit (flagBasisMatrix v) U
  refine ⟨s.length, b, flagBasisMatrix v, hDv, hev, hUpper, hb, hGenv, ?_⟩
  letI := (blockDiagonalAlgebra_isHopf b V.val hDv hUpper).hopfAlgebra
  let hLie := hopfMatrixLieAction_toMatrix U hD v
  let h := blockDiagonalQuotientGeneratingMatrix_relations b V.val hDv hUpper hev
  let hG := blockDiagonalQuotientGeneratingMatrix_generates b V.val hDv hUpper
  let hK := blockDiagonalQuotient_derived_isKilling_and_isCompl_center s v b hv V.val hDv hev hUpper hLie
  let hZ := blockDiagonalQuotientGeneratingMatrix_center_diagonal s v b hv V.val hDv hev hUpper hLie
  refine ⟨h.1, h.2, hG, hK.1, hK.2, hZ, fun D hDcenter hn => ?_⟩
  obtain ⟨d, hd⟩ := hZ D hDcenter
  exact hopfLie_eq_zero_of_diagonal_nilpotent _ h.1 hG D d hd hn

end ActualQuotient

end WideE
