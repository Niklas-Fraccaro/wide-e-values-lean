import WideE.HopfKernelTorsor
import WideE.UpperTriangularCocycle

/-! Galois cocycle reduction to the actual diagonal-block quotient. -/

noncomputable section

open scoped TensorProduct

namespace WideE

section

local notation "k" => AlgebraicComplex

variable {F : Type*} [Field F] [Algebra k F] {H : Type} {β : Type*}
  [CommRing H] [IsDomain H] [HopfAlgebra k H] [LinearOrder β] {n : ℕ}

/-- The identity fiber has a generating unitriangular representation. Thus a
cocycle is a coboundary precisely when its actual diagonal-block image is. -/
theorem isHopfPointCoboundary_iff_blockDiagonal
    (b : Fin n → β) (M : Matrix (Fin n) (Fin n) H)
    (hD : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (M i j) = if i = j then 1 else 0)
    (hUpper : M.BlockTriangular b) (hb : Monotone b)
    (hGen : Algebra.adjoin k (Set.range fun ij : Fin n × Fin n => M ij.1 ij.2) = ⊤)
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (c : (E ≃ₐ[F] E) → H →ₐ[k] E) (hc : IsHopfPointCocycle c) :
    letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
    IsHopfPointCoboundary c ↔
      IsHopfPointCoboundary (precomposeHopfPointCocycle (blockDiagonalQuotientMap b M hD hUpper) c) := by
  letI : IsAlgClosed k := IsAlgClosure.isAlgClosed ℚ
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  letI : Algebra.FiniteType k H := ⟨Subalgebra.fg_def.mpr ⟨_, Set.finite_range _, hGen⟩⟩
  letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
  let j := blockDiagonalQuotientMap b M hD hUpper
  letI : IsDomain (H ⧸ blockDiagonalKernelIdeal b M hD hUpper) :=
    blockDiagonalKernel_isDomain b M hD he hUpper hb hGen
  refine ⟨fun h => h.precompose j, fun h => ?_⟩
  apply isHopfPointCoboundary_of_quotient_and_hopfKernel E j
    (blockDiagonalQuotient_faithfullyFlat b M hD hUpper) c hc h
  letI := (blockDiagonalKernelIdeal_isHopf b M hD hUpper).quotientHopf
  obtain ⟨hD', he', hGen'⟩ := blockDiagonalKernelMatrix_relations b M hD hUpper he hGen
  have hUpper' := (blockDiagonalKernelMatrix_unitriangular b M hD hUpper hb he).1
  intro L d hd
  exact upperTriangular_isHopfPointCoboundary
    (blockDiagonalKernelMatrix b M hD hUpper) hD' he' hUpper' hGen' L d hd

end

end WideE
