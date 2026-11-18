import WideE.PositiveKostantNormalizer

/-! A regular Cartan point has a representative on the principal slice in its actual adjoint orbit. -/

noncomputable section

open LieAlgebra LieAlgebra.IsKilling
open scoped Matrix TensorProduct

namespace WideE

variable {k L A ι : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ k L] [LieAlgebra.IsKilling k L] [FiniteDimensional k L]
  [CommRing A] [HopfAlgebra k A] [Fintype ι] [DecidableEq ι]
  {H : LieSubalgebra k L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable k H L]

local notation "Φ" => LieAlgebra.IsKilling.rootSystem H
local notation "𝔤" => hopfInvariantDerivations k A
local notation "J" => hopfLieVectorInvariantDerivations (k := k) (H := A)
local notation "B" => kostantWeightFiltration (k := k)

/-- Negative normalization of a regular Cartan term gives a slice point
that is genuinely conjugate to the original Cartan point. -/
theorem exists_principalKostantSlice_conjugate_regularCartan (U : (Matrix ι ι A)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (j : L →ₗ⁅k⁆ 𝔤) (b : (Φ).Base) [Fintype b.support] (e : b.support → L)
    (heRoot : ∀ i : b.support, e i ∈ rootSpace H (((Φ).root i : H →ₗ[k] k) : H → k))
    {f : L} (t : IsSl2Triple (principalCartanElement b : L) (∑ i, e i) f)
    (z : H) (hz : ∀ α : H.root, (Φ).root α z ≠ 0) :
    ∃ (s : L) (p : A →ₐ[k] k),
      s ∈ B (principalCartanElement b : L) 0 ∧ ⁅f, s⁆ = 0 ∧
      U.val.map p - 1 ∈ B (hopfLieMatrix U.val (j (principalCartanElement b))) 1 ∧
      hopfAdjoint p ((J).symm (j ((∑ i, e i) + (z : L)))) =
        (J).symm (j ((∑ i, e i) + s)) ∧
      ∃ q : A →ₐ[k] k, hopfAdjoint q ((J).symm (j ((∑ i, e i) + s))) =
        (J).symm (j (z : L)) := by
  classical
  let h : L := principalCartanElement b
  let E : L := ∑ i, e i
  have hZ : (z : L) ∈ negativeEvenWeightSpace (k := k) h 0 := by
    change (z : L) ∈ principalWeightSpace b 0
    rw [principalWeightSpace_zero_eq_cartan]
    exact z.property
  let z₀ : B h 0 := ⟨z, negativeEvenWeightSpace_le_filtration h le_rfl hZ⟩
  obtain ⟨p, s, hp, hs, hk, hNeg⟩ := exists_hopfPoint_kostantNormalizer_negative
    U hD he hGen j t z₀
  obtain ⟨q, hPos⟩ := exists_hopfPoint_principalCartan_conjugation U hD he hGen j b e heRoot z hz
  letI : Group (A →ₐ[k] k) := hopfPointGroup
  letI : Algebra.FiniteType k A := ⟨⟨(Set.finite_range
    (fun ij : ι × ι => U.val ij.1 ij.2)).toFinset, by simpa using hGen⟩⟩
  letI : FiniteDimensional k (HopfCotangent k A) := hopfCotangent_finiteDimensional k A
  let bC := Module.finBasis k (HopfCotangent k A)
  refine ⟨s, p, hs, hk, hp, hNeg, q * p⁻¹, ?_⟩
  change hopfAdjoint p ((J).symm (j (E + (z : L)))) = (J).symm (j (E + s)) at hNeg
  change hopfAdjoint (q * p⁻¹) ((J).symm (j (E + s))) = (J).symm (j (z : L))
  rw [← hNeg, ← hopfAdjoint_mul bC, mul_assoc, inv_mul_cancel, mul_one]
  exact hPos

end WideE
