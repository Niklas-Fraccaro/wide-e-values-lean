import WideE.HopfLieMatrix
import WideE.InvariantIdeal
import WideE.MatrixFlagRefinement
import NilpotentMatrixExpDerivative

/-! A flag preserved by the Lie algebra of a connected group is preserved by the group. -/

noncomputable section

open scoped Matrix TensorProduct
open StrictEUnit

namespace WideE

variable {k H ι : Type*} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsDomain H] [Fintype ι] [DecidableEq ι]

omit [CharZero k] [Algebra.FiniteType k H] [IsDomain H] in
/-- A basis change of the universal matrix induces the same basis change on its tangent matrices. -/
theorem hopfLieMatrix_conjugateMatrixUnit (P : (Matrix ι ι k)ˣ) (U : (Matrix ι ι H)ˣ)
    (D : hopfInvariantDerivations k H) :
    hopfLieMatrix (conjugateMatrixUnit P U).val D = P.inv * hopfLieMatrix U.val D * P.val := by
  let C := (algebraMap k H).mapMatrix (m := ι)
  let ε := Bialgebra.counitAlgHom k H
  let φ := (ε.toRingHom.mapMatrix (m := ι))
  have he (T : Matrix ι ι k) : φ (C T) = T := Matrix.ext fun i j => ε.commutes (T i j)
  change φ (matrixDerivative D.val (C P.inv * U.val * C P.val)) = _
  rw [matrixDerivative_mul, matrixDerivative_constant, mul_zero, add_zero,
    matrixDerivative_mul, matrixDerivative_constant, zero_mul, zero_add, map_mul, map_mul, he, he]
  rfl

/-- A coordinate subspace stable under every tangent matrix is stable under the universal
group matrix. This applies separately to each subspace in a simultaneous flag. -/
theorem matrixCoefficient_eq_zero_of_lieInvariantSubspace (U : Matrix ι ι H)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U i j) = ∑ l, U i l ⊗ₜ[k] U l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U i j) = if i = j then 1 else 0)
    (s : Set ι) (hLie : ∀ (D : hopfInvariantDerivations k H) i j,
      i ∉ s → j ∈ s → hopfLieMatrix U D i j = 0) :
    ∀ i j, i ∉ s → j ∈ s → U i j = 0 := by
  classical
  let S : Set H := {a | ∃ i j, i ∉ s ∧ j ∈ s ∧ a = U i j}
  let J : Ideal H := Ideal.span S
  have hJ : J ≤ hopfAugmentationIdeal k H := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, j, hi, hj, rfl⟩
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    change Coalgebra.counit (R := k) (U i j) = 0
    rw [hε, if_neg hij]
  have hStable (D : hopfInvariantDerivations k H) : ∀ a ∈ J, D.val a ∈ J := by
    intro a ha
    refine Submodule.span_induction (p := fun a _ => D.val a ∈ J) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨i, j, hi, hj, rfl⟩
      rw [hopfInvariantDerivation_matrixCoefficient U hΔ D]
      apply J.sum_mem
      intro l _
      by_cases hl : l ∈ s
      · exact J.mul_mem_right _ (Ideal.subset_span ⟨i, l, hi, hl, rfl⟩)
      · rw [hLie D l j hl hj, map_zero, mul_zero]
        exact J.zero_mem
    · change D.val 0 ∈ J
      rw [map_zero]
      exact J.zero_mem
    · intro x y _ _ hx hy
      rw [map_add]
      exact J.add_mem hx hy
    · intro r x hx hd
      change D.val (r * x) ∈ J
      rw [D.val.leibniz, Algebra.id.smul_eq_mul, Algebra.id.smul_eq_mul]
      exact J.add_mem (J.mul_mem_left _ hd) (J.mul_mem_right _ hx)
  have hz := hopfInvariantIdeal_eq_bot J hJ hStable
  intro i j hi hj
  have h : U i j ∈ J := Ideal.subset_span ⟨i, j, hi, hj, rfl⟩
  rw [hz] at h
  exact h

end WideE
