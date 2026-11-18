import WideE.FlagStabilizer
import Mathlib.Algebra.Group.Commute.Units

/-! The closed subgroup preserving each weight space of a diagonal torus. -/

noncomputable section

open scoped TensorProduct Matrix

namespace WideE

section Matrices

variable {R ι Λ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

private def weightProjection (χ : ι → Λ) (a : Λ) : Matrix ι ι R := by
  classical
  exact Matrix.diagonal (fun i => if χ i = a then 1 else 0)

private theorem weightBlocks_iff_commute_projections (χ : ι → Λ) (M : Matrix ι ι R) :
    (∀ i j, χ i ≠ χ j → M i j = 0) ↔
      ∀ a : Λ, Commute M (weightProjection χ a) := by
  classical
  constructor
  · intro h a
    apply Matrix.ext
    intro i j
    rw [weightProjection, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : χ i = χ j
    · rw [hij, mul_comm]
    · rw [h i j hij, zero_mul, mul_zero]
  · intro h i j hij
    have hM := congrArg (fun N : Matrix ι ι R => N i j) (h (χ i)).eq
    change (M * weightProjection (R := R) χ (χ i)) i j =
      (weightProjection (R := R) χ (χ i) * M) i j at hM
    rw [weightProjection, Matrix.mul_diagonal, Matrix.diagonal_mul, if_neg (Ne.symm hij), if_pos rfl,
      mul_zero, one_mul] at hM
    exact hM.symm

private theorem weightBlocks_inverse (χ : ι → Λ) (U : (Matrix ι ι R)ˣ)
    (h : ∀ i j, χ i ≠ χ j → U.val i j = 0) : ∀ i j, χ i ≠ χ j → U.inv i j = 0 := by
  rw [weightBlocks_iff_commute_projections] at h ⊢
  intro a
  exact (h a).units_inv_left

variable {k : Type*} [Field k] [Algebra k R]

/-- A diagonal operator with distinct scalars on different weights has precisely
the matrices preserving those weight spaces as its centralizer. -/
theorem commute_weightDiagonal_iff (χ : ι → Λ) (a : Λ → k) (M : Matrix ι ι R)
    (hDistinct : ∀ i j, χ i ≠ χ j → a (χ i) ≠ a (χ j)) :
    Commute M (Matrix.diagonal fun i => algebraMap k R (a (χ i))) ↔
      ∀ i j, χ i ≠ χ j → M i j = 0 := by
  constructor
  · intro h i j hij
    have hh := congrArg (fun N : Matrix ι ι R => N i j) h.eq
    change (M * Matrix.diagonal fun i => algebraMap k R (a (χ i))) i j =
      ((Matrix.diagonal fun i => algebraMap k R (a (χ i))) * M) i j at hh
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm _ (M i j)] at hh
    let a := a (χ j) - a (χ i)
    have hUnit : IsUnit (algebraMap k R a) :=
      (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (hDistinct i j hij).symm)).map (algebraMap k R)
    have hz : M i j * algebraMap k R a = 0 := by
      simp only [a, map_sub, mul_sub, hh, sub_self]
    obtain ⟨b, hb⟩ := hUnit
    calc
      M i j = (M i j * (b : R)) * b.inv := by rw [mul_assoc, b.val_inv, mul_one]
      _ = 0 := by rw [hb, hz, zero_mul]
  · intro h
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : χ i = χ j
    · rw [hij, mul_comm]
    · rw [h i j hij, zero_mul, mul_zero]

end Matrices

section HopfIdeal

variable {k H ι Λ : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H]
  [Fintype ι] [DecidableEq ι]

/-- The coordinate equations for preserving the weight spaces of a matrix representation. -/
def weightCentralizerIdeal (χ : ι → Λ) (M : Matrix ι ι H) : Ideal H :=
  Ideal.span {a | ∃ i j, χ i ≠ χ j ∧ M i j = a}

variable (U : (Matrix ι ι H)ˣ) (χ : ι → Λ)

local notation "I" => (weightCentralizerIdeal χ U.val)
local notation "π" => (Ideal.Quotient.mkₐ k I)

private theorem weightCentralizerIdeal_entry_zero {i j : ι} (h : χ i ≠ χ j) : π (U.val i j) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, j, h, rfl⟩)

/-- The equations for the block centralizer give the corresponding closed subgroup. -/
theorem weightCentralizerIdeal_isHopf
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0) : IsHopfIdeal k I := by
  classical
  refine IsHopfIdeal.span_of_generators k _ ?_ ?_ ?_
  · rintro _ ⟨i, j, hij, rfl⟩
    change Algebra.TensorProduct.map π π (Coalgebra.comul (R := k) (U.val i j)) = 0
    rw [hD, map_sum]
    apply Finset.sum_eq_zero
    intro l _
    rw [Algebra.TensorProduct.map_tmul]
    by_cases hil : χ i = χ l
    · have hlj : χ l ≠ χ j := fun h => hij (hil.trans h)
      rw [weightCentralizerIdeal_entry_zero (k := k) U χ hlj, TensorProduct.tmul_zero]
    · rw [weightCentralizerIdeal_entry_zero (k := k) U χ hil, TensorProduct.zero_tmul]
  · rintro _ ⟨i, j, hij, rfl⟩
    exact (he i j).trans (if_neg (fun h => hij (congrArg χ h)))
  · rintro _ ⟨i, j, hij, rfl⟩
    let V : (Matrix ι ι (H ⧸ I))ˣ := U.map ((π).toRingHom.mapMatrix).toMonoidHom
    have hV : ∀ i j, χ i ≠ χ j → V.val i j = 0 :=
      fun _ _ h => weightCentralizerIdeal_entry_zero (k := k) U χ h
    have h := congrArg (fun M : Matrix ι ι H => π (M i j)) (hopfMatrix_inv_eq_map_antipode U hD he)
    exact h.symm.trans (weightBlocks_inverse χ V hV i j hij)

end HopfIdeal

end WideE
