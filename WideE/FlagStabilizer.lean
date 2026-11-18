import WideE.HopfQuotient
import Mathlib.LinearAlgebra.Matrix.Block

/-! The stabilizer of the coordinate flag in an affine matrix group. -/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

section Flag

variable {A : Type*} [CommRing A] {n : ℕ}

/-- A matrix stabilizes the coordinate flag exactly when it is upper triangular. -/
theorem blockTriangular_iff_preserves_coordinateFlag (M : Matrix (Fin n) (Fin n) A) :
    M.BlockTriangular id ↔ ∀ (d : ℕ) (x : Fin n → A), (∀ j, d ≤ j.val → x j = 0) →
      ∀ i, d ≤ i.val → (M *ᵥ x) i = 0 := by
  classical
  constructor
  · intro h d x hx i hi
    change ∑ j, M i j * x j = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : d ≤ j.val
    · rw [hx j hj, mul_zero]
    · rw [h (Nat.lt_of_not_ge hj |>.trans_le hi), zero_mul]
  · intro h i j hij
    let x : Fin n → A := fun l => if l = j then 1 else 0
    have hx : ∀ l, j.val + 1 ≤ l.val → x l = 0 := by
      intro l hl
      have hne : l ≠ j := fun e => (Nat.not_succ_le_self j.val) (e ▸ hl)
      simp only [x, if_neg hne]
    have he := h (j.val + 1) x hx i (Nat.succ_le_of_lt hij)
    simpa only [Matrix.mulVec, dotProduct, x, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] using he

end Flag

section MatrixAntipode

variable {k H ι : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H]
  [Fintype ι] [DecidableEq ι]

/-- Inversion acts on the matrix coefficients by taking the inverse matrix. -/
theorem hopfMatrix_inv_eq_map_antipode (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0) :
    U.inv = U.val.map (HopfAlgebra.antipode (R := k) (A := H)) := by
  let σ := HopfAlgebra.antipode (R := k) (A := H)
  have h : U.val * U.val.map σ = 1 := by
    ext i j
    have hA := HopfAlgebra.mul_antipode_lTensor_comul_apply (R := k) (U.val i j)
    rw [hD i j] at hA
    simpa only [map_sum, LinearMap.lTensor_tmul, LinearMap.mul'_apply, Matrix.mul_apply,
      Matrix.map_apply, he, apply_ite (algebraMap k H), map_one, map_zero, Matrix.one_apply] using hA
  calc
    U.inv = U.inv * 1 := (mul_one _).symm
    _ = U.inv * (U.val * U.val.map σ) := congrArg (U.inv * ·) h.symm
    _ = U.val.map σ := by rw [← mul_assoc, U.inv_val, one_mul]

end MatrixAntipode

section Stabilizer

variable {k H : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H] {n : ℕ}

/-- Equations for the closed subgroup preserving the standard flag. -/
def flagStabilizerIdeal (M : Matrix (Fin n) (Fin n) H) : Ideal H :=
  Ideal.span {x | ∃ i j, j < i ∧ M i j = x}

variable (U : (Matrix (Fin n) (Fin n) H)ˣ)
  (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
  (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)

local notation "π" => (Ideal.Quotient.mkₐ k (flagStabilizerIdeal U.val))
local notation "σ" => (HopfAlgebra.antipode (R := k) (A := H))

private theorem flagStabilizer_entry_zero {i j : Fin n} (h : j < i) : π (U.val i j) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, j, h, rfl⟩)

include hD he in
/-- The equations of the flag stabilizer cut out a Hopf quotient. -/
theorem flagStabilizerIdeal_isHopf : IsHopfIdeal k (flagStabilizerIdeal U.val) := by
  classical
  refine IsHopfIdeal.span_of_generators k _ ?_ ?_ ?_
  · rintro x ⟨i, j, hij, rfl⟩
    change Algebra.TensorProduct.map π π (Coalgebra.comul (R := k) (U.val i j)) = 0
    rw [hD i j, map_sum]
    apply Finset.sum_eq_zero
    intro l _
    rw [Algebra.TensorProduct.map_tmul]
    by_cases hl : l < i
    · rw [flagStabilizer_entry_zero U hl, TensorProduct.zero_tmul]
    · rw [flagStabilizer_entry_zero U (hij.trans_le (le_of_not_gt hl)), TensorProduct.tmul_zero]
  · rintro x ⟨i, j, hij, rfl⟩
    exact (he i j).trans (if_neg hij.ne.symm)
  · rintro x ⟨i, j, hij, rfl⟩
    let V : (Matrix (Fin n) (Fin n) (H ⧸ flagStabilizerIdeal U.val))ˣ :=
      U.map ((π).toRingHom.mapMatrix).toMonoidHom
    have hV : V.val.BlockTriangular id := fun _ _ h => flagStabilizer_entry_zero (k := k) U h
    letI : Invertible V.val := Units.invertible V
    have hInv : V.inv.BlockTriangular id := by
      change ((V⁻¹ : (Matrix (Fin n) (Fin n) (H ⧸ flagStabilizerIdeal U.val))ˣ) :
        Matrix (Fin n) (Fin n) (H ⧸ flagStabilizerIdeal U.val)).BlockTriangular id
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular hV
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) H => π (M i j))
      (hopfMatrix_inv_eq_map_antipode U hD he)
    exact h.symm.trans (hInv hij)

end Stabilizer

section Points

variable {k H A : Type*} [CommRing k] [CommRing H] [Algebra k H] [CommRing A] [Algebra k A]
  {n : ℕ} (M : Matrix (Fin n) (Fin n) H)

/-- The quotient by the stabilizer equations represents flag-preserving points. -/
def flagStabilizerPointEquiv : ((H ⧸ flagStabilizerIdeal M) →ₐ[k] A) ≃
    {g : H →ₐ[k] A // (M.map g).BlockTriangular id} where
  toFun g := ⟨g.comp (Ideal.Quotient.mkₐ k _), fun i j hij => by
    change g (Ideal.Quotient.mkₐ k (flagStabilizerIdeal M) (M i j)) = 0
    rw [show Ideal.Quotient.mkₐ k (flagStabilizerIdeal M) (M i j) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, j, hij, rfl⟩), map_zero]⟩
  invFun g := Ideal.Quotient.liftₐ (flagStabilizerIdeal M) g.val (by
    change flagStabilizerIdeal M ≤ RingHom.ker g.val.toRingHom
    unfold flagStabilizerIdeal
    rw [Ideal.span_le]
    rintro x ⟨i, j, hij, rfl⟩
    exact g.2 hij)
  left_inv g := by
    apply Ideal.Quotient.algHom_ext
    rfl
  right_inv g := Subtype.ext rfl

end Points

end WideE
