import Mathlib.LinearAlgebra.Matrix.Block

/-! Extracting the diagonal blocks of a block-unitriangular factorization. -/

noncomputable section

open scoped Matrix

namespace WideE

section SchurComplement

variable {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq ι]

/-- The Schur complement of the leading block selected by the predicate. -/
def schurComplementAt (M : Matrix ι ι R) (p : ι → Prop) [DecidablePred p] :
    Matrix {i // ¬p i} {i // ¬p i} R := M.toBlock (fun i => ¬p i) (fun i => ¬p i) -
    M.toBlock (fun i => ¬p i) p * (M.toBlock p p)⁻¹ * M.toBlock p (fun i => ¬p i)

private theorem map_nonsing_inv_of_det_isUnit (f : R →+* S)
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n R) (hM : IsUnit M.det) :
    M⁻¹.map f = (M.map f)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  change (f.mapMatrix M⁻¹) * (f.mapMatrix M) = 1
  rw [← map_mul, Matrix.nonsing_inv_mul M hM, map_one]

/-- Schur extraction commutes with specialization on the leading-minor open. -/
theorem schurComplementAt_map (f : R →+* S) (M : Matrix ι ι R) (p : ι → Prop) [DecidablePred p]
    (hM : IsUnit (M.toBlock p p).det) :
    (schurComplementAt M p).map f = schurComplementAt (M.map f) p := by
  rw [schurComplementAt, schurComplementAt, Matrix.map_sub _ (map_sub f),
    Matrix.map_mul, Matrix.map_mul, map_nonsing_inv_of_det_isUnit f _ hM]
  rfl

/-- For a lower, block-diagonal, upper product, taking a Schur complement
deletes the first diagonal block and restricts the three factors. -/
theorem schurComplementAt_mul (L T U : Matrix ι ι R) (p : ι → Prop) [DecidablePred p]
    (hL₀ : L.toBlock p (fun i => ¬p i) = 0)
    (hT₀ : T.toBlock p (fun i => ¬p i) = 0)
    (hT₁ : T.toBlock (fun i => ¬p i) p = 0)
    (hU₀ : U.toBlock (fun i => ¬p i) p = 0)
    (hL : IsUnit (L.toBlock p p).det) (hT : IsUnit (T.toBlock p p).det)
    (hU : IsUnit (U.toBlock p p).det) :
    schurComplementAt (L * T * U) p =
      L.toBlock (fun i => ¬p i) (fun i => ¬p i) *
        T.toBlock (fun i => ¬p i) (fun i => ¬p i) *
        U.toBlock (fun i => ¬p i) (fun i => ¬p i) := by
  classical
  let A := L.toBlock p p
  let B := T.toBlock p p
  let C := U.toBlock p p
  have hA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hL
  have hB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hT
  have hC : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul C hU
  have hC' : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hU
  have hInv : (A * B * C)⁻¹ = C⁻¹ * B⁻¹ * A⁻¹ := by
    apply Matrix.inv_eq_left_inv
    calc
      (C⁻¹ * B⁻¹ * A⁻¹) * (A * B * C) = C⁻¹ * (B⁻¹ * ((A⁻¹ * A) * (B * C))) := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hA, Matrix.one_mul, ← Matrix.mul_assoc B⁻¹ B C, hB, Matrix.one_mul, hC]
  unfold schurComplementAt
  simp only [Matrix.toBlock_mul_eq_add _ p _, hL₀, hT₀, hT₁, hU₀,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  change (L.toBlock (fun i => ¬p i) p * B * U.toBlock p (fun i => ¬p i) + _) -
    ((L.toBlock (fun i => ¬p i) p * B * C) * (A * B * C)⁻¹ *
      (A * B * U.toBlock p (fun i => ¬p i))) = _
  rw [hInv]
  let X := L.toBlock (fun i => ¬p i) p
  let Y := U.toBlock p (fun i => ¬p i)
  have hCancel : X * B * C * (C⁻¹ * B⁻¹ * A⁻¹) * (A * B * Y) = X * B * Y := by
    calc
      X * B * C * (C⁻¹ * B⁻¹ * A⁻¹) * (A * B * Y) =
          X * (B * ((C * C⁻¹) * (B⁻¹ * ((A⁻¹ * A) * (B * Y))))) := by
            simp only [Matrix.mul_assoc]
      _ = X * B * Y := by
        rw [hA, hC', Matrix.one_mul, Matrix.one_mul, ← Matrix.mul_assoc B⁻¹ B Y, hB,
          Matrix.one_mul, Matrix.mul_assoc]
  rw [show X * B * C * (C⁻¹ * B⁻¹ * A⁻¹) * (A * B * Y) =
      (X * B) * Y from hCancel, add_sub_cancel_left]

end SchurComplement

section OrderedBlocks

variable {R S ι β : Type*} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq ι]
  [LinearOrder β]

/-- The diagonal blocks given by successive Schur complements. -/
def blockSchurDiagonal (w : ι → β) (M : Matrix ι ι R) : Matrix ι ι R :=
  Matrix.of fun i j => if h : w i = w j then
    schurComplementAt M (fun l => w l < w i) ⟨i, lt_irrefl _⟩
      ⟨j, by change ¬w j < w i; rw [← h]; exact lt_irrefl _⟩
    else 0

/-- Schur extraction commutes with a map when every leading determinant is a unit. -/
theorem blockSchurDiagonal_map (w : ι → β) (f : R →+* S) (M : Matrix ι ι R)
    (hM : ∀ i, IsUnit (M.toBlock (fun j => w j < w i) (fun j => w j < w i)).det) :
    (blockSchurDiagonal w M).map f = blockSchurDiagonal w (M.map f) := by
  ext i j
  simp only [Matrix.map_apply, blockSchurDiagonal, Matrix.of_apply]
  by_cases h : w i = w j
  · simp only [dif_pos h]
    exact congrArg (fun N : Matrix {l // ¬w l < w i} {l // ¬w l < w i} S =>
      N ⟨i, lt_irrefl _⟩ ⟨j, by rw [← h]; exact lt_irrefl _⟩)
      (schurComplementAt_map f M _ (hM i))
  · simp only [dif_neg h, map_zero]

/-- A block diagonal matrix is unchanged by the extraction. -/
theorem blockSchurDiagonal_eq_self (w : ι → β) (M : Matrix ι ι R)
    (hM : ∀ i j, w i ≠ w j → M i j = 0) :
    blockSchurDiagonal w M = M := by
  classical
  ext i j
  simp only [blockSchurDiagonal, Matrix.of_apply]
  by_cases h : w i = w j
  · simp only [dif_pos h]
    let p (l : ι) := w l < w i
    have h₀ : M.toBlock (fun l => ¬p l) p = 0 := by
      ext r s
      apply hM
      intro e
      apply r.prop
      change w r.val < w i
      rw [e]
      exact s.prop
    change (schurComplementAt M p) ⟨i, lt_irrefl _⟩
      ⟨j, by change ¬w j < w i; rw [← h]; exact lt_irrefl _⟩ = _
    rw [schurComplementAt, h₀, Matrix.zero_mul, Matrix.zero_mul, sub_zero]
    rfl
  · rw [dif_neg h, hM i j h]

/-- Every leading block of an invertible block-triangular matrix is invertible. -/
theorem prefixDet_isUnit_of_blockTriangular (w : ι → β) (M : Matrix ι ι R)
    (hM : M.BlockTriangular w) (hDet : IsUnit M.det) (a : β) :
    IsUnit (M.toBlock (fun j => w j < a) (fun j => w j < a)).det := by
  letI : Invertible M := ((Matrix.isUnit_iff_isUnit_det M).mpr hDet).nonempty_invertible.some
  letI := hM.invertibleToBlock a
  exact Matrix.isUnit_det_of_invertible _

/-- The same leading-block assertion for a lower block-triangular matrix. -/
theorem prefixDet_isUnit_of_lowerBlockTriangular (w : ι → β) (M : Matrix ι ι R)
    (hM : M.BlockTriangular (OrderDual.toDual ∘ w)) (hDet : IsUnit M.det) (a : β) :
    IsUnit (M.toBlock (fun j => w j < a) (fun j => w j < a)).det := by
  have hmt : Mᵀ.BlockTriangular w := fun i j h => hM (i := j) (j := i) h
  have ht := prefixDet_isUnit_of_blockTriangular w Mᵀ hmt (Matrix.isUnit_det_transpose M hDet) a
  change IsUnit ((M.toBlock (fun j => w j < a) (fun j => w j < a))ᵀ).det at ht
  rwa [Matrix.det_transpose] at ht

/-- For a lower unitriangular, block-diagonal, upper unitriangular product,
the Schur extraction gives exactly the middle factor. -/
theorem blockSchurDiagonal_mul (w : ι → β) (L T U : (Matrix ι ι R)ˣ)
    (hL : L.val.BlockTriangular (OrderDual.toDual ∘ w))
    (hL₁ : ∀ i j, w i = w j → L.val i j = (1 : Matrix ι ι R) i j)
    (hT : ∀ i j, w i ≠ w j → T.val i j = 0)
    (hU : U.val.BlockTriangular w)
    (hU₁ : ∀ i j, w i = w j → U.val i j = (1 : Matrix ι ι R) i j) :
    blockSchurDiagonal w (L.val * T.val * U.val) = T.val := by
  classical
  ext i j
  simp only [blockSchurDiagonal, Matrix.of_apply]
  by_cases h : w i = w j
  · simp only [dif_pos h]
    let p (l : ι) := w l < w i
    let q (l : ι) := ¬p l
    have hpq (r : Subtype p) (s : Subtype q) : w r.val < w s.val :=
      lt_of_lt_of_le r.prop (le_of_not_gt s.prop)
    have hLp : L.val.toBlock p q = 0 := Matrix.ext fun r s =>
      hL (i := r.val) (j := s.val) (hpq r s)
    have hTp : T.val.toBlock p q = 0 := Matrix.ext fun r s =>
      hT _ _ (ne_of_lt (hpq r s))
    have hTq : T.val.toBlock q p = 0 := Matrix.ext fun r s =>
      hT _ _ (ne_of_gt (hpq s r))
    have hUp : U.val.toBlock q p = 0 := Matrix.ext fun r s =>
      hU (hpq s r)
    have hLdet := prefixDet_isUnit_of_lowerBlockTriangular w L.val hL (Matrix.isUnits_det_units L) (w i)
    have hTdet := prefixDet_isUnit_of_blockTriangular w T.val
      (fun r s hrs => hT r s (ne_of_gt hrs)) (Matrix.isUnits_det_units T) (w i)
    have hUdet := prefixDet_isUnit_of_blockTriangular w U.val hU (Matrix.isUnits_det_units U) (w i)
    let I : Subtype q := ⟨i, lt_irrefl _⟩
    let J : Subtype q := ⟨j, by change ¬w j < w i; rw [← h]; exact lt_irrefl _⟩
    change schurComplementAt (L.val * T.val * U.val) p I J = _
    rw [schurComplementAt_mul _ _ _ p hLp hTp hTq hUp hLdet hTdet hUdet]
    have hRow (s : Subtype q) : L.val.toBlock q q I s = (1 : Matrix (Subtype q) (Subtype q) R) I s := by
      have hs : w i ≤ w s.val := le_of_not_gt s.prop
      rcases hs.eq_or_lt with hEq | hLt
      · rw [Matrix.toBlock_apply, hL₁ _ _ hEq]
        by_cases hs : I = s
        · subst s
          simp [I]
        · rw [Matrix.one_apply_ne hs, Matrix.one_apply_ne (fun e => hs (Subtype.ext e))]
      · rw [Matrix.toBlock_apply, hL (i := i) (j := s.val) hLt, Matrix.one_apply_ne]
        intro hs
        exact (ne_of_lt hLt) (congrArg (fun x : Subtype q => w x.val) hs)
    have hColumn (s : Subtype q) : U.val.toBlock q q s J = (1 : Matrix (Subtype q) (Subtype q) R) s J := by
      have hs : w j ≤ w s.val := h ▸ le_of_not_gt s.prop
      rcases hs.eq_or_lt with hEq | hLt
      · rw [Matrix.toBlock_apply, hU₁ _ _ hEq.symm]
        by_cases hs : s = J
        · subst s
          simp [J]
        · rw [Matrix.one_apply_ne hs, Matrix.one_apply_ne (fun e => hs (Subtype.ext e))]
      · rw [Matrix.toBlock_apply, hU (i := s.val) (j := j) hLt, Matrix.one_apply_ne]
        intro hs
        exact (ne_of_gt hLt) (congrArg (fun x : Subtype q => w x.val) hs)
    let L₀ := L.val.toBlock q q
    let T₀ := T.val.toBlock q q
    let U₀ := U.val.toBlock q q
    change (L₀ * T₀ * U₀) I J = _
    calc
      (L₀ * T₀ * U₀) I J = (L₀ * T₀ * (1 : Matrix (Subtype q) (Subtype q) R)) I J := by
        change (∑ s, (L₀ * T₀) I s * U₀ s J) =
          ∑ s, (L₀ * T₀) I s * (1 : Matrix (Subtype q) (Subtype q) R) s J
        exact Finset.sum_congr rfl fun s _ => congrArg ((L₀ * T₀) I s * ·) (hColumn s)
      _ = (L₀ * T₀) I J := by rw [Matrix.mul_one]
      _ = ((1 : Matrix (Subtype q) (Subtype q) R) * T₀) I J := by
        change (∑ s, L₀ I s * T₀ s J) =
          ∑ s, (1 : Matrix (Subtype q) (Subtype q) R) I s * T₀ s J
        exact Finset.sum_congr rfl fun s _ => congrArg (· * T₀ s J) (hRow s)
      _ = T.val i j := by rw [Matrix.one_mul]; rfl
  · rw [dif_neg h, hT i j h]

end OrderedBlocks

end WideE
