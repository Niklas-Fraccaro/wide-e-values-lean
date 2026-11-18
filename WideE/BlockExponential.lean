import WideE.HopfMatrixExponential
import WideE.BlockSchurDiagonal

/-! Polynomial exponentials in the actual unitriangular block subgroups. -/

noncomputable section

open scoped Matrix Polynomial

namespace WideE

section Blocks

variable {R S ι β : Type*} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq ι] [LinearOrder β]

/-- Block upper triangular with identity on each diagonal block. -/
def BlockUnitriangular (w : ι → β) (M : Matrix ι ι R) : Prop :=
  M.BlockTriangular w ∧ ∀ i j, w i = w j → M i j = (1 : Matrix ι ι R) i j

omit [Fintype ι] in
theorem BlockUnitriangular.one (w : ι → β) : BlockUnitriangular w (1 : Matrix ι ι R) :=
  ⟨Matrix.blockTriangular_one, fun _ _ _ => rfl⟩

theorem BlockUnitriangular.mul {w : ι → β} {M N : Matrix ι ι R}
    (hM : BlockUnitriangular w M) (hN : BlockUnitriangular w N) :
    BlockUnitriangular w (M * N) := by
  refine ⟨hM.1.mul hN.1, fun i j hij => ?_⟩
  trans ((1 : Matrix ι ι R) * (1 : Matrix ι ι R)) i j
  · simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro l _
    rcases lt_trichotomy (w l) (w i) with hl | hl | hl
    · rw [hM.1 hl, Matrix.one_apply_ne (fun e => (ne_of_lt hl) (congrArg w e.symm)), zero_mul, zero_mul]
    · rw [hM.2 _ _ hl.symm, hN.2 _ _ (hl.trans hij)]
    · have hlj : w j < w l := hij ▸ hl
      rw [hN.1 hlj, Matrix.one_apply_ne (fun e => (ne_of_lt hlj) (congrArg w e.symm)), mul_zero, mul_zero]
  · rw [Matrix.one_mul]

theorem BlockUnitriangular.map {w : ι → β} {M : Matrix ι ι R} (hM : BlockUnitriangular w M)
    (f : R →+* S) : BlockUnitriangular w (M.map f) := by
  refine ⟨hM.1.map f, fun i j hij => ?_⟩
  change f (M i j) = _
  rw [hM.2 i j hij]
  exact congrArg (fun A : Matrix ι ι S => A i j) (map_one f.mapMatrix)

/-- Strict block upper triangularity forces nilpotence, including when the
ordering type is infinite and only finitely many weights occur. -/
theorem isNilpotent_of_strictBlockTriangular (w : ι → β) (N : Matrix ι ι R)
    (hN : ∀ i j, ¬w i < w j → N i j = 0) : IsNilpotent N := by
  let s (i : ι) := Finset.univ.filter fun j => w i < w j
  have hS (i j : ι) (h : w i < w j) : (s j).card < (s i).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro l hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.trans (Finset.mem_filter.mp hl).2⟩
    · intro hEq
      have hj : j ∈ s i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      have hj' : j ∈ s j := hEq.symm ▸ hj
      have hc : w j < w j := (Finset.mem_filter.mp hj').2
      exact (lt_irrefl (w j)) hc
  have hPower (n : ℕ) : ∀ i j, (s i).card < n → (N ^ n) i j = 0 := by
    induction n with
    | zero => exact fun _ _ h => (Nat.not_lt_zero _ h).elim
    | succ n ih =>
      intro i j hi
      rw [pow_succ', Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases h : w i < w l
      · rw [ih l j ((hS i l h).trans_le (Nat.lt_succ_iff.mp hi)), mul_zero]
      · rw [hN i l h, zero_mul]
  refine ⟨Fintype.card ι, Matrix.ext fun i j => hPower _ i j ?_⟩
  rw [← Finset.card_univ]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, fun hEq => ?_⟩
  have hi : i ∈ s i := hEq.symm ▸ Finset.mem_univ i
  have hc : w i < w i := (Finset.mem_filter.mp hi).2
  exact (lt_irrefl (w i)) hc

private theorem strictBlockTriangular_pow_succ (w : ι → β) (N : Matrix ι ι R)
    (hN : ∀ i j, ¬w i < w j → N i j = 0) (n : ℕ) :
    ∀ i j, ¬w i < w j → (N ^ (n + 1)) i j = 0 := by
  have hTri : N.BlockTriangular w := fun i j hij => hN i j (not_lt_of_gt hij)
  have hPow : ∀ m : ℕ, (N ^ m).BlockTriangular w := by
    intro m
    induction m with
    | zero => simpa only [pow_zero] using Matrix.blockTriangular_one
    | succ m hm => simpa only [pow_succ] using hm.mul hTri
  intro i j hij
  rw [pow_succ, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases h : w l < w i
  · rw [hPow n h, zero_mul]
  · rw [hN l j (fun hl => hij ((le_of_not_gt h).trans_lt hl)), mul_zero]

end Blocks

section Exponential

variable {k ι β : Type*} [Field k] [CharZero k] [Fintype ι] [DecidableEq ι] [LinearOrder β]

/-- The polynomial exponential of a strict block-triangular tangent
lies in the corresponding block-unitriangular subgroup. -/
theorem polynomialMatrixExponential_blockUnitriangular (w : ι → β) (N : Matrix ι ι k)
    (hN : ∀ i j, ¬w i < w j → N i j = 0) :
    BlockUnitriangular w (polynomialMatrixExponential N) := by
  let M : Matrix ι ι k[X] := (Polynomial.X : k[X]) • (algebraMap k k[X]).mapMatrix N
  have hM (i j : ι) (h : ¬w i < w j) : M i j = 0 := by
    change Polynomial.X * algebraMap k k[X] (N i j) = 0
    rw [hN i j h, map_zero, mul_zero]
  obtain ⟨n, hn⟩ := isNilpotent_of_strictBlockTriangular w M hM
  have hn' : M ^ (n + 1) = 0 := by rw [pow_succ, hn, Matrix.zero_mul]
  have hEval (i j : ι) (hij : ¬w i < w j) :
      polynomialMatrixExponential N i j = (1 : Matrix ι ι k[X]) i j := by
    change (IsNilpotent.exp M) i j = _
    rw [IsNilpotent.exp_eq_sum hn', Matrix.sum_apply]
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.zero_lt_succ n))]
    · simp
    · intro m _ hm
      obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
      rw [Matrix.smul_apply, strictBlockTriangular_pow_succ w M hM _ i j hij, smul_zero]
  refine ⟨fun i j hij => ?_, fun i j hij => hEval i j (by rw [hij]; exact lt_irrefl _)⟩
  rw [hEval i j (not_lt_of_gt hij), Matrix.one_apply_ne]
  exact fun e => (ne_of_lt hij) (congrArg w e.symm)

end Exponential

end WideE
