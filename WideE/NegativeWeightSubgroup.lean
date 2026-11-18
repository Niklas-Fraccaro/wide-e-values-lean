import WideE.KostantWeightAlgebra

/-! Units congruent to the identity in the strictly negative weight filtration. -/

noncomputable section

namespace WideE

variable {k R : Type*} [Field k] [CharZero k] [Ring R] [Algebra k R]
  [FiniteDimensional k R]

local notation "B" => kostantWeightFiltration (k := k)

omit [CharZero k] [FiniteDimensional k R] in
private theorem mul_sub_one_mem_negativeFiltration (a : R) {x y : R}
    (hx : x - 1 ∈ B a 1) (hy : y - 1 ∈ B a 1) : x * y - 1 ∈ B a 1 := by
  let u := x - 1
  let v := y - 1
  have hu : x = 1 + u := by dsimp [u]; abel
  have hv : y = 1 + v := by dsimp [v]; abel
  have hp : u * v ∈ B a 1 := kostantWeightFiltration_antitone a (by decide : 1 ≤ 1 + 1)
    (mul_mem_kostantWeightFiltration a hx hy)
  have hSum : u + v + u * v ∈ B a 1 := (B a 1).add_mem ((B a 1).add_mem hx hy) hp
  rw [hu, hv, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one]
  convert hSum using 1
  abel

private theorem inv_sub_one_mem_negativeFiltration (a : R) (x : Rˣ)
    (hx : (x : R) - 1 ∈ B a 1) : x.inv - 1 ∈ B a 1 := by
  let u := (x : R) - 1
  have hu : -u ∈ B a 1 := (B a 1).neg_mem hx
  obtain ⟨n, hn⟩ := isNilpotent_of_mem_kostantWeightFiltration a (by decide : 0 < 1) hu
  have hn' : (-u) ^ (n + 1) = 0 := pow_eq_zero_of_le (Nat.le_succ n) hn
  have hx' : (x : R) = 1 - (-u) := by dsimp [u]; abel
  have hSum := geom_sum_mul_neg (-u) (n + 1)
  rw [← hx', hn', sub_zero] at hSum
  have hInv := congrArg (fun v : R => v * x.inv) hSum
  change _ * (x : R) * x.inv = 1 * x.inv at hInv
  rw [mul_assoc, x.val_inv, mul_one, one_mul] at hInv
  rw [← hInv, Finset.sum_range_succ', pow_zero, add_sub_cancel_right]
  apply Submodule.sum_mem
  intro i hi
  exact kostantWeightFiltration_antitone a (by omega : 1 ≤ (i + 1) * 1)
    (pow_mem_kostantWeightFiltration a hu (i + 1))

/-- The group of units in (1+B_1) for the adjoint filtration. -/
def negativeWeightUnitSubgroup (a : R) : Subgroup Rˣ where
  carrier := {x | (x : R) - 1 ∈ B a 1}
  one_mem' := by
    change (1 : R) - 1 ∈ B a 1
    rw [sub_self]
    exact zero_mem _
  mul_mem' {x y} hx hy := mul_sub_one_mem_negativeFiltration a hx hy
  inv_mem' {x} hx := inv_sub_one_mem_negativeFiltration a x hx

variable [Algebra ℚ R] [IsScalarTower ℚ k R]

/-- The exponential of a strictly negative element is congruent to the
identity in the same filtration stage. -/
theorem exp_sub_one_mem_kostantWeightFiltration (a : R) {r : ℕ} {x : R}
    (hr : 0 < r) (hx : x ∈ B a r) : IsNilpotent.exp x - 1 ∈ B a r := by
  obtain ⟨n, hn⟩ := isNilpotent_of_mem_kostantWeightFiltration a hr hx
  have hN : x ^ (n + 1) = 0 := pow_eq_zero_of_le (Nat.le_succ n) hn
  rw [IsNilpotent.exp_eq_sum hN, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero, add_sub_cancel_right]
  apply Submodule.sum_mem
  intro i hi
  rw [← IsScalarTower.algebraMap_smul k]
  apply Submodule.smul_mem
  have hir : r ≤ (i + 1) * r := by
    simpa using Nat.mul_le_mul_right r (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero i))
  exact kostantWeightFiltration_antitone a hir (pow_mem_kostantWeightFiltration a hx (i + 1))

end WideE
