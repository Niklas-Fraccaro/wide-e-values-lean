import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Nonzero-weight elements in a finite-dimensional associative algebra are nilpotent. -/

noncomputable section

namespace WideE

variable {k A : Type*} [Field k] [CharZero k] [Ring A] [Algebra k A]

/-- A nonzero adjoint weight in a finite-dimensional associative algebra
forces nilpotence, since all nonzero powers have distinct adjoint weights. -/
theorem isNilpotent_of_lie_eq_smul_ne_zero [FiniteDimensional k A]
    (a b : A) (c : k) (hc : c ≠ 0) (h : ⁅a, b⁆ = c • b) : IsNilpotent b := by
  have hLeibniz (x y : A) : ⁅a, x * y⁆ = ⁅a, x⁆ * y + x * ⁅a, y⁆ := by
    simp only [LieRing.of_associative_ring_bracket, sub_mul, mul_sub, mul_assoc]
    abel
  have hPower (n : ℕ) : ⁅a, b ^ n⁆ = ((n : k) * c) • b ^ n := by
    induction n with
    | zero => simp only [pow_zero, LieRing.of_associative_ring_bracket, mul_one, one_mul,
        sub_self, Nat.cast_zero, zero_mul, zero_smul]
    | succ n ih =>
      rw [pow_succ, hLeibniz, ih, h, smul_mul_assoc, mul_smul_comm, ← add_smul,
        Nat.cast_succ, add_mul, one_mul]
  by_contra hNil
  let μ (n : ℕ) : k := (n : k) * c
  have hμ : Function.Injective μ := by
    intro n m hEq
    exact Nat.cast_injective (mul_right_cancel₀ hc hEq)
  let D : Module.End k A := (LieAlgebra.ad k A) a
  have hEig (n : ℕ) : D.HasEigenvector (μ n) (b ^ n) := by
    refine Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · exact hPower n
    · intro hz
      exact hNil ⟨n, hz⟩
  have hLI := D.eigenvectors_linearIndependent' μ hμ (fun n => b ^ n) hEig
  letI : Finite ℕ := hLI.finite_of_isNoetherian
  exact not_finite ℕ

end WideE
