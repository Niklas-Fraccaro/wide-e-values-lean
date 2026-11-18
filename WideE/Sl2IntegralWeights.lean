import WideE.AdjointWeightNilpotence
import Mathlib.Algebra.Lie.Sl2

/-! The eigenvalues of the Cartan element of a Sl₂ triple are integral. -/

noncomputable section

open LieModule Module

namespace WideE

variable {k L V : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
  [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V] [FiniteDimensional k V]

/-- Raising a nonzero weight vector to the top of its string reduces integrality
to mathlib's highest-weight theorem. -/
theorem exists_int_of_sl2Cartan_eigenvector {h e f : L} (t : IsSl2Triple h e f)
    {v : V} {a : k} (hv : v ≠ 0) (ha : ⁅h, v⁆ = a • v) : ∃ n : ℤ, a = n := by
  let ρ := LieModule.toEnd k L V
  let ψ (r : ℕ) := (ρ e ^ r) v
  have he : IsNilpotent (ρ e) := by
    apply isNilpotent_of_lie_eq_smul_ne_zero (ρ h) (ρ e) (2 : k) (by norm_num)
    rw [← LieHom.map_lie, t.lie_h_e_smul k, LieHom.map_smul]
  have hExists : ∃ r : ℕ, ψ r = 0 := by
    obtain ⟨r, hr⟩ := he
    exact ⟨r, by rw [show ψ r = (ρ e ^ r) v from rfl, hr, LinearMap.zero_apply]⟩
  have hz : ψ 0 ≠ 0 := by simpa [ψ] using hv
  obtain ⟨r, hr, hr'⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists hz hExists
  have hWeight (m : ℕ) : ⁅h, ψ m⁆ = (a + 2 * m) • ψ m := by
    induction m with
    | zero => simpa [ψ] using ha
    | succ m ih =>
      have hψ : ψ (m + 1) = ⁅e, ψ m⁆ := by
        simp only [ψ, pow_succ', Module.End.mul_apply, ρ, toEnd_apply_apply]
      rw [hψ, leibniz_lie h, t.lie_h_e_smul k, smul_lie, ih, lie_smul, ← add_smul, Nat.cast_succ]
      congr 1
      ring
  have hRaise : ⁅e, ψ r⁆ = 0 := by
    change (ρ e) (ψ r) = 0
    rw [show (ρ e) (ψ r) = ψ (r + 1) by simp only [ψ, pow_succ', Module.End.mul_apply], hr']
  letI : NoZeroSMulDivisors ℤ V := NoZeroSMulDivisors.int_of_charZero k V
  have hPrim : t.HasPrimitiveVectorWith (ψ r) (a + 2 * r) := ⟨hr, hWeight r, hRaise⟩
  obtain ⟨m, hm⟩ := hPrim.exists_nat
  refine ⟨(m : ℤ) - 2 * (r : ℤ), ?_⟩
  rw [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_natCast, ← hm]
  ring

end WideE
