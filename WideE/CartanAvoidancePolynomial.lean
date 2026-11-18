import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fintype.Prod

/-! Simultaneous avoidance of vanishing roots and collisions between principal blocks. -/

noncomputable section

namespace WideE

variable {k η ι ξ : Type*} [Field k] [Fintype η] [Fintype ι] [Fintype ξ]

private def coordinateLinearPolynomial (l : η → k) : MvPolynomial η k :=
  ∑ i, MvPolynomial.C (l i) * MvPolynomial.X i

private theorem aeval_coordinateLinearPolynomial {A : Type*} [CommRing A] [Algebra k A]
    (c : η → A) (v : η → k) : MvPolynomial.aeval c (coordinateLinearPolynomial v) =
      ∑ i, c i * algebraMap k A (v i) := by
  simp only [coordinateLinearPolynomial, map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

universe uΩ

/-- A single polynomial expresses nonvanishing of the roots and block differences.
The principal Cartan vector certifies that the polynomial is nonzero. -/
theorem exists_cartanAvoidancePolynomial
    (r : ξ → η → k) (a : η → ι → k) (w : ι → k) (c₀ : η → k)
    (hr : ∀ α, ∑ s, c₀ s * r α s ≠ 0) (ha : ∀ i, ∑ s, c₀ s * a s i = w i) :
    ∃ d : MvPolynomial η k, d ≠ 0 ∧ ∀ (Ω : Type uΩ) [Field Ω] [Algebra k Ω] (c : η → Ω),
      MvPolynomial.aeval c d ≠ 0 →
        (∀ α, ∑ s, c s * algebraMap k Ω (r α s) ≠ 0) ∧
        (∀ i j, w i ≠ w j → ∑ s, c s * algebraMap k Ω (a s j) ≠ ∑ s, c s * algebraMap k Ω (a s i)) := by
  classical
  let I := {p : ι × ι // w p.1 ≠ w p.2}
  let l (i : ι) := coordinateLinearPolynomial (fun s => a s i)
  let d : MvPolynomial η k :=
    (∏ α, coordinateLinearPolynomial (r α)) * ∏ ij : I, (l ij.val.2 - l ij.val.1)
  have h₀ : MvPolynomial.aeval c₀ d ≠ 0 := by
    have hId (x : k) : algebraMap k k x = x := rfl
    simp only [d, l, map_mul, map_prod, map_sub, aeval_coordinateLinearPolynomial, hId]
    apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr fun α _ => hr α
    · refine Finset.prod_ne_zero_iff.mpr fun ij _ => ?_
      rw [ha, ha]
      exact sub_ne_zero.mpr ij.property.symm
  refine ⟨d, fun h => h₀ (by rw [h, map_zero]), ?_⟩
  intro Ω _ _ c hc
  simp only [d, l, map_mul, map_prod, map_sub, aeval_coordinateLinearPolynomial] at hc
  obtain ⟨hR, hA⟩ := mul_ne_zero_iff.mp hc
  refine ⟨fun α => Finset.prod_ne_zero_iff.mp hR α (Finset.mem_univ _), fun i j hij => ?_⟩
  exact sub_ne_zero.mp (Finset.prod_ne_zero_iff.mp hA (⟨(i, j), hij⟩ : I) (Finset.mem_univ _))

end WideE
