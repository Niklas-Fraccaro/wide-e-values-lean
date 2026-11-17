import StrictEFunctionDefinitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The wide Siegel E-function and E-value predicates. -/

noncomputable section

namespace WideE

abbrev AlgebraicComplex := StrictEUnit.AlgebraicComplex

/-- The same number field contains every coefficient of the chosen series. -/
def HasFixedCoefficientField (a : ℕ → AlgebraicComplex) : Prop :=
  ∃ K : IntermediateField ℚ AlgebraicComplex, FiniteDimensional ℚ K ∧ ∀ n, a n ∈ K

/-- Subfactorial bounds on conjugates and positive common denominators, for every
positive real exponent. The common constant can be enlarged to cover both bounds. -/
def HasWideEArithmetic (a : ℕ → AlgebraicComplex) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ σ : AlgebraicComplex →ₐ[ℚ] ℂ, ∀ n : ℕ,
        ‖σ (a n)‖ ≤ C * (n.factorial : ℝ) ^ ε) ∧
      ∃ d : ℕ → ℕ, (∀ n, 0 < d n) ∧
        (∀ n, (d n : ℝ) ≤ C * (n.factorial : ℝ) ^ ε) ∧
        ∀ n j : ℕ, j ≤ n → IsIntegral ℤ ((d n : ℂ) * (a j : ℂ))

/-- The actual factorial-normalized expansion holds at every complex point. -/
def HasFactorialExpansion (f : ℂ → ℂ) (a : ℕ → AlgebraicComplex) : Prop :=
  ∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z)

/-- An actual entire function and its defining factorial-normalized series. The
polynomial ODE records the rational ODE after clearing its denominators. -/
def IsWideEFunction (f : ℂ → ℂ) : Prop :=
  ∃ a : ℕ → AlgebraicComplex,
    Differentiable ℂ f ∧ HasFactorialExpansion f a ∧
    StrictEUnit.HasAlgebraicPolynomialODE f ∧ HasWideEArithmetic a ∧
    HasFixedCoefficientField a

/-- Values in the normalization used in the paper. -/
def IsWideEValue (ξ : ℂ) : Prop :=
  ∃ f : ℂ → ℂ, IsWideEFunction f ∧ f 1 = ξ

/-- Numerical unit membership before bundling the value ring. -/
def IsWideEValueUnit (ξ : ℂ) : Prop :=
  ξ ≠ 0 ∧ IsWideEValue ξ ∧ IsWideEValue ξ⁻¹

def IsAlgebraicScalarExp (ξ : ℂ) : Prop :=
  ∃ α β : ℂ, IsAlgebraic ℚ α ∧ α ≠ 0 ∧ IsAlgebraic ℚ β ∧ ξ = α * Complex.exp β

theorem HasWideEArithmetic.chosen_bound {a : ℕ → AlgebraicComplex}
    (ha : HasWideEArithmetic a) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n, ‖(a n : ℂ)‖ ≤ C * (n.factorial : ℝ) ^ ε := by
  obtain ⟨C, hC, hconj, _⟩ := ha ε hε
  exact ⟨C, hC, hconj (algebraicClosure ℚ ℂ).val⟩

theorem HasWideEArithmetic.numberField_conjugates {a : ℕ → AlgebraicComplex}
    (ha : HasWideEArithmetic a) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (K : IntermediateField ℚ AlgebraicComplex) (σ : K →ₐ[ℚ] ℂ)
        (n : ℕ) (x : K), (x : AlgebraicComplex) = a n →
        ‖σ x‖ ≤ C * (n.factorial : ℝ) ^ ε := by
  obtain ⟨C, hC, hconj, _⟩ := ha ε hε
  refine ⟨C, hC, ?_⟩
  intro K σ n x hx
  obtain ⟨τ, hτ⟩ := StrictEUnit.algebraicComplex_embedding_extends K σ
  rw [← hτ x, hx]
  exact hconj τ n

theorem IsWideEFunction.differentiable {f : ℂ → ℂ} (hf : IsWideEFunction f) :
    Differentiable ℂ f := by
  obtain ⟨_, hd, _⟩ := hf
  exact hd

theorem IsWideEFunction.zero_isAlgebraic {f : ℂ → ℂ} (hf : IsWideEFunction f) :
    IsAlgebraic ℚ (f 0) := by
  obtain ⟨a, _, hs, _⟩ := hf
  have hzero : f 0 = (a 0 : ℂ) := by
    rw [← (hs 0).tsum_eq, tsum_eq_single 0]
    · simp
    · intro n hn
      simp [zero_pow hn]
  rw [hzero]
  exact mem_algebraicClosure_iff.mp (a 0).property

end WideE
