import WideE.Closure
import Stage14StrictERingClosure

/-! The actual wide E-value subring and the explicitly constructed inclusion
of algebraic scalar exponentials in its unit group. -/

noncomputable section

namespace WideE

open StrictEUnit

theorem IsWideEValue.of_algebraic_argument {f : ℂ → ℂ} (hf : IsWideEFunction f)
    (α : AlgebraicComplex) : IsWideEValue (f α) :=
  ⟨_, hf.rescale α, by simp⟩

theorem isWideEValue_iff_algebraic_argument (ξ : ℂ) :
    IsWideEValue ξ ↔
      ∃ f : ℂ → ℂ, IsWideEFunction f ∧ ∃ α : AlgebraicComplex, f α = ξ := by
  constructor
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, 1, by simpa only [IntermediateField.coe_one] using h⟩
  · rintro ⟨f, hf, α, rfl⟩
    exact IsWideEValue.of_algebraic_argument hf α

theorem algebraic_isWideEValue (α : AlgebraicComplex) : IsWideEValue (α : ℂ) :=
  ⟨_, isWideEFunction_const α, rfl⟩

theorem IsWideEValue.add {ξ η : ℂ} (hξ : IsWideEValue ξ) (hη : IsWideEValue η) :
    IsWideEValue (ξ + η) := by
  obtain ⟨f, hf, rfl⟩ := hξ
  obtain ⟨g, hg, rfl⟩ := hη
  exact ⟨_, hf.add hg, rfl⟩

theorem IsWideEValue.mul {ξ η : ℂ} (hξ : IsWideEValue ξ) (hη : IsWideEValue η) :
    IsWideEValue (ξ * η) := by
  obtain ⟨f, hf, rfl⟩ := hξ
  obtain ⟨g, hg, rfl⟩ := hη
  exact ⟨_, hf.mul hg, rfl⟩

theorem IsWideEValue.neg {ξ : ℂ} (hξ : IsWideEValue ξ) : IsWideEValue (-ξ) := by
  obtain ⟨f, hf, rfl⟩ := hξ
  exact ⟨_, hf.neg, rfl⟩

/-- The actual class of wide E-values, with its proven closure operations. -/
def valueSubring : Subring ℂ where
  carrier := {ξ | IsWideEValue ξ}
  zero_mem' := by simpa only [IntermediateField.coe_zero] using algebraic_isWideEValue 0
  one_mem' := by simpa only [IntermediateField.coe_one] using algebraic_isWideEValue 1
  add_mem' := IsWideEValue.add
  mul_mem' := IsWideEValue.mul
  neg_mem' := IsWideEValue.neg

@[simp] theorem mem_valueSubring (ξ : ℂ) :
    ξ ∈ valueSubring ↔ IsWideEValue ξ := Iff.rfl

theorem wideEValueUnit_iff_exists_unit (ξ : ℂ) :
    IsWideEValueUnit ξ ↔ ∃ v : valueSubringˣ, ((v : valueSubring) : ℂ) = ξ := by
  constructor
  · rintro ⟨hne, hξ, hi⟩
    refine ⟨{ val := ⟨ξ, hξ⟩, inv := ⟨ξ⁻¹, hi⟩
              val_inv := Subtype.ext (mul_inv_cancel₀ hne)
              inv_val := Subtype.ext (inv_mul_cancel₀ hne) }, rfl⟩
  · rintro ⟨v, rfl⟩
    have hne : ((v : valueSubring) : ℂ) ≠ 0 :=
      (Units.map valueSubring.subtype.toMonoidHom v).ne_zero
    have hinv : (((v⁻¹ : valueSubringˣ) : valueSubring) : ℂ) =
        ((v : valueSubring) : ℂ)⁻¹ :=
      eq_inv_of_mul_eq_one_left (congrArg (fun x : valueSubring => (x : ℂ)) v.inv_val)
    refine ⟨hne, (v : valueSubring).property, ?_⟩
    rw [← hinv]
    exact ((v⁻¹ : valueSubringˣ) : valueSubring).property

theorem wideEValueUnit_iff_isUnit (u : valueSubring) :
    IsWideEValueUnit (u : ℂ) ↔ IsUnit u := by
  rw [wideEValueUnit_iff_exists_unit]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, Subtype.ext hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, congrArg (fun x : valueSubring => (x : ℂ)) hv⟩

theorem isWideEValue_of_strict {ξ : ℂ} (hξ : IsStrictEValue ξ) : IsWideEValue ξ := by
  obtain ⟨f, hf, h⟩ := (strictEValue_iff_at_one ξ).mp hξ
  exact ⟨f, isWideEFunction_of_strict hf, h⟩

theorem isWideEValueUnit_of_strict {ξ : ℂ} (hξ : IsStrictEValueUnit ξ) :
    IsWideEValueUnit ξ :=
  ⟨hξ.1, isWideEValue_of_strict hξ.2.1, isWideEValue_of_strict hξ.2.2⟩

/-- The direct inclusion from §10, proved with actual wide representatives
of the number and its reciprocal. -/
theorem algebraic_scalar_exp_isWideEValueUnit {ξ : ℂ} (hξ : IsAlgebraicScalarExp ξ) :
    IsWideEValueUnit ξ :=
  isWideEValueUnit_of_strict (algebraic_exponential_reverse_inclusion hξ)

end WideE
