import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Topology.Homotopy.Lifting

/-! Killing the monodromy of a finite cover of the complex punctured line. -/

open scoped Topology
open Function.Periodic Topology

noncomputable section

namespace WideE

abbrev ComplexPuncturedLine := {z : ℂ // z ≠ 0}

/-- The base point of the complex punctured line. -/
def puncturedOne : ComplexPuncturedLine := ⟨1, one_ne_zero⟩

/-- The exponential parametrization with period `h`, taking values off zero. -/
def puncturedExp (h : ℝ) : C(ℂ, ComplexPuncturedLine) :=
  ⟨fun w => ⟨qParam h w, Complex.exp_ne_zero _⟩,
    (Complex.continuous_exp.comp (by fun_prop)).subtype_mk _⟩

@[simp] theorem puncturedExp_coe (h : ℝ) (w : ℂ) :
    (puncturedExp h w : ℂ) = qParam h w := rfl

private theorem periodic_puncturedExp : Function.Periodic (puncturedExp 1) (1 : ℂ) := by
  intro w
  apply Subtype.ext
  simp only [puncturedExp_coe, qParam, Complex.ofReal_one, div_one, mul_add, mul_one,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

private theorem puncturedExp_one_nat (n : ℕ) : puncturedExp 1 (n : ℂ) = puncturedOne := by
  have h := periodic_puncturedExp.nat_mul n 0
  simpa [qParam, puncturedOne, puncturedExp] using h

private theorem puncturedExp_power (q : ℕ) (hq : 0 < q) (w : ℂ) :
    (puncturedExp (q : ℝ) w : ℂ) ^ q = (puncturedExp 1 w : ℂ) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [puncturedExp_coe, qParam, ← Complex.exp_nat_mul, Complex.ofReal_natCast,
    Complex.ofReal_one, div_one]
  congr 1
  rw [mul_comm, div_mul_cancel₀ _ hq']

/-- The lift of the exponential map through a finite-fiber covering becomes
periodic after an integral multiple of one turn. -/
theorem exists_periodic_puncturedExp_lift {E : Type*} [TopologicalSpace E]
    {p : E → ComplexPuncturedLine} (hp : IsCoveringMap p)
    [Finite (p ⁻¹' {puncturedOne} : Set E)] (e : E) (he : p e = puncturedOne) :
    ∃ q : ℕ, 0 < q ∧ ∃ f : C(ℂ, E), f 0 = e ∧ p ∘ f = puncturedExp 1 ∧
      Function.Periodic f (q : ℂ) := by
  obtain ⟨f, ⟨hf₀, hf⟩, _⟩ := hp.existsUnique_continuousMap_lifts (puncturedExp 1) 0 e
    (he.trans (by simpa using (puncturedExp_one_nat 0).symm))
  let orbit (n : ℕ) : (p ⁻¹' {puncturedOne} : Set E) :=
    ⟨f (n : ℂ), (congrFun hf (n : ℂ)).trans (puncturedExp_one_nat n)⟩
  have hcollision : ∃ a b : ℕ, a < b ∧ f (a : ℂ) = f (b : ℂ) := by
    obtain ⟨a, b, heq, hne⟩ : ∃ a b : ℕ, orbit a = orbit b ∧ a ≠ b := by
      simpa only [Function.Injective, not_forall, exists_prop] using
        not_injective_infinite_finite orbit
    exact (lt_or_gt_of_ne hne).elim
      (fun hab => ⟨a, b, hab, congrArg Subtype.val heq⟩)
      (fun hba => ⟨b, a, hba, congrArg Subtype.val heq.symm⟩)
  obtain ⟨a, b, hab, heq⟩ := hcollision
  have hshift (n : ℕ) (w : ℂ) : p (f (w + (n : ℂ))) = puncturedExp 1 w := by
    have hn := periodic_puncturedExp.nat_mul n w
    simpa using (congrFun hf (w + (n : ℂ))).trans (by simpa using hn)
  have hsame : (fun w : ℂ => f (w + (a : ℂ))) = fun w : ℂ => f (w + (b : ℂ)) :=
    hp.eq_of_comp_eq (f.continuous.comp (continuous_id.add continuous_const))
      (f.continuous.comp (continuous_id.add continuous_const))
      (funext fun w => (hshift a w).trans (hshift b w).symm) 0 (by simpa using heq)
  refine ⟨b - a, Nat.sub_pos_of_lt hab, f, hf₀, hf, ?_⟩
  intro w
  have h := congrFun hsame (w - (a : ℂ))
  simp only [sub_add_cancel] at h
  rw [Nat.cast_sub hab.le]
  simpa only [sub_add_eq_add_sub, add_sub_assoc] using h.symm

/-- A power map admits a continuous lift through any covering with finite
fiber at one, starting at an arbitrary point of that fiber. -/
theorem exists_puncturedPower_lift {E : Type*} [TopologicalSpace E]
    {p : E → ComplexPuncturedLine} (hp : IsCoveringMap p)
    [Finite (p ⁻¹' {puncturedOne} : Set E)] (e : E) (he : p e = puncturedOne) :
    ∃ q : ℕ, 0 < q ∧ ∃ g : C(ComplexPuncturedLine, E), g puncturedOne = e ∧
      ∀ z, (p (g z) : ℂ) = (z : ℂ) ^ q := by
  obtain ⟨q, hq, f, hf₀, hf, hperiod⟩ := exists_periodic_puncturedExp_lift hp e he
  have hq₀ : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  let g (z : ComplexPuncturedLine) := f (invQParam (q : ℝ) z)
  have hcomp (w : ℂ) : g (puncturedExp (q : ℝ) w) = f w := by
    obtain ⟨a, ha⟩ := qParam_left_inv_mod_period hq₀ w
    change f (invQParam (q : ℝ) (qParam (q : ℝ) w)) = f w
    rw [ha]
    simpa using hperiod.int_mul a w
  have hopen : IsOpenMap (puncturedExp (q : ℝ) : ℂ → ComplexPuncturedLine) := by
    intro U hU
    rw [isOpen_induced_iff]
    refine ⟨qParam (q : ℝ) '' U, ?_, ?_⟩
    · have hc : (2 * (Real.pi : ℂ) * Complex.I / (q : ℂ)) ≠ 0 :=
        div_ne_zero Complex.two_pi_I_ne_zero (by exact_mod_cast hq.ne')
      let scale := Homeomorph.mulLeft₀ (2 * (Real.pi : ℂ) * Complex.I / (q : ℂ)) hc
      have heq : qParam (q : ℝ) = Complex.exp ∘ scale := by
        funext w
        simp [qParam, scale, div_mul_eq_mul_div]
      rw [heq]
      exact (Complex.isOpenMap_exp.comp scale.isOpenMap) U hU
    · ext z
      simp only [Set.mem_preimage, Set.mem_image]
      exact ⟨fun ⟨w, hw, hwz⟩ => ⟨w, hw, Subtype.ext hwz⟩,
        fun ⟨w, hw, hwz⟩ => ⟨w, hw, congrArg Subtype.val hwz⟩⟩
  have hsurj : Function.Surjective (puncturedExp (q : ℝ)) :=
    fun z => ⟨invQParam (q : ℝ) z, Subtype.ext (qParam_right_inv hq₀ z.property)⟩
  have hcont : Continuous g := (hopen.isQuotientMap (puncturedExp (q : ℝ)).continuous hsurj)
    |>.continuous_iff.mpr (show Continuous (g ∘ puncturedExp (q : ℝ)) from
      (funext hcomp : g ∘ puncturedExp (q : ℝ) = f) ▸ f.continuous)
  refine ⟨q, hq, ⟨g, hcont⟩, ?_, ?_⟩
  · change f (invQParam (q : ℝ) 1) = e
    simpa [invQParam, Complex.log_one] using hf₀
  · intro z
    obtain ⟨w, rfl⟩ := hsurj z
    change (p (g (puncturedExp (q : ℝ) w)) : ℂ) = _
    rw [hcomp, puncturedExp_power q hq]
    exact congrArg Subtype.val (congrFun hf w)

end WideE
