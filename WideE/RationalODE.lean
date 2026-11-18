import WideE.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Topology.Algebra.Module.Cardinality

/-! Clearing rational coefficients of a homogeneous differential equation for an entire function. -/

open scoped BigOperators

noncomputable section

namespace WideE

local notation "k" => AlgebraicComplex
local notation "incl" => AlgHom.toRingHom (IntermediateField.val (algebraicClosure ℚ ℂ))

/-- A nonzero homogeneous linear differential equation over the algebraic
rational functions, at every point where all its reduced denominators are nonzero. -/
def HasAlgebraicRationalODE (f : ℂ → ℂ) : Prop :=
  ∃ m : ℕ, ∃ r : Fin (m + 1) → RatFunc k,
    (∃ i, r i ≠ 0) ∧
    ∀ z : ℂ, (∀ i, (r i).denom.eval₂ incl z ≠ 0) →
      ∑ i, RatFunc.eval incl z (r i) * iteratedDeriv i.val f z = 0

/-- Clearing the reduced denominators gives the polynomial equation on all
of the complex plane by continuity. -/
theorem hasAlgebraicRationalODE_iff_polynomialODE {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) :
    HasAlgebraicRationalODE f ↔ StrictEUnit.HasAlgebraicPolynomialODE f := by
  classical
  constructor
  · rintro ⟨m, r, ⟨i, hi⟩, hr⟩
    let d (j : Fin (m + 1)) := (r j).denom
    let D := ∏ j, d j
    let q (j : Fin (m + 1)) := ∏ l ∈ Finset.univ.erase j, d l
    let p (j : Fin (m + 1)) := (r j).num * q j
    have hq (j : Fin (m + 1)) : q j * d j = D :=
      Finset.prod_erase_mul _ d (Finset.mem_univ j)
    have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => (r j).denom_ne_zero)
    have hqi : q i ≠ 0 := by
      intro h
      exact hD (by rw [← hq i, h, zero_mul])
    refine ⟨m, p, ⟨i, mul_ne_zero (RatFunc.num_ne_zero hi) hqi⟩, ?_⟩
    let e (z : ℂ) : Polynomial k →+* ℂ := Polynomial.eval₂RingHom incl z
    have hdense : Dense {z : ℂ | D.eval₂ incl z ≠ 0} := by
      have hmap : D.map incl ≠ 0 := (Polynomial.map_ne_zero_iff (incl).injective).mpr hD
      simpa only [Set.compl_setOf, Polynomial.IsRoot, Polynomial.eval_map] using
        (Polynomial.finite_setOf_isRoot hmap).countable.dense_compl ℂ
    let F (z : ℂ) := ∑ j, (p j).eval₂ incl z * iteratedDeriv j.val f z
    have hF : Continuous F := continuous_finset_sum _ (fun j _ =>
      ((p j).continuous_eval₂ incl).mul
        ((hf.contDiff (n := ⊤)).continuous_iteratedDeriv j.val le_top))
    have hOn : Set.EqOn F (fun _ => 0) {z : ℂ | D.eval₂ incl z ≠ 0} := by
      intro z hz
      have hd (j : Fin (m + 1)) : e z (d j) ≠ 0 := by
        have hprod : (∏ j, e z (d j)) ≠ 0 := by
          change e z (∏ j, d j) ≠ 0 at hz
          rwa [map_prod] at hz
        exact Finset.prod_ne_zero_iff.mp hprod j (Finset.mem_univ j)
      have hEval (j : Fin (m + 1)) : (p j).eval₂ incl z = e z D * RatFunc.eval incl z (r j) := by
        change e z ((r j).num * q j) = e z D * (e z (r j).num / e z (d j))
        rw [map_mul, ← hq j, map_mul, ← mul_div_assoc,
          mul_right_comm (e z (q j)) (e z (d j)), mul_div_cancel_right₀ _ (hd j), mul_comm]
      change ∑ j, (p j).eval₂ incl z * iteratedDeriv j.val f z = 0
      simp_rw [hEval, mul_assoc]
      rw [← Finset.mul_sum, hr z hd, mul_zero]
    exact congrFun (Continuous.ext_on hdense hF continuous_const hOn)
  · rintro ⟨m, p, ⟨i, hi⟩, hp⟩
    let r (j : Fin (m + 1)) : RatFunc k := algebraMap (Polynomial k) (RatFunc k) (p j)
    refine ⟨m, r, ⟨i, RatFunc.algebraMap_ne_zero hi⟩, fun z _ => ?_⟩
    simpa only [r, RatFunc.eval_algebraMap, Algebra.id.map_eq_id, RingHom.id_apply] using hp z

end WideE
