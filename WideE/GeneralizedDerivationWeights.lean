import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.Ring

/-! Generalized weights of a derivation add under multiplication. -/

noncomputable section

namespace WideE

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

private theorem shiftedDerivation_mul (D : Derivation k A A) (a b : k) (x y : A) :
    (D.toLinearMap - (a + b) • (1 : Module.End k A)) (x * y) =
      (D.toLinearMap - a • (1 : Module.End k A)) x * y +
        x * (D.toLinearMap - b • (1 : Module.End k A)) y := by
  change D (x * y) - (a + b) • (x * y) = (D x - a • x) * y + x * (D y - b • y)
  simp only [D.leibniz, Algebra.id.smul_eq_mul, Algebra.smul_def, map_add]
  ring

private theorem shiftedDerivation_pow_mul (D : Derivation k A A) (a b : k) (m n : ℕ)
    (x y : A) (hx : ((D.toLinearMap - a • (1 : Module.End k A)) ^ m) x = 0)
    (hy : ((D.toLinearMap - b • (1 : Module.End k A)) ^ n) y = 0) :
    ((D.toLinearMap - (a + b) • (1 : Module.End k A)) ^ (m + n)) (x * y) = 0 := by
  induction m generalizing n x y with
  | zero =>
    have h : x = 0 := by simpa only [pow_zero, Module.End.one_apply] using hx
    rw [h, zero_mul, map_zero]
  | succ m hm =>
    induction n generalizing x y with
    | zero =>
      have h : y = 0 := by simpa only [pow_zero, Module.End.one_apply] using hy
      rw [h, mul_zero, map_zero]
    | succ n hn =>
      have hx' : ((D.toLinearMap - a • (1 : Module.End k A)) ^ m)
          ((D.toLinearMap - a • (1 : Module.End k A)) x) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply] using hx
      have hy' : ((D.toLinearMap - b • (1 : Module.End k A)) ^ n)
          ((D.toLinearMap - b • (1 : Module.End k A)) y) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply] using hy
      rw [Nat.succ_add, pow_succ, Module.End.mul_apply, shiftedDerivation_mul, map_add,
        hm (n + 1) _ y hx' hy, Nat.add_succ, ← Nat.succ_add, hn x _ hx hy', zero_add]

/-- Generalized eigenvectors of a derivation multiply into the sum of their weights. -/
theorem mul_mem_derivation_maxGenEigenspace (D : Derivation k A A) {a b : k} {x y : A}
    (hx : x ∈ Module.End.maxGenEigenspace D.toLinearMap a)
    (hy : y ∈ Module.End.maxGenEigenspace D.toLinearMap b) :
    x * y ∈ Module.End.maxGenEigenspace D.toLinearMap (a + b) := by
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx
  obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hy
  exact (Module.End.mem_maxGenEigenspace _ _ _).mpr
    ⟨m + n, shiftedDerivation_pow_mul D a b m n x y hm hn⟩

private theorem one_mem_derivation_maxGenEigenspace (D : Derivation k A A) :
    (1 : A) ∈ Module.End.maxGenEigenspace D.toLinearMap 0 :=
  (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨1, by
    rw [pow_one, zero_smul, sub_zero]
    exact D.map_one_eq_zero⟩

private theorem pow_mem_derivation_maxGenEigenspace (D : Derivation k A A) {a : k} {x : A}
    (hx : x ∈ Module.End.maxGenEigenspace D.toLinearMap a) (n : ℕ) :
    x ^ n ∈ Module.End.maxGenEigenspace D.toLinearMap (n • a) := by
  induction n with
  | zero => simpa only [pow_zero, zero_nsmul] using one_mem_derivation_maxGenEigenspace D
  | succ n ih =>
    simpa only [pow_succ, succ_nsmul, add_comm] using mul_mem_derivation_maxGenEigenspace D ih hx

private theorem prod_mem_derivation_maxGenEigenspace (D : Derivation k A A)
    {σ : Type*} {x : σ → A} {w : σ → k}
    (h : ∀ i, x i ∈ Module.End.maxGenEigenspace D.toLinearMap (w i))
    (m : σ →₀ ℕ) (s : Finset σ) :
    ∏ i ∈ s, x i ^ m i ∈ Module.End.maxGenEigenspace D.toLinearMap (∑ i ∈ s, m i • w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.sum_empty] using one_mem_derivation_maxGenEigenspace D
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mul_mem_derivation_maxGenEigenspace D (pow_mem_derivation_maxGenEigenspace D (h i) _) ih

/-- Evaluating a monomial of generalized eigenvector generators gives a generalized eigenvector. -/
theorem aeval_monomial_mem_derivation_maxGenEigenspace (D : Derivation k A A)
    {σ : Type*} {x : σ → A} {w : σ → k}
    (h : ∀ i, x i ∈ Module.End.maxGenEigenspace D.toLinearMap (w i))
    (m : σ →₀ ℕ) (c : k) :
    MvPolynomial.aeval x (MvPolynomial.monomial m c) ∈
      Module.End.maxGenEigenspace D.toLinearMap (m.sum fun i n => n • w i) := by
  rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  exact Submodule.smul_mem _ c (prod_mem_derivation_maxGenEigenspace D h m m.support)

end WideE
