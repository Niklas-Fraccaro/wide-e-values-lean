import WideE.HomogeneousZeros
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Tsen's coefficient count over a rational function field

Substitute polynomials of bounded degree with independent coefficient variables. The
coefficients of the resulting polynomial form fewer homogeneous equations than unknowns.
This is the rational function field case of the argument in Stacks Project, Tag 03RD.
-/

noncomputable section

open scoped BigOperators
open MvPolynomial

namespace WideE

/-- Common zeros of equally graded equations over the coefficient field. -/
def HomogeneousSystemHasNonzeroZero (K : Type*) [Field K] : Prop :=
  ∀ {r s d : ℕ} (f : Fin s → MvPolynomial (Fin r) K),
    (∀ i, (f i).IsHomogeneous d) → 0 < d → s < r →
      ∃ x : Fin r → K, x ≠ 0 ∧ ∀ i, eval x (f i) = 0

/-- A field is C₁ if positive-degree homogeneous forms in more variables than
their degree have a nontrivial zero. -/
def IsC1 (K : Type*) [Field K] : Prop :=
  ∀ {r d : ℕ} (p : MvPolynomial (Fin r) K),
    p.IsHomogeneous d → 0 < d → d < r → ∃ x : Fin r → K, x ≠ 0 ∧ eval x p = 0

namespace Tsen

section Coefficients

variable {K σ : Type*} [CommSemiring K]

private def coefficientsHomogeneous (d : ℕ) (P : Polynomial (MvPolynomial σ K)) : Prop :=
  ∀ j : ℕ, (P.coeff j).IsHomogeneous d

private theorem coefficientsHomogeneous_one :
    coefficientsHomogeneous 0 (1 : Polynomial (MvPolynomial σ K)) := by
  intro j
  by_cases h : j = 0 <;> simp [Polynomial.coeff_one, h, isHomogeneous_one, isHomogeneous_zero]

private theorem coefficientsHomogeneous_mul {d e : ℕ} {P Q : Polynomial (MvPolynomial σ K)}
    (hP : coefficientsHomogeneous d P) (hQ : coefficientsHomogeneous e Q) :
    coefficientsHomogeneous (d + e) (P * Q) := by
  intro j
  rw [Polynomial.coeff_mul]
  exact IsHomogeneous.sum _ _ _ fun z _ => (hP z.1).mul (hQ z.2)

private theorem coefficientsHomogeneous_prod {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (MvPolynomial σ K)) (d : ι → ℕ)
    (hP : ∀ i ∈ s, coefficientsHomogeneous (d i) (P i)) :
    coefficientsHomogeneous (∑ i ∈ s, d i) (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Finset.prod_empty] using coefficientsHomogeneous_one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact coefficientsHomogeneous_mul (hP i (Finset.mem_insert_self _ _))
      (ih fun j hj => hP j (Finset.mem_insert_of_mem hj))

private theorem coefficientsHomogeneous_pow {d : ℕ} {P : Polynomial (MvPolynomial σ K)}
    (hP : coefficientsHomogeneous d P) (n : ℕ) : coefficientsHomogeneous (n * d) (P ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, zero_mul] using coefficientsHomogeneous_one
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact coefficientsHomogeneous_mul ih hP

end Coefficients

variable {K : Type*} [CommSemiring K] {r e : ℕ}

/-- The `i`th polynomial with independent coefficients up to degree `e`. -/
private def genericPolynomial (i : Fin r) : Polynomial (MvPolynomial (Fin (r * (e + 1))) K) :=
  ∑ j : Fin (e + 1), Polynomial.monomial j.val (X (finProdFinEquiv (i, j)))

private theorem coeff_genericPolynomial (i : Fin r) (j : ℕ) :
    (genericPolynomial (K := K) (e := e) i).coeff j =
      if hj : j < e + 1 then X (finProdFinEquiv (i, ⟨j, hj⟩)) else 0 := by
  classical
  rw [genericPolynomial, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  split_ifs with hj
  · rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin (e + 1))]
    · simp
    · intro l _ hl
      refine if_neg ?_
      exact fun h => hl (Fin.ext h)
    · simp
  · apply Finset.sum_eq_zero
    intro l _
    refine if_neg ?_
    intro h
    exact hj (h ▸ l.isLt)

private theorem natDegree_genericPolynomial_le (i : Fin r) :
    (genericPolynomial (K := K) (e := e) i).natDegree ≤ e := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ j.isLt)

private theorem genericPolynomial_homogeneous (i : Fin r) :
    coefficientsHomogeneous 1 (genericPolynomial (K := K) (e := e) i) := by
  intro j
  rw [coeff_genericPolynomial]
  split_ifs
  · exact isHomogeneous_X (R := K) _
  · exact isHomogeneous_zero _ K _

private def substituteGeneric (p : MvPolynomial (Fin r) (Polynomial K)) :
    Polynomial (MvPolynomial (Fin (r * (e + 1))) K) :=
  eval₂ (Polynomial.mapRingHom (C : K →+* MvPolynomial (Fin (r * (e + 1))) K))
    (genericPolynomial (K := K) (e := e)) p

private theorem substituteGeneric_natDegree_le {p : MvPolynomial (Fin r) (Polynomial K)} {d D : ℕ}
    (hp : p.IsHomogeneous d) (hD : ∀ s ∈ p.support, (p.coeff s).natDegree ≤ D) :
    (substituteGeneric (e := e) p).natDegree ≤ D + e * d := by
  rw [substituteGeneric, eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  have hsd : s.degree = d := (congrFun Finsupp.degree_eq_weight_one s).trans (hp (mem_support_iff.mp hs))
  apply Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_map_le.trans (hD s hs))
  calc
    (∏ i ∈ s.support, (genericPolynomial (K := K) (e := e) i) ^ s i).natDegree
        ≤ ∑ i ∈ s.support, ((genericPolynomial (K := K) (e := e) i) ^ s i).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i ∈ s.support, e * s i := Finset.sum_le_sum fun i _ => by
      exact (Polynomial.natDegree_pow_le_of_le (s i) (natDegree_genericPolynomial_le i)).trans_eq
        (Nat.mul_comm (s i) e)
    _ = e * d := by rw [← Finset.mul_sum, ← Finsupp.degree, hsd]

private theorem substituteGeneric_homogeneous {p : MvPolynomial (Fin r) (Polynomial K)} {d : ℕ}
    (hp : p.IsHomogeneous d) : coefficientsHomogeneous d (substituteGeneric (e := e) p) := by
  intro j
  rw [substituteGeneric, eval₂_eq, Polynomial.finset_sum_coeff]
  apply IsHomogeneous.sum
  intro s hs
  have hsd : s.degree = d := (congrFun Finsupp.degree_eq_weight_one s).trans (hp (mem_support_iff.mp hs))
  have hC : coefficientsHomogeneous 0
      (Polynomial.map (C : K →+* MvPolynomial (Fin (r * (e + 1))) K) (p.coeff s)) := by
    intro m
    rw [Polynomial.coeff_map]
    exact isHomogeneous_C _ _
  have hPow (i : Fin r) (hi : i ∈ s.support) :
      coefficientsHomogeneous (s i) ((genericPolynomial (K := K) (e := e) i) ^ s i) := by
    simpa only [mul_one] using coefficientsHomogeneous_pow (genericPolynomial_homogeneous i) (s i)
  have hProd := coefficientsHomogeneous_prod s.support
    (fun i => (genericPolynomial (K := K) (e := e) i) ^ s i) s hPow
  change coefficientsHomogeneous s.degree _ at hProd
  simpa only [zero_add, hsd] using (coefficientsHomogeneous_mul hC hProd) j

private theorem eval_substituteGeneric
    (p : MvPolynomial (Fin r) (Polynomial K)) (x : Fin (r * (e + 1)) → K) :
    Polynomial.map (eval x) (substituteGeneric (e := e) p) =
      eval (fun i => Polynomial.map (eval x) (genericPolynomial (K := K) (e := e) i)) p := by
  change (Polynomial.mapRingHom (eval x)) (eval₂ _ _ p) = _
  rw [eval₂_comp_left, Polynomial.mapRingHom_comp]
  have h : (eval x).comp C = RingHom.id K := RingHom.ext fun a => eval_C a
  have h' : Polynomial.mapRingHom (RingHom.id K) = RingHom.id (Polynomial K) :=
    RingHom.ext fun _ => Polynomial.map_id
  rw [h, h']
  rfl

end Tsen

section RationalFunctionField

open Tsen

variable {K : Type*} [Field K] {r d : ℕ}

/-- Coefficient counting gives a polynomial vector solving a homogeneous form. -/
theorem exists_polynomial_nonzero_zero_of_common_zeros
    (hSystems : HomogeneousSystemHasNonzeroZero K)
    (p : MvPolynomial (Fin r) (Polynomial K)) (hp : p.IsHomogeneous d)
    (hd : 0 < d) (hdr : d < r) :
    ∃ y : Fin r → Polynomial K, y ≠ 0 ∧ eval y p = 0 := by
  classical
  let D := p.support.sup fun s => (p.coeff s).natDegree
  let P := substituteGeneric (e := D) p
  let f (j : Fin (D + D * d + 1)) : MvPolynomial (Fin (r * (D + 1))) K := P.coeff j.val
  have hcount : D + D * d + 1 < r * (D + 1) := by
    calc
      D + D * d + 1 < (d + 1) * (D + 1) := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.mul_comm D d]
        omega
      _ ≤ r * (D + 1) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hdr)
  have hdegree : P.natDegree ≤ D + D * d :=
    substituteGeneric_natDegree_le hp (fun _ hs => Finset.le_sup (f := fun s => (p.coeff s).natDegree) hs)
  obtain ⟨x, hx, hfx⟩ := hSystems f (fun j => substituteGeneric_homogeneous hp j.val) hd hcount
  let y (i : Fin r) : Polynomial K := Polynomial.map (eval x) (genericPolynomial (e := D) i)
  refine ⟨y, ?_, ?_⟩
  · intro hy
    apply hx
    funext k
    obtain ⟨⟨i, j⟩, rfl⟩ := (finProdFinEquiv (m := r) (n := D + 1)).surjective k
    have h := congrArg (fun Q : Polynomial K => Q.coeff j.val) (congrFun hy i)
    simpa only [y, Polynomial.coeff_map, coeff_genericPolynomial, dif_pos j.isLt, eval_X,
      Pi.zero_apply, Polynomial.coeff_zero] using h
  · rw [← eval_substituteGeneric (e := D) p x]
    ext j
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero]
    by_cases hj : j < D + D * d + 1
    · exact hfx ⟨j, hj⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegree (by omega)), map_zero]

private theorem clearHomogeneousDenominators
    (p : MvPolynomial (Fin r) (RatFunc K)) (hp : p.IsHomogeneous d) :
    ∃ a : RatFunc K, a ≠ 0 ∧ ∃ q : MvPolynomial (Fin r) (Polynomial K),
      q.IsHomogeneous d ∧ map (algebraMap (Polynomial K) (RatFunc K)) q = C a * p := by
  classical
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples
    (nonZeroDivisors (Polynomial K)) p.support p.coeff
  let q := ∑ s ∈ p.support.attach, monomial s.val (ha s.val s.property).choose
  refine ⟨algebraMap _ _ a.val, (IsLocalization.map_units (RatFunc K) a).ne_zero, q, ?_, ?_⟩
  · apply IsHomogeneous.sum
    intro s _
    exact isHomogeneous_monomial _ ((congrFun Finsupp.degree_eq_weight_one s.val).trans
      (hp (mem_support_iff.mp s.property)))
  · calc
      map (algebraMap (Polynomial K) (RatFunc K)) q =
          ∑ s ∈ p.support.attach, monomial s.val (algebraMap _ _ a.val * p.coeff s.val) := by
        dsimp only [q]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro s _
        rw [map_monomial]
        exact congrArg (monomial s.val) (by
          simpa only [Algebra.smul_def] using (ha s.val s.property).choose_spec)
      _ = ∑ s ∈ p.support, monomial s (algebraMap _ _ a.val * p.coeff s) :=
        Finset.sum_attach p.support (fun s => monomial s (algebraMap _ _ a.val * p.coeff s))
      _ = C (algebraMap _ _ a.val) * p := by
        simp only [← C_mul_monomial, ← Finset.mul_sum, ← p.as_sum]

/-- The rational function field is C₁ if the coefficient field solves the common-zero systems. -/
theorem exists_ratFunc_nonzero_zero_of_common_zeros
    (hSystems : HomogeneousSystemHasNonzeroZero K)
    (p : MvPolynomial (Fin r) (RatFunc K)) (hp : p.IsHomogeneous d)
    (hd : 0 < d) (hdr : d < r) :
    ∃ y : Fin r → RatFunc K, y ≠ 0 ∧ eval y p = 0 := by
  obtain ⟨a, ha, q, hq, hqmap⟩ := clearHomogeneousDenominators p hp
  obtain ⟨x, hx, hz⟩ := exists_polynomial_nonzero_zero_of_common_zeros hSystems q hq hd hdr
  let emb := algebraMap (Polynomial K) (RatFunc K)
  refine ⟨emb ∘ x, ?_, ?_⟩
  · intro hy
    apply hx
    funext i
    apply RatFunc.algebraMap_injective K
    simpa only [Function.comp_apply, Pi.zero_apply, map_zero] using congrFun hy i
  · have h := congrArg (eval (emb ∘ x)) hqmap
    rw [eval_map, ← eval₂_comp, hz, map_zero, map_mul, eval_C] at h
    exact (mul_eq_zero.mp h.symm).resolve_left ha

/-- Tsen's theorem for the rational function field over an algebraically closed field. -/
theorem ratFunc_isC1 (K : Type*) [Field K] [IsAlgClosed K] : IsC1 (RatFunc K) :=
  fun p hp hd hdr => exists_ratFunc_nonzero_zero_of_common_zeros
    (fun f hf hd' hsr => exists_homogeneous_common_nonzero_zero f hf hd' hsr) p hp hd hdr

/-- A positive-degree homogeneous form over k(t) has a nontrivial zero if the
number of variables exceeds the degree and k is algebraically closed. -/
theorem exists_ratFunc_nonzero_zero [IsAlgClosed K]
    (p : MvPolynomial (Fin r) (RatFunc K)) (hp : p.IsHomogeneous d)
    (hd : 0 < d) (hdr : d < r) : ∃ y : Fin r → RatFunc K, y ≠ 0 ∧ eval y p = 0 :=
  ratFunc_isC1 K p hp hd hdr

end RationalFunctionField
end WideE
