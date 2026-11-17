import WideE.Closure
import Stage16LaurentMatrixClearing
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Division from Laurent operators and ordinary linear specialization

The Laurent-operator assertion and the exact linear lifting assertion are
explicit inputs. This reduction constructs the divided wide function from
its derivative companion system.
-/

noncomputable section

namespace WideE

open scoped BigOperators

local notation "algIncl" => AlgHom.toRingHom (IntermediateField.val (algebraicClosure ℚ ℂ))

/-- An actual differential equation monic in the highest derivative, with
Laurent coefficients evaluated on the punctured plane. -/
def HasLaurentOperator (f : ℂ → ℂ) : Prop :=
  ∃ r : ℕ, 0 < r ∧ ∃ b : Fin r → LaurentPolynomial AlgebraicComplex,
    ∀ z : ℂˣ, iteratedDeriv r f (z : ℂ) =
      ∑ j, LaurentPolynomial.eval₂ algIncl z (b j) * iteratedDeriv j.val f (z : ℂ)

/-- The Laurent-operator input used for nonzero wide functions. -/
def WideLaurentOperatorExistence : Prop :=
  ∀ f : ℂ → ℂ, IsWideEFunction f → f ≠ 0 → HasLaurentOperator f

/-- A global differential system in which one polynomial denominator was cleared. -/
def ClearedLinearSystem {ι : Type*} [Fintype ι]
    (F : ι → ℂ → ℂ) (t : Polynomial AlgebraicComplex)
    (B : Matrix ι ι (Polynomial AlgebraicComplex)) : Prop :=
  ∀ z i, t.eval₂ algIncl z * deriv (F i) z =
    ∑ j, (B i j).eval₂ algIncl z * F j z

/-- Every linear relation among the values at an ordinary point lifts to
polynomials that specialize to the original coefficients. -/
def WideLinearOrdinaryLiftingAtOne : Prop :=
  ∀ (r : ℕ), 0 < r →
    ∀ (F : Fin r → ℂ → ℂ) (t : Polynomial AlgebraicComplex)
      (B : Matrix (Fin r) (Fin r) (Polynomial AlgebraicComplex)),
      t.eval 1 ≠ 0 → (∀ i, IsWideEFunction (F i)) → ClearedLinearSystem F t B →
      ∀ (c : Fin r → AlgebraicComplex),
        (∑ i, (c i : ℂ) * F i 1) = 0 →
        ∃ p : Fin r → Polynomial AlgebraicComplex,
          (∀ i, (p i).eval 1 = c i) ∧ ∀ z : ℂ, ∑ i, (p i).eval₂ algIncl z * F i z = 0

/-- A common power of the coordinate clears every coefficient of a Laurent
system. Continuity extends the cleared equation across the origin. -/
theorem exists_clearedLinearSystem_of_laurent {ι : Type*} [Fintype ι]
    (F : ι → ℂ → ℂ) (hf : ∀ i, IsWideEFunction (F i))
    (A : Matrix ι ι (LaurentPolynomial AlgebraicComplex))
    (hs : ∀ z : ℂˣ, ∀ i, deriv (F i) (z : ℂ) =
      ∑ j, LaurentPolynomial.eval₂ algIncl z (A i j) * F j (z : ℂ)) :
    ∃ N : ℕ, ∃ B : Matrix ι ι (Polynomial AlgebraicComplex),
      (∀ i j, Polynomial.toLaurent (B i j) = A i j * LaurentPolynomial.T (N : ℤ)) ∧
      ClearedLinearSystem F (Polynomial.X ^ N) B := by
  obtain ⟨N, _, B, hB⟩ := StrictEUnit.stage16_laurentMatrix_exists_positive_clearing A
  refine ⟨N, B, hB, fun z i => ?_⟩
  let left : ℂ → ℂ := fun w => w ^ N * deriv (F i) w
  let right : ℂ → ℂ := fun w => ∑ j, (B i j).eval₂ algIncl w * F j w
  have hleft : Continuous left :=
    (continuous_id.pow N).mul (hf i).derivative.differentiable.continuous
  have hright : Continuous right :=
    continuous_finset_sum _ (fun j _ =>
      ((B i j).continuous_eval₂ algIncl).mul (hf j).differentiable.continuous)
  have hsame : Set.EqOn left right ({0}ᶜ : Set ℂ) := by
    intro w hw
    have hne : w ≠ 0 := fun heq => hw (Set.mem_singleton_iff.mpr heq)
    let u := Units.mk0 w hne
    change w ^ N * deriv (F i) w = ∑ j, (B i j).eval₂ algIncl w * F j w
    have hsys : deriv (F i) w = ∑ j, LaurentPolynomial.eval₂ algIncl u (A i j) * F j w :=
      hs u i
    rw [hsys, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hEval := congrArg (LaurentPolynomial.eval₂ algIncl u) (hB i j)
    rw [LaurentPolynomial.eval₂_toLaurent, map_mul, LaurentPolynomial.eval₂_T_n] at hEval
    change (B i j).eval₂ algIncl w = LaurentPolynomial.eval₂ algIncl u (A i j) * w ^ N
      at hEval
    rw [hEval, mul_left_comm, mul_assoc]
  have heq := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hleft hright hsame
  simpa only [left, right, Polynomial.eval₂_X_pow] using congrFun heq z

/-- The vector of derivatives below the order of a Laurent operator has a
global polynomial system, with denominator nonzero at one. -/
theorem HasLaurentOperator.derivativeCompanion {f : ℂ → ℂ} (hf : IsWideEFunction f)
    (h : HasLaurentOperator f) :
    ∃ r : ℕ, 0 < r ∧ ∃ (t : Polynomial AlgebraicComplex)
      (B : Matrix (Fin r) (Fin r) (Polynomial AlgebraicComplex)),
      t.eval 1 ≠ 0 ∧ ClearedLinearSystem (fun i => iteratedDeriv i.val f) t B := by
  classical
  obtain ⟨r, hr, b, hb⟩ := h
  let F (i : Fin r) := iteratedDeriv i.val f
  let A : Matrix (Fin r) (Fin r) (LaurentPolynomial AlgebraicComplex) :=
    fun i j => if i.val + 1 < r then (if j.val = i.val + 1 then 1 else 0) else b j
  have hSystem (z : ℂˣ) (i : Fin r) : deriv (F i) (z : ℂ) =
      ∑ j, LaurentPolynomial.eval₂ algIncl z (A i j) * F j (z : ℂ) := by
    by_cases hi : i.val + 1 < r
    · let j₀ : Fin r := ⟨i.val + 1, hi⟩
      rw [Finset.sum_eq_single j₀]
      · simp [A, F, hi, j₀, iteratedDeriv_succ]
      · intro j _ hj
        have hne : j.val ≠ i.val + 1 := fun heq => hj (Fin.ext heq)
        simp [A, hi, hne]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ j₀))
    · have hid : i.val + 1 = r :=
        le_antisymm (Nat.succ_le_of_lt i.isLt) (Nat.le_of_not_gt hi)
      simpa only [A, F, if_neg hi, ← iteratedDeriv_succ, hid] using hb z
  obtain ⟨N, B, _, hB⟩ := exists_clearedLinearSystem_of_laurent F
    (fun i => hf.iteratedDeriv i.val) A hSystem
  exact ⟨r, hr, Polynomial.X ^ N, B, by simp, hB⟩

/-- Clearing a Laurent operator gives a polynomial annihilator whose leading
coefficient is nonzero at one. -/
theorem HasLaurentOperator.polynomialAnnihilator {f : ℂ → ℂ} (hf : IsWideEFunction f)
    (h : HasLaurentOperator f) :
    ∃ r : ℕ, ∃ p : Fin (r + 1) → Polynomial AlgebraicComplex,
      (p (Fin.last r)).eval 1 ≠ 0 ∧
        ∀ z : ℂ, ∑ i, (p i).eval₂ algIncl z * iteratedDeriv i.val f z = 0 := by
  obtain ⟨r, hr, t, B, ht, hB⟩ := h.derivativeCompanion hf
  let i : Fin r := ⟨r.pred, Nat.pred_lt (Nat.ne_of_gt hr)⟩
  let p : Fin (r + 1) → Polynomial AlgebraicComplex := Fin.lastCases t (fun j => -B i j)
  refine ⟨r, p, by simpa [p] using ht, fun z => ?_⟩
  have heq : t.eval₂ algIncl z * iteratedDeriv r f z =
      ∑ j, (B i j).eval₂ algIncl z * iteratedDeriv j.val f z := by
    have hi : r.pred + 1 = r := Nat.succ_pred_eq_of_pos hr
    simpa only [i, ← iteratedDeriv_succ, hi] using hB z i
  rw [Fin.sum_univ_castSucc]
  simp only [p, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.coe_castSucc, Fin.val_last,
    Polynomial.eval₂_neg, neg_mul, Finset.sum_neg_distrib, heq, neg_add_cancel]

private theorem polynomial_factor_at_one (p : Polynomial AlgebraicComplex) :
    ∃ q : Polynomial AlgebraicComplex,
      p = Polynomial.C (p.eval 1) + (Polynomial.X - Polynomial.C 1) * q := by
  have hd : Polynomial.X - Polynomial.C 1 ∣ p - Polynomial.C (p.eval 1) :=
    Polynomial.dvd_iff_isRoot.mpr (by simp [Polynomial.IsRoot])
  obtain ⟨q, hq⟩ := hd
  exact ⟨q, by rw [← hq, add_comm, sub_add_cancel]⟩

/-- Finite polynomial linear combinations of wide functions stay in the same class. -/
theorem isWideEFunction_polynomialCombination {ι : Type*} [Fintype ι]
    (p : ι → Polynomial AlgebraicComplex) (F : ι → ℂ → ℂ)
    (hF : ∀ i, IsWideEFunction (F i)) :
    IsWideEFunction (fun z => ∑ i, (p i).eval₂ algIncl z * F i z) := by
  classical
  let term (i : ι) (z : ℂ) := (p i).eval₂ algIncl z * F i z
  have hterm (i : ι) : IsWideEFunction (term i) :=
    (isWideEFunction_polynomial (p i)).mul (hF i)
  change IsWideEFunction (fun z => ∑ i, term i z)
  refine Finset.induction_on
    (motive := fun s => IsWideEFunction (fun z => ∑ i ∈ s, term i z)) Finset.univ ?_ ?_
  · simpa using isWideEFunction_const (0 : AlgebraicComplex)
  · intro i s hi hs
    simpa only [Finset.sum_insert hi] using (hterm i).add hs

/-- A Laurent operator and linear lifting applied to the zeroth companion
coordinate give the wide quotient at one for arbitrary algebraic coefficients. -/
theorem wideEFunction_divAtOne_of_laurentOperator_and_linearLifting
    (hLift : WideLinearOrdinaryLiftingAtOne) {f : ℂ → ℂ}
    (hf : IsWideEFunction f) (hOperator : HasLaurentOperator f) (hz : f 1 = 0) :
    ∃ g : ℂ → ℂ, IsWideEFunction g ∧ ∀ z : ℂ, (z - 1) * g z = f z := by
  classical
  obtain ⟨r, hr, t, B, ht, hB⟩ := hOperator.derivativeCompanion hf
  let F (i : Fin r) := iteratedDeriv i.val f
  have hF (i : Fin r) : IsWideEFunction (F i) := hf.iteratedDeriv i.val
  let i₀ : Fin r := ⟨0, hr⟩
  let c (i : Fin r) : AlgebraicComplex := if i = i₀ then 1 else 0
  have hc (z : ℂ) : ∑ i, (c i : ℂ) * F i z = f z := by
    rw [Finset.sum_eq_single i₀]
    · simp [c, F, i₀, iteratedDeriv_zero]
    · intro i _ hi
      simp [c, hi]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i₀))
  obtain ⟨p, hp, hpSum⟩ := hLift r hr F t B ht hF hB c ((hc 1).trans hz)
  choose q hq using fun i => polynomial_factor_at_one (p i)
  let g (z : ℂ) := -(∑ i, (q i).eval₂ algIncl z * F i z)
  refine ⟨g, (isWideEFunction_polynomialCombination q F hF).neg, ?_⟩
  intro z
  have heval (i : Fin r) :
      (p i).eval₂ algIncl z = (c i : ℂ) + (z - 1) * (q i).eval₂ algIncl z := by
    rw [hq i, hp i]
    simp
  have heq := hpSum z
  simp_rw [heval, add_mul, mul_assoc] at heq
  rw [Finset.sum_add_distrib, hc, ← Finset.mul_sum] at heq
  dsimp only [g]
  rw [mul_neg]
  exact (eq_neg_of_add_eq_zero_left heq).symm

/-- The two arithmetic inputs give division at one on the whole wide class. -/
theorem wideEFunction_divAtOne_of_arithmetic_inputs
    (hOperator : WideLaurentOperatorExistence) (hLift : WideLinearOrdinaryLiftingAtOne)
    {f : ℂ → ℂ} (hf : IsWideEFunction f) (hz : f 1 = 0) :
    ∃ g : ℂ → ℂ, IsWideEFunction g ∧ ∀ z : ℂ, (z - 1) * g z = f z := by
  by_cases hne : f = 0
  · refine ⟨fun _ => 0, ?_, fun z => ?_⟩
    · simpa using isWideEFunction_const (0 : AlgebraicComplex)
    · simp [hne]
  · exact wideEFunction_divAtOne_of_laurentOperator_and_linearLifting hLift hf
      (hOperator f hf hne) hz

end WideE
