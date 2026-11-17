import WideE.AnalyticUnit
import WideE.ModuleCoordinates
import WideE.RelationModule

/-! Realization of Kummer-pulled module coordinates as actual punctured
functions, with multiplication and the value at one preserved. -/

open scoped BigOperators WideE

noncomputable section

namespace WideE

open LaurentPolynomial StrictEUnit

local notation "R" => LaurentPolynomial AlgebraicComplex
local notation "algIncl" => AlgHom.toRingHom (IntermediateField.val (algebraicClosure ℚ ℂ))

private def evalLaurent (z : ℂˣ) : R →+* ℂ := eval₂ algIncl z

private theorem evalLaurent_kummer (z : ℂˣ) (q : ℕ) (p : R) :
    evalLaurent z (kummer AlgebraicComplex q p) = evalLaurent (z ^ q) p :=
  DFunLike.congr_fun (eval₂_comp_kummer AlgebraicComplex algIncl z q) p

private theorem evalLaurent_one (p : R) :
    evalLaurent 1 p = (evalAtOne AlgebraicComplex p : ℂ) := by
  simpa only [evalLaurent, evalAtOne, evalLaurentAt, Units.mk0_one] using
    evalLaurentAt_one (algebraicClosure ℚ ℂ).toSubfield p

/-- This is evaluation of the Kummer pullback of one finite coordinate vector. -/
def ramifiedModuleRealization {ι : Type*} [Fintype ι] (q : ℕ)
    (F : ι → WidePunctured) (X : ι → R) (z : ℂˣ) : ℂ :=
  ∑ i, evalLaurent z (X i) * puncturedEvaluation (z ^ q) (F i)

theorem puncturedEvaluation_basis {ι : Type*} [Fintype ι]
    {M : Submodule R WidePunctured} (b : Basis ι R M) (x : M) (z : ℂˣ) :
    puncturedEvaluation z x.val =
      ∑ i, evalLaurent z (b.repr x i) * puncturedEvaluation z (b i).val := by
  have h := congrArg (fun v : M => puncturedEvaluation z v.val) (b.sum_repr x)
  change puncturedEvaluation z (↑(∑ i, b.repr x i • b i : M) : WidePunctured) = _ at h
  rw [Submodule.coe_sum, map_sum] at h
  simpa only [Submodule.coe_smul, puncturedEvaluation_smul, evalLaurent] using h.symm

/-- The actual value of a realized coordinate vector depends on its
specialization at one. -/
theorem ramifiedModuleRealization_atOne {ι : Type*} [Fintype ι]
    {M : Submodule R WidePunctured} (b : Basis ι R M) (x : M)
    (q : ℕ) (X : ι → R)
    (hX : ∀ i, evalAtOne AlgebraicComplex (X i) = evalAtOne AlgebraicComplex (b.repr x i)) :
    ramifiedModuleRealization q (fun i => (b i).val) X 1 = puncturedEvaluation 1 x.val := by
  rw [puncturedEvaluation_basis b x, ramifiedModuleRealization, one_pow]
  exact Finset.sum_congr rfl (fun i _ => by rw [evalLaurent_one, hX, evalLaurent_one])

/-- A product identity on the two finite coordinate vectors gives the
pointwise identity on the punctured plane. -/
theorem ramifiedModuleRealization_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Submodule R WidePunctured) (h1 : (1 : WidePunctured) ∈ M)
    (bM : Basis ι R M) (bN : Basis κ R (M * M : Submodule R WidePunctured))
    (q : ℕ) (X Y : ι → R)
    (hXY : coordinateProduct (fun i j l => kummer AlgebraicComplex q
      (bN.repr (productBilinear M (bM i) (bM j)) l)) X Y =
      fun l => kummer AlgebraicComplex q (bN.repr (productOne M h1) l))
    (z : ℂˣ) :
    ramifiedModuleRealization q (fun i => (bM i).val) X z *
      ramifiedModuleRealization q (fun i => (bM i).val) Y z = 1 := by
  let f (i : ι) := puncturedEvaluation (z ^ q) (bM i).val
  let g (l : κ) := puncturedEvaluation (z ^ q) (bN l).val
  let c (i j : ι) (l : κ) := kummer AlgebraicComplex q
    (bN.repr (productBilinear M (bM i) (bM j)) l)
  let d (l : κ) := kummer AlgebraicComplex q (bN.repr (productOne M h1) l)
  let e := evalLaurent z
  have hProduct (i j : ι) : f i * f j = ∑ l, e (c i j l) * g l := by
    have h := puncturedEvaluation_basis bN (productBilinear M (bM i) (bM j)) (z ^ q)
    simp only [e, c, evalLaurent_kummer]
    exact h
  have hOne : 1 = ∑ l, e (d l) * g l := by
    have h := puncturedEvaluation_basis bN (productOne M h1) (z ^ q)
    simp only [e, d, evalLaurent_kummer]
    exact h
  change (∑ i, e (X i) * f i) * (∑ j, e (Y j) * f j) = 1
  calc
    _ = ∑ i, ∑ j, e (X i) * (e (Y j) * (f i * f j)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i, ∑ j, ∑ l, (e (X i) * (e (Y j) * e (c i j l))) * g l := by
      simp only [hProduct, Finset.mul_sum, mul_assoc]
    _ = ∑ l, e (coordinateProduct c X Y l) * g l := by
      simp only [coordinateProduct_apply, map_sum, map_mul, Finset.sum_mul]
      calc
        _ = ∑ i, ∑ l, ∑ j, (e (X i) * (e (Y j) * e (c i j l))) * g l :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
        _ = _ := Finset.sum_comm
    _ = 1 := by rw [hXY, ← hOne]

private theorem exists_taylorRealization {f : ℂ → ℂ} (hf : IsWideEFunction f) :
    ∃ F : subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield,
      ∀ z, F.val.val z = f z := by
  obtain ⟨_, hd, hs, _⟩ := hf
  exact ⟨taylorRealization f hd hs, fun _ => rfl⟩

/-- The analytic conclusion applied to a pair of inverse realizations.
The denominators of the chosen module basis are absorbed into the Laurent
coefficients. -/
theorem ramifiedModuleUnit_atOne {ι : Type*} [Fintype ι]
    {q : ℕ} (hq : 0 < q) (F : ι → WidePunctured) (X : ι → R)
    (v : ℂˣ → ℂ) (huv : ∀ z, ramifiedModuleRealization q F X z * v z = 1) :
    IsAlgebraicScalarExp (ramifiedModuleRealization q F X 1) := by
  have hNum (i : ι) : HasWideNumerator (F i).val := (F i).property
  choose f hf n hn using hNum
  choose G hG using fun i => exists_taylorRealization (hf i)
  let p (i : ι) := X i * T (-((q * n i : ℕ) : ℤ))
  let u (z : Stage16PuncturedPlane) := ramifiedModuleRealization q F X (Units.mk0 z.val z.property)
  let v' (z : Stage16PuncturedPlane) := v (Units.mk0 z.val z.property)
  have hb (i : ι) : ∃ C : ℝ, 0 < C ∧
      ∀ z : ℂ, ‖(G i).val.val z‖ ≤ C * Real.exp (‖z‖ ^ 2) := by
    simpa only [hG] using (hf i).quadratic_exp_bound
  have hU (z : Stage16PuncturedPlane) :
      u z = ∑ i, evalLaurentAt (algebraicClosure ℚ ℂ).toSubfield z (p i) *
        (G i).val.val (z.val ^ q) := by
    let w := Units.mk0 z.val z.property
    change ramifiedModuleRealization q F X w = _
    unfold ramifiedModuleRealization
    apply Finset.sum_congr rfl
    intro i _
    rw [puncturedEvaluation_apply, hn i, hG, Units.val_pow_eq_pow_val]
    change evalLaurent w (X i) * (f i (z.val ^ q) / (z.val ^ q) ^ n i) =
      evalLaurent w (X i * T (-((q * n i : ℕ) : ℤ))) * f i (z.val ^ q)
    have ht : evalLaurent w (T (-((q * n i : ℕ) : ℤ))) = (z.val ^ (q * n i))⁻¹ := by
      rw [evalLaurent, eval₂_T, Units.val_zpow_eq_zpow_val, zpow_neg, zpow_natCast]
      rfl
    rw [(evalLaurent w).map_mul, ht, ← pow_mul, div_eq_mul_inv]
    ring
  have h := ramifiedLaurentUnit_at_one_eq_algebraic_scalar_exp hq p G hb (u := u) (v := v') hU
    (fun z => huv (Units.mk0 z.val z.property))
  have h1 : Units.mk0 (1 : ℂ) one_ne_zero = 1 := Units.ext rfl
  simpa only [u, h1, IsAlgebraicScalarExp] using h

end WideE
