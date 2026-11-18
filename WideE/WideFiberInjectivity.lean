import WideE.RelationModule
import WideE.LaurentExistence

/-! Numerical evaluation is injective on the algebraic fiber of a
differential submodule of the actual punctured wide functions. -/

open scoped TensorProduct WideE

noncomputable section

namespace WideE

open LaurentPolynomial

set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 75000

local notation "k" => AlgebraicComplex
local notation "R" => LaurentPolynomial AlgebraicComplex
local notation "D" => widePuncturedDerivation
local notation "π" => (T 1 - 1 : R)

private theorem punctured_exists_finite_stable_span (u : WidePunctured) :
    ∃ L : Submodule R WidePunctured, L.FG ∧ u ∈ L ∧ ∀ x ∈ L, D x ∈ L := by
  obtain ⟨f, hf, n, h⟩ := u.property
  by_cases hf0 : f = 0
  · have hu : u = 0 := Subtype.ext (funext fun z => by simp [h z, hf0])
    refine ⟨⊥, Submodule.fg_bot, by simp [hu], ?_⟩
    intro x hx
    rw [Submodule.mem_bot] at hx
    simp [hx]
  obtain ⟨L, hLfin, hLmem, hLst⟩ := wideFiniteSpan_of_operator hf
    (wideLaurentOperatorExistence _ hf hf0)
  refine ⟨L, hLfin, ?_, hLst⟩
  have heq : u = (T (-(n : ℤ)) : R) • restrictWide hf := by
    apply Subtype.ext
    funext z
    change u.val z = puncturedEvaluation z ((T (-(n : ℤ)) : R) • restrictWide hf)
    rw [h z, puncturedEvaluation_smul, eval₂_T, zpow_neg, Units.val_inv_eq_inv_val,
      zpow_natCast, Units.val_pow_eq_pow_val, puncturedEvaluation_apply,
      restrictWide_apply, div_eq_mul_inv, mul_comm]
  exact heq ▸ L.smul_mem _ hLmem

private theorem punctured_exists_divAtOne (u : WidePunctured)
    (h : puncturedEvaluation 1 u = 0) : ∃ v : WidePunctured, π • v = u := by
  obtain ⟨f, hf, n, hu⟩ := u.property
  have hzero : f 1 = 0 := by
    simpa only [puncturedEvaluation_apply, hu, Units.val_one, one_pow, div_one] using h
  obtain ⟨g, hg, hdiv⟩ := wideEFunction_divAtOne hf hzero
  refine ⟨(T (-(n : ℤ)) : R) • restrictWide hg, ?_⟩
  apply Subtype.ext
  funext z
  change puncturedEvaluation z (π • ((T (-(n : ℤ)) : R) • restrictWide hg)) = u.val z
  rw [puncturedEvaluation_smul, puncturedEvaluation_smul, map_sub, map_one, eval₂_T,
    zpow_one, eval₂_T, zpow_neg, Units.val_inv_eq_inv_val, zpow_natCast,
    Units.val_pow_eq_pow_val, puncturedEvaluation_apply, restrictWide_apply, hu z,
    ← hdiv (z : ℂ), div_eq_mul_inv]
  ac_rfl

/-- The division by the fiber parameter takes place inside the differential
submodule. Finiteness is needed only for the span of the ambient quotient
function, which exists by the Laurent differential equation theorem. -/
theorem exists_smul_coordinate_sub_one_of_wideEvaluation_eq_zero
    (M : Submodule R WidePunctured) (hM : ∀ x ∈ M, D x ∈ M)
    (u : M) (hu : puncturedEvaluation 1 u = 0) :
    ∃ v : M, π • v = u := by
  obtain ⟨v, hv⟩ := punctured_exists_divAtOne _ hu
  obtain ⟨L, hLFG, hvL, hL⟩ := punctured_exists_finite_stable_span v
  let N := M.comap L.subtype
  let dL := StrictEUnit.restrictConnection L (D).toLinearMap hL
  have hN (x : L) (hx : x ∈ N) : dL x ∈ N :=
    hM _ hx
  letI : Module.Finite R L := Module.Finite.iff_fg.mpr hLFG
  letI : Module.Finite R (L ⧸ N) := Module.Finite.of_surjective N.mkQ N.mkQ_surjective
  letI : Module.Free R (L ⧸ N) :=
    finiteLaurentDifferentialModuleFree (StrictEUnit.quotientConnection N dL hN)
      (StrictEUnit.quotientConnection_leibniz laurentDerivation N dL hN
        (StrictEUnit.restrictConnection_leibniz laurentDerivation L (D).toLinearMap hL
          widePuncturedDerivation_smul))
  letI : NoZeroSMulDivisors R (L ⧸ N) := (Module.Free.chooseBasis R (L ⧸ N)).noZeroSMulDivisors
  have hπ : π ≠ 0 := by
    intro h
    have hd := congrArg (laurentDerivation (K := k)) h
    simp at hd
  have hvzero : π • N.mkQ ⟨v, hvL⟩ = 0 := by
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change π • v ∈ M
    exact hv ▸ u.property
  have hvN : (⟨v, hvL⟩ : L) ∈ N := by
    have hz := (smul_eq_zero.mp hvzero).resolve_left hπ
    exact (Submodule.Quotient.mk_eq_zero N).mp hz
  exact ⟨⟨v, hvN⟩, Subtype.ext hv⟩

private theorem eval₂_one_eq (p : R) :
    eval₂ (algebraicClosure ℚ ℂ).val.toRingHom 1 p =
      (evalAtOne k p : ℂ) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq, map_add]
    change (algebraMap k ℂ) (evalAtOne k p) + (algebraMap k ℂ) (evalAtOne k q) =
      (algebraMap k ℂ) (evalAtOne k p + evalAtOne k q)
    rw [map_add]
  | C_mul_T n c => simp [evalAtOne_C]

section Evaluation

local instance wideFiberComplexAlgebra : Algebra R ℂ :=
  ((algebraMap k ℂ).comp (evalAtOne k)).toAlgebra

local instance wideFiberComplexTower : IsScalarTower R k ℂ :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private def wideEvaluationLinear (M : Submodule R WidePunctured) : M →ₗ[R] ℂ where
  toFun x := puncturedEvaluation 1 x
  map_add' x y := map_add (puncturedEvaluation 1) (x : WidePunctured) (y : WidePunctured)
  map_smul' p x := by
    change puncturedEvaluation 1 (p • (x : WidePunctured)) =
      ((evalAtOne k p : k) : ℂ) * puncturedEvaluation 1 x
    rw [puncturedEvaluation_smul, eval₂_one_eq]

/-- Evaluation on the ordinary fiber over the algebraic numbers. -/
def wideFiberEvaluation (M : Submodule R WidePunctured) : FiberAtOne k M →ₗ[k] ℂ :=
  TensorProduct.AlgebraTensorModule.lift («R» := R) (A := k) (M := k) (P := ℂ)
    { toFun := fun a => a • wideEvaluationLinear M
      map_add' := fun a b => add_smul a b _
      map_smul' := fun a b => smul_assoc a b _ }

@[simp] theorem wideFiberEvaluation_class (M : Submodule R WidePunctured) (u : M) :
    wideFiberEvaluation M (fiberClass k M u) = puncturedEvaluation 1 u := by
  change (1 : k) • puncturedEvaluation 1 u = _
  rw [one_smul]

end Evaluation

private theorem wideFiberClass_surjective (M : Submodule R WidePunctured) :
    Function.Surjective (fiberClass k M) := by
  intro x
  let e := fiberAtOneEquivQuotient k M
  obtain ⟨u, hu⟩ := Submodule.mkQ_surjective _ (e x)
  exact ⟨u, e.injective ((fiberAtOneEquivQuotient_class k M u).trans hu)⟩

theorem wideFiberEvaluation_injective (M : Submodule R WidePunctured)
    (hM : ∀ x ∈ M, D x ∈ M) : Function.Injective (wideFiberEvaluation M) := by
  have hzero (x : FiberAtOne k M) (hx : wideFiberEvaluation M x = 0) : x = 0 := by
    obtain ⟨u, rfl⟩ := wideFiberClass_surjective M x
    rw [wideFiberEvaluation_class] at hx
    obtain ⟨v, hv⟩ := exists_smul_coordinate_sub_one_of_wideEvaluation_eq_zero M hM u hx
    exact (fiberClass_relation k M (show u - 0 = π • v by rw [sub_zero, hv])).trans
      ((fiberClass k M).map_zero)
  letI : AddCommGroup (FiberAtOne k M) := TensorProduct.addCommGroup
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero
  rw [(wideFiberEvaluation M).map_sub, hxy, sub_self]

theorem wideFiberEvaluation_mul (M : Submodule R WidePunctured)
    (u v : FiberAtOne k M) :
    wideFiberEvaluation (M * M)
        (baseChangeMul k (productMap M) (u ⊗ₜ[k] v)) =
      wideFiberEvaluation M u * wideFiberEvaluation M v := by
  obtain ⟨a, rfl⟩ := wideFiberClass_surjective M u
  obtain ⟨b, rfl⟩ := wideFiberClass_surjective M v
  rw [fiberClass_mul, wideFiberEvaluation_class, wideFiberEvaluation_class,
    wideFiberEvaluation_class, productMap_tmul, map_mul]

/-- The values of a Laurent basis of a stable submodule are linearly
independent over the algebraic numbers. -/
theorem linearIndependent_wideBasisValues {ι : Type*} {M : Submodule R WidePunctured}
    (hM : ∀ x ∈ M, D x ∈ M) (b : Basis ι R M) :
    LinearIndependent k (fun i => puncturedEvaluation 1 (b i : M)) := by
  letI : AddCommGroup (FiberAtOne k M) := TensorProduct.addCommGroup
  letI : Module k (FiberAtOne k M) := TensorProduct.leftModule
  have hker : LinearMap.ker (wideFiberEvaluation M) = ⊥ :=
    (LinearMap.ker_eq_bot (f := wideFiberEvaluation M)).mpr (wideFiberEvaluation_injective M hM)
  have hi := (b.baseChange k).linearIndependent.map' (wideFiberEvaluation M) hker
  convert hi using 1
  funext i
  rw [Function.comp_apply, Basis.baseChange_apply]
  exact (wideFiberEvaluation_class M (b i)).symm

/-- Evaluation of an element is the linear combination of the basis values
with the coefficients specialized at one. -/
theorem puncturedEvaluation_eq_sum_repr {ι : Type*} [Fintype ι]
    {M : Submodule R WidePunctured} (b : Basis ι R M) (x : M) :
    puncturedEvaluation 1 x = ∑ i, evalAtOne k (b.repr x i) • puncturedEvaluation 1 (b i : M) := by
  have h := congrArg (fun u : M => puncturedEvaluation 1 u) (b.sum_repr x)
  change puncturedEvaluation 1 ((∑ i, b.repr x i • b i : M) : WidePunctured) =
    puncturedEvaluation 1 x at h
  rw [Submodule.coe_sum, map_sum] at h
  have hsmul (p : R) (u : M) :
      puncturedEvaluation 1 (↑(p • u) : WidePunctured) =
        evalAtOne k p • puncturedEvaluation 1 u := by
    change puncturedEvaluation 1 (p • (u : WidePunctured)) = _
    rw [puncturedEvaluation_smul, eval₂_one_eq]
    rfl
  simpa only [hsmul] using h.symm

end WideE
