import WideE.Closure
import WideE.Laurent
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Wide numerators with a possible pole at the origin, realized as actual
functions on the punctured plane. -/

open scoped Topology
open Filter

noncomputable section

namespace WideE

abbrev PuncturedFunction := ℂˣ → ℂ

/-- A power of the coordinate clears the pole and leaves a wide entire function. -/
def HasWideNumerator (u : PuncturedFunction) : Prop :=
  ∃ f : ℂ → ℂ, IsWideEFunction f ∧ ∃ n : ℕ, ∀ z : ℂˣ, u z = f z / (z : ℂ) ^ n

theorem HasWideNumerator.ofEntire {f : ℂ → ℂ} (hf : IsWideEFunction f) :
    HasWideNumerator (fun z => f z) :=
  ⟨f, hf, 0, fun z => by simp⟩

private theorem wideCoordinate_pow (n : ℕ) : IsWideEFunction (fun z : ℂ => z ^ n) := by
  simpa only [Polynomial.eval₂_X_pow] using isWideEFunction_polynomial (Polynomial.X ^ n)

theorem HasWideNumerator.add {u v : PuncturedFunction} (hu : HasWideNumerator u)
    (hv : HasWideNumerator v) : HasWideNumerator (u + v) := by
  obtain ⟨f, hf, m, huf⟩ := hu
  obtain ⟨g, hg, n, hvg⟩ := hv
  refine ⟨_, (hf.mul (wideCoordinate_pow n)).add (hg.mul (wideCoordinate_pow m)),
    m + n, fun z => ?_⟩
  change u z + v z = (f z * (z : ℂ) ^ n + g z * (z : ℂ) ^ m) / (z : ℂ) ^ (m + n)
  rw [huf, hvg, pow_add]
  simpa only [mul_comm ((z : ℂ) ^ m) (g z)] using
    div_add_div (f z) (g z) (pow_ne_zero m z.ne_zero) (pow_ne_zero n z.ne_zero)

theorem HasWideNumerator.mul {u v : PuncturedFunction} (hu : HasWideNumerator u)
    (hv : HasWideNumerator v) : HasWideNumerator (u * v) := by
  obtain ⟨f, hf, m, huf⟩ := hu
  obtain ⟨g, hg, n, hvg⟩ := hv
  refine ⟨_, hf.mul hg, m + n, fun z => ?_⟩
  change u z * v z = f z * g z / (z : ℂ) ^ (m + n)
  rw [huf, hvg, pow_add, div_mul_div_comm]

private def extendByZero (u : PuncturedFunction) (z : ℂ) : ℂ :=
  if hz : z = 0 then 0 else u (Units.mk0 z hz)

private theorem extendByZero_mk0 (u : PuncturedFunction) (z : ℂ) (hz : z ≠ 0) :
    extendByZero u z = u (Units.mk0 z hz) := dif_neg hz

private theorem extendByZero_eventuallyEq {u : PuncturedFunction} {f : ℂ → ℂ}
    (h : ∀ w : ℂˣ, u w = f w) (z : ℂˣ) : extendByZero u =ᶠ[𝓝 (z : ℂ)] f := by
  filter_upwards [continuous_id.continuousAt.eventually_ne z.ne_zero] with w hw
  rw [extendByZero_mk0 u w hw]
  exact h (Units.mk0 w hw)

/-- The ordinary complex derivative at a point of the punctured plane. -/
def puncturedDerivative (u : PuncturedFunction) (z : ℂˣ) : ℂ :=
  deriv (extendByZero u) (z : ℂ)

theorem puncturedDerivative_of_restriction {u : PuncturedFunction} {f : ℂ → ℂ}
    (h : ∀ w : ℂˣ, u w = f w) (z : ℂˣ) : puncturedDerivative u z = deriv f z :=
  (extendByZero_eventuallyEq h z).deriv_eq

private theorem HasWideNumerator.differentiableAt {u : PuncturedFunction}
    (hu : HasWideNumerator u) (z : ℂˣ) : DifferentiableAt ℂ (extendByZero u) (z : ℂ) := by
  obtain ⟨f, hf, n, h⟩ := hu
  refine (extendByZero_eventuallyEq (f := fun w : ℂ => f w / w ^ n) h z).differentiableAt_iff.mpr ?_
  exact hf.differentiable.differentiableAt.div (differentiableAt_id.pow n) (pow_ne_zero n z.ne_zero)

theorem HasWideNumerator.derivative {u : PuncturedFunction} (hu : HasWideNumerator u) :
    HasWideNumerator (puncturedDerivative u) := by
  obtain ⟨f, hf, n, h⟩ := hu
  refine ⟨_, (hf.derivative.mul (wideCoordinate_pow n)).sub
    (hf.mul ((wideCoordinate_pow (n - 1)).const_mul (n : AlgebraicComplex))),
    n * 2, fun z => ?_⟩
  have hpow : DifferentiableAt ℂ (fun w : ℂ => w ^ n) (z : ℂ) := differentiableAt_id.pow n
  rw [puncturedDerivative_of_restriction (f := fun w : ℂ => f w / w ^ n) h,
    deriv_div hf.differentiable.differentiableAt hpow (pow_ne_zero n z.ne_zero), deriv_pow, pow_mul]
  rw [show ((n : AlgebraicComplex) : ℂ) = (n : ℂ) from
    map_natCast (algebraicClosure ℚ ℂ).val.toRingHom n]

/-- The actual Laurent ambient algebra used for the finite spans. -/
def widePuncturedAlgebra : Subalgebra AlgebraicComplex PuncturedFunction where
  carrier := {u | HasWideNumerator u}
  zero_mem' := HasWideNumerator.ofEntire (isWideEFunction_const 0)
  one_mem' := HasWideNumerator.ofEntire (isWideEFunction_const 1)
  add_mem' := HasWideNumerator.add
  mul_mem' := HasWideNumerator.mul
  algebraMap_mem' α := HasWideNumerator.ofEntire (isWideEFunction_const α)

abbrev WidePunctured := ↥widePuncturedAlgebra

instance (priority := 2000) : CommRing WidePunctured := widePuncturedAlgebra.toCommRing
instance (priority := 2000) : Algebra AlgebraicComplex WidePunctured := widePuncturedAlgebra.algebra

instance (priority := 2000) : AddCommGroup WidePunctured := widePuncturedAlgebra.toRing.toAddCommGroup
instance (priority := 2000) : AddCommMonoid WidePunctured := widePuncturedAlgebra.toSemiring.toAddCommMonoid
instance (priority := 2000) : Module AlgebraicComplex WidePunctured := Algebra.toModule
instance (priority := 2000) : Module WidePunctured WidePunctured := Semiring.toModule
instance (priority := 2000) : SMul AlgebraicComplex WidePunctured := Algebra.toSMul
instance (priority := 2000) : Mul WidePunctured := widePuncturedAlgebra.toSemiring.toMul

/-- The same entire function regarded as a function on the punctured plane. -/
def restrictWide {f : ℂ → ℂ} (hf : IsWideEFunction f) : WidePunctured :=
  ⟨fun z => f z, HasWideNumerator.ofEntire hf⟩

@[simp] theorem restrictWide_apply {f : ℂ → ℂ} (hf : IsWideEFunction f) (z : ℂˣ) :
    (restrictWide hf).val z = f z := rfl

set_option maxHeartbeats 750000 in
/-- A genuine derivation on actual punctured functions. Its construction uses
only the complex derivative in neighborhoods of nonzero points. -/
def widePuncturedDerivation : Derivation AlgebraicComplex WidePunctured WidePunctured :=
  Derivation.mk'
    { toFun := fun u => ⟨puncturedDerivative u.val, HasWideNumerator.derivative u.property⟩
      map_add' := by
        intro u v
        apply Subtype.ext
        funext z
        have h (w : ℂˣ) : (u + v).val w = extendByZero u.val w + extendByZero v.val w := by
          rw [extendByZero_mk0 u.val w w.ne_zero, extendByZero_mk0 v.val w w.ne_zero]
          rw [Units.mk0_val]
          rfl
        exact (puncturedDerivative_of_restriction (f := extendByZero u.val + extendByZero v.val) h z).trans
          (deriv_add (HasWideNumerator.differentiableAt u.property z)
            (HasWideNumerator.differentiableAt v.property z))
      map_smul' := by
        intro c u
        apply Subtype.ext
        funext z
        have h (w : ℂˣ) : (c • u).val w = (c : ℂ) * extendByZero u.val w := by
          rw [extendByZero_mk0 u.val w w.ne_zero]
          rw [Units.mk0_val]
          rfl
        exact (puncturedDerivative_of_restriction
          (f := fun w : ℂ => (c : ℂ) * extendByZero u.val w) h z).trans (deriv_const_mul_field _) }
    (by
      intro u v
      apply Subtype.ext
      funext z
      have h (w : ℂˣ) : (u * v).val w = extendByZero u.val w * extendByZero v.val w := by
        rw [extendByZero_mk0 u.val w w.ne_zero, extendByZero_mk0 v.val w w.ne_zero]
        rw [Units.mk0_val]
        rfl
      change puncturedDerivative (u * v).val z =
        u.val z * puncturedDerivative v.val z + v.val z * puncturedDerivative u.val z
      rw [puncturedDerivative_of_restriction
        (f := fun w : ℂ => extendByZero u.val w * extendByZero v.val w) h z,
        deriv_mul (HasWideNumerator.differentiableAt u.property z)
          (HasWideNumerator.differentiableAt v.property z)]
      simp only [puncturedDerivative]
      rw [extendByZero_mk0 u.val z z.ne_zero, extendByZero_mk0 v.val z z.ne_zero]
      rw [Units.mk0_val]
      ac_rfl)

@[simp] theorem widePuncturedDerivation_restrict {f : ℂ → ℂ} (hf : IsWideEFunction f) :
    widePuncturedDerivation (restrictWide hf) = restrictWide hf.derivative := by
  apply Subtype.ext
  funext z
  exact puncturedDerivative_of_restriction (f := f) (fun _ => rfl) z

@[simp] theorem widePuncturedDerivation_iterate {f : ℂ → ℂ} (hf : IsWideEFunction f) (n : ℕ) :
    widePuncturedDerivation^[n] (restrictWide hf) = restrictWide (hf.iteratedDeriv n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, widePuncturedDerivation_restrict]
    apply Subtype.ext
    funext z
    exact (congrFun (iteratedDeriv_succ (n := n) (f := f)) z).symm

open LaurentPolynomial

private def puncturedCoordinateUnit : WidePuncturedˣ where
  val := restrictWide isWideEFunction_coordinate
  inv := ⟨fun z => (z : ℂ)⁻¹, ⟨fun _ => 1, isWideEFunction_const 1, 1, fun z => by simp⟩⟩
  val_inv := Subtype.ext (funext fun z => mul_inv_cancel₀ z.ne_zero)
  inv_val := Subtype.ext (funext fun z => inv_mul_cancel₀ z.ne_zero)

/-- The scalar action of Laurent polynomials is evaluation at the actual coordinate. -/
def puncturedLaurentEmbedding : LaurentPolynomial AlgebraicComplex →ₐ[AlgebraicComplex]
    WidePunctured where
  toRingHom := eval₂ (algebraMap AlgebraicComplex WidePunctured) puncturedCoordinateUnit
  commutes' c := by
    change eval₂ _ _ (algebraMap _ _ c) = _
    rw [← LaurentPolynomial.C_eq_algebraMap, eval₂_C]

scoped instance puncturedLaurentAlgebra : Algebra (LaurentPolynomial AlgebraicComplex) WidePunctured :=
  puncturedLaurentEmbedding.toRingHom.toAlgebra

scoped instance (priority := 2000) puncturedLaurentModule :
    Module (LaurentPolynomial AlgebraicComplex) WidePunctured := Algebra.toModule

scoped instance puncturedLaurentTower :
    IsScalarTower AlgebraicComplex (LaurentPolynomial AlgebraicComplex) WidePunctured :=
  IsScalarTower.of_algebraMap_eq fun c => (puncturedLaurentEmbedding.commutes c).symm

@[simp] theorem puncturedLaurentEmbedding_coordinate :
    puncturedLaurentEmbedding (T 1) = restrictWide isWideEFunction_coordinate := by
  change eval₂ _ _ (T 1) = _
  rw [eval₂_T, zpow_one]
  rfl

@[simp] theorem puncturedLaurentEmbedding_derivation (p : LaurentPolynomial AlgebraicComplex) :
    widePuncturedDerivation (puncturedLaurentEmbedding p) =
      puncturedLaurentEmbedding (laurentDerivation p) := by
  rw [laurentDerivation_chain, puncturedLaurentEmbedding_coordinate,
    widePuncturedDerivation_restrict]
  have h : restrictWide isWideEFunction_coordinate.derivative = 1 :=
    Subtype.ext (funext fun z : ℂˣ => congrFun deriv_id'' (z : ℂ))
  rw [h, one_mul]

def puncturedEvaluation (z : ℂˣ) : WidePunctured →ₐ[AlgebraicComplex] ℂ :=
  (Pi.evalAlgHom AlgebraicComplex (fun _ : ℂˣ => ℂ) z).comp widePuncturedAlgebra.val

@[simp] theorem puncturedEvaluation_apply (z : ℂˣ) (f : WidePunctured) :
    puncturedEvaluation z f = f.val z := rfl

theorem puncturedLaurentEmbedding_eval (z : ℂˣ) (p : LaurentPolynomial AlgebraicComplex) :
    puncturedEvaluation z (puncturedLaurentEmbedding p) =
      eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z p := by
  let e := puncturedEvaluation z
  have hunit : Units.map e.toRingHom.toMonoidHom puncturedCoordinateUnit = z := Units.ext rfl
  change e (eval₂ (algebraMap _ _) puncturedCoordinateUnit p) = _
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [(eval₂ (algebraMap AlgebraicComplex WidePunctured) puncturedCoordinateUnit).map_add,
      (eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z).map_add, ← hp, ← hq]
    rfl
  | C_mul_T n c =>
    simp only [map_mul, eval₂_C, eval₂_T, e.commutes]
    change (c : ℂ) * (((Units.map e.toRingHom.toMonoidHom (puncturedCoordinateUnit ^ n)) : ℂˣ) : ℂ) = _
    rw [map_zpow, hunit]
    rfl

end WideE
