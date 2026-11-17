import WideE.Closure
import ActualStrictEGaloisNorm

/-! Conjugate wide series and their literal finite Galois norm product. -/

noncomputable section

namespace WideE

open StrictEUnit
open scoped BigOperators

/-- Conjugation preserves the coefficient bounds and the same integral
denominators. -/
theorem HasWideEArithmetic.map {a : ℕ → AlgebraicComplex}
    (ha : HasWideEArithmetic a) (σ : AlgebraicComplex →ₐ[ℚ] AlgebraicComplex) :
    HasWideEArithmetic (fun n => σ (a n)) := by
  intro ε hε
  obtain ⟨C, hC, hconj, d, hd, hdb, hint⟩ := ha ε hε
  let v : AlgebraicComplex →ₐ[ℚ] ℂ := (algebraicClosure ℚ ℂ).val
  refine ⟨C, hC, fun τ n => hconj (τ.comp σ) n, d, hd, hdb, ?_⟩
  intro n j hj
  have hi : IsIntegral ℤ ((d n : AlgebraicComplex) * a j) := by
    apply (isIntegral_algHom_iff (v.restrictScalars ℤ) v.injective).mp
    simpa only [map_mul, map_natCast] using hint n j hj
  have hm := IsIntegral.map ((v.comp σ).restrictScalars ℤ) hi
  simpa only [map_mul, map_natCast, AlgHom.comp_apply] using hm

theorem IsWideEFunction.arithmetic_of_expansion {f : ℂ → ℂ}
    (hf : IsWideEFunction f) {a : ℕ → AlgebraicComplex} (hs : HasFactorialExpansion f a) :
    HasWideEArithmetic a := by
  obtain ⟨b, hd, hb, _, hba, _⟩ := hf
  rw [hs.unique hb hd]
  exact hba

/-- The entire factorial series is formed from the coefficients in the chosen
embedding. -/
def factorialSeriesFunction (a : ℕ → AlgebraicComplex) : ℂ → ℂ :=
  exponentialGeneratingFunction (fun n => (a n : ℂ))

theorem HasWideEArithmetic.expansion {a : ℕ → AlgebraicComplex} (ha : HasWideEArithmetic a) :
    HasFactorialExpansion (factorialSeriesFunction a) a := by
  obtain ⟨C, hC, hbound⟩ := ha.chosen_bound (1 / 2) (by norm_num)
  exact fun z => half_factorial_egf_hasSum _ C (zero_le_one.trans hC) hbound z

theorem HasWideEArithmetic.differentiable_factorialSeries {a : ℕ → AlgebraicComplex}
    (ha : HasWideEArithmetic a) : Differentiable ℂ (factorialSeriesFunction a) := by
  obtain ⟨C, hC, hbound⟩ := ha.chosen_bound (1 / 2) (by norm_num)
  exact half_factorial_egf_differentiable _ C (zero_le_one.trans hC) hbound

/-- The source power series is independent of which arithmetic bounds
establish convergence. -/
theorem taylorRealization_factorialSeries {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a : ℕ → AlgebraicComplex} (hs : HasFactorialExpansion f a) :
    subfieldEntireTaylorAlgHom algebraicSubfield (taylorRealization f hf hs) =
      stage41_strictFormalSeries a := by
  apply PowerSeries.ext
  intro n
  change PowerSeries.coeff AlgebraicComplex n
    (subfieldEntireTaylorAlgHom algebraicSubfield (taylorRealization f hf hs)) =
      PowerSeries.coeff AlgebraicComplex n (stage41_strictFormalSeries a)
  rw [taylorRealization_coeff hf hs, stage41_coeff_strictFormalSeries]

/-- The actual entire function formed from a sequence with wide arithmetic. -/
def wideSeriesRealization (a : ℕ → AlgebraicComplex) (ha : HasWideEArithmetic a) :
    subfieldEntireFunctionAlgebra algebraicSubfield :=
  taylorRealization (factorialSeriesFunction a) ha.differentiable_factorialSeries ha.expansion

@[simp] theorem wideSeriesRealization_apply (a : ℕ → AlgebraicComplex)
    (ha : HasWideEArithmetic a) (z : ℂ) :
    (wideSeriesRealization a ha).val.val z = factorialSeriesFunction a z := rfl

@[simp] theorem wideSeriesRealization_taylor (a : ℕ → AlgebraicComplex)
    (ha : HasWideEArithmetic a) :
    subfieldEntireTaylorAlgHom algebraicSubfield (wideSeriesRealization a ha) =
      stage41_strictFormalSeries a :=
  taylorRealization_factorialSeries ha.differentiable_factorialSeries ha.expansion

/-- A formal factorial-series identity gives the same global analytic
polynomial ODE on its actual realization. -/
theorem factorialSeries_polynomial_relation_of_formal {a : ℕ → AlgebraicComplex}
    (ha : HasWideEArithmetic a) (m : ℕ) (p : Fin (m + 1) → Polynomial AlgebraicComplex)
    (h : ∑ i, (p i : PowerSeries AlgebraicComplex) *
      (PowerSeries.derivative AlgebraicComplex)^[i.val] (stage41_strictFormalSeries a) = 0) :
    ∀ z : ℂ, ∑ i, (p i).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z *
      iteratedDeriv i.val (factorialSeriesFunction a) z = 0 := by
  let F := wideSeriesRealization a ha
  let A := subfieldEntireFunctionAlgebra algebraicSubfield
  letI : CommSemiring A := A.toCommSemiring
  letI : Algebra algebraicSubfield A := A.algebra
  letI : Semiring A := CommSemiring.toSemiring
  letI : AddCommMonoid A :=
    (inferInstance : Semiring A).toNonUnitalNonAssocSemiring.toAddCommMonoid
  apply (stage14_actualPolynomialRelation_iff algebraicSubfield F m p).mp
  apply subfieldEntireTaylorAlgHom_injective algebraicSubfield
  simpa only [map_sum, map_zero, map_mul, stage26_subfieldTaylor_iterate,
    stage26_subfieldTaylor_polynomial, F, wideSeriesRealization_taylor] using h

/-- The wide conjugate is an actual function obtained by mapping the factorial
coefficients. The same polynomials transport its formal and analytic ODEs. -/
theorem IsWideEFunction.coefficient_conjugate {f : ℂ → ℂ}
    (hf : IsWideEFunction f) {a : ℕ → AlgebraicComplex} (hs : HasFactorialExpansion f a)
    (σ : AlgebraicComplex →ₐ[ℚ] AlgebraicComplex) :
    IsWideEFunction (factorialSeriesFunction (fun n => σ (a n))) := by
  have hac := (hf.arithmetic_of_expansion hs).map σ
  obtain ⟨_, hd, _, hODE, _⟩ := hf
  obtain ⟨m, p, ⟨i, hi⟩, hformal⟩ := formal_polynomial_ode hd hs hODE
  rw [taylorRealization_factorialSeries hd hs] at hformal
  have hm := ordinaryTuple_equation_map σ.toRingHom m p (stage41_strictFormalSeries a) hformal
  rw [stage41_strictFormalSeries_map] at hm
  exact wideEFunction_of_expansion hac.differentiable_factorialSeries hac.expansion
    ⟨m, fun j => (p j).map σ.toRingHom, ⟨i, (Polynomial.map_ne_zero_iff σ.injective).mpr hi⟩,
      factorialSeries_polynomial_relation_of_formal hac m _ hm⟩ hac

theorem isWideEFunction_finsetProd {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, IsWideEFunction (f i)) : IsWideEFunction (fun z => ∏ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isWideEFunction_const (1 : AlgebraicComplex)
  | @insert i s hi ih =>
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.prod_insert hi] using (hf i (Finset.mem_insert_self i s)).mul hs

section GaloisNorm

variable (K : IntermediateField ℚ AlgebraicComplex)

/-- The norm uses the actual conjugate series indexed by the automorphisms of
the finite coefficient field. -/
def galoisNormFunction [Fintype (K ≃ₐ[ℚ] K)] (a : ℕ → K) : ℂ → ℂ :=
  fun z => ∏ σ : K ≃ₐ[ℚ] K, factorialSeriesFunction
    (fun n => (σ (a n) : AlgebraicComplex)) z

theorem HasWideEArithmetic.galois_conjugate {a : ℕ → K}
    (ha : HasWideEArithmetic (fun n => (a n : AlgebraicComplex))) (σ : K ≃ₐ[ℚ] K) :
    HasWideEArithmetic (fun n => (σ (a n) : AlgebraicComplex)) := by
  have h := ha.map (σ.toAlgHom.liftNormal AlgebraicComplex)
  have heq (n : ℕ) : σ.toAlgHom.liftNormal AlgebraicComplex (a n : AlgebraicComplex) =
      (σ (a n) : AlgebraicComplex) :=
    σ.toAlgHom.liftNormal_commutes AlgebraicComplex (a n)
  simpa only [heq] using h

theorem IsWideEFunction.galois_conjugate {a : ℕ → K}
    {f : ℂ → ℂ} (hf : IsWideEFunction f)
    (hs : HasFactorialExpansion f (fun n => (a n : AlgebraicComplex))) (σ : K ≃ₐ[ℚ] K) :
    IsWideEFunction (factorialSeriesFunction (fun n => (σ (a n) : AlgebraicComplex))) := by
  have h := hf.coefficient_conjugate hs (σ.toAlgHom.liftNormal AlgebraicComplex)
  have heq (n : ℕ) : σ.toAlgHom.liftNormal AlgebraicComplex (a n : AlgebraicComplex) =
      (σ (a n) : AlgebraicComplex) :=
    σ.toAlgHom.liftNormal_commutes AlgebraicComplex (a n)
  simpa only [heq] using h

variable [Fintype (K ≃ₐ[ℚ] K)]

local instance normEntireRing : CommRing (subfieldEntireFunctionAlgebra algebraicSubfield) :=
  (subfieldEntireFunctionAlgebra algebraicSubfield).toCommRing

local instance normEntireMonoid : CommMonoid (subfieldEntireFunctionAlgebra algebraicSubfield) :=
  (subfieldEntireFunctionAlgebra algebraicSubfield).toCommRing.toCommMonoid

/-- The Taylor series of the actual norm is the coefficient extension of the
literal product in the finite Galois field. -/
theorem galoisNorm_realization (a : ℕ → K)
    (ha : HasWideEArithmetic (fun n => (a n : AlgebraicComplex))) :
    ∃ G : subfieldEntireFunctionAlgebra algebraicSubfield,
      G.val.val = galoisNormFunction K a ∧
      subfieldEntireTaylorAlgHom algebraicSubfield G = PowerSeries.map K.val.toRingHom
        (∏ σ : K ≃ₐ[ℚ] K, PowerSeries.map σ.toRingHom
          (PowerSeries.mk (fun n => a n / (n.factorial : K)))) := by
  classical
  let B (σ : K ≃ₐ[ℚ] K) :=
    wideSeriesRealization (fun n => (σ (a n) : AlgebraicComplex)) (ha.galois_conjugate K σ)
  refine ⟨∏ σ, B σ, ?_, ?_⟩
  · funext z
    change stage14_subfieldEntireEvaluation algebraicSubfield z (∏ σ, B σ) =
      ∏ σ, stage14_subfieldEntireEvaluation algebraicSubfield z (B σ)
    exact map_prod _ _ _
  · rw [map_prod, map_prod]
    apply Finset.prod_congr rfl
    intro σ _
    rw [show subfieldEntireTaylorAlgHom algebraicSubfield (B σ) =
      stage41_strictFormalSeries (fun n => (σ (a n) : AlgebraicComplex)) from
      wideSeriesRealization_taylor _ _]
    ext n
    simp only [PowerSeries.coeff_map, stage41_coeff_strictFormalSeries,
      PowerSeries.coeff_mk, map_div₀, map_natCast]
    rfl

/-- The norm product is wide, has a rational factorial expansion, preserves
nonzeroness and inherits a zero at one from its identity factor. -/
theorem galoisNorm_properties [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (a : ℕ → K) {f : ℂ → ℂ} (hf : IsWideEFunction f)
    (hs : HasFactorialExpansion f (fun n => (a n : AlgebraicComplex))) :
    IsWideEFunction (galoisNormFunction K a) ∧
      (∃ c : ℕ → ℚ, HasFactorialExpansion (galoisNormFunction K a)
        (fun n => algebraMap ℚ AlgebraicComplex (c n))) ∧
      (f ≠ 0 → galoisNormFunction K a ≠ 0) ∧
      (f 1 = 0 → galoisNormFunction K a 1 = 0) := by
  classical
  have hg : IsWideEFunction (galoisNormFunction K a) := by
    unfold galoisNormFunction
    exact isWideEFunction_finsetProd (Finset.univ : Finset (K ≃ₐ[ℚ] K))
      (fun σ => factorialSeriesFunction (fun n => (σ (a n) : AlgebraicComplex)))
      (fun σ _ => hf.galois_conjugate K hs σ)
  let x : PowerSeries K := PowerSeries.mk (fun n => a n / (n.factorial : K))
  let P : PowerSeries K := ∏ σ : K ≃ₐ[ℚ] K, PowerSeries.map σ.toRingHom x
  obtain ⟨G, hGval, hT⟩ := galoisNorm_realization K a (hf.arithmetic_of_expansion hs)
  change subfieldEntireTaylorAlgHom algebraicSubfield G = PowerSeries.map K.val.toRingHom P at hT
  refine ⟨hg, ?_, ?_, ?_⟩
  · choose q hq using fun n => finiteGalois_product_coeff_rational x n
    have hcoeffA (n : ℕ) :
        PowerSeries.coeff AlgebraicComplex n (subfieldEntireTaylorAlgHom algebraicSubfield G) =
          algebraMap ℚ AlgebraicComplex (q n) := by
      rw [hT, PowerSeries.coeff_map, ← hq n]
      exact K.val.commutes (q n)
    have hcoeffC (n : ℕ) :
        entireCauchyCoefficient (galoisNormFunction K a) n = (q n : ℂ) := by
      have hh := congrArg (algebraicClosure ℚ ℂ).val (hcoeffA n)
      simpa only [subfieldEntireTaylorAlgHom_apply, subfieldEntireTaylorSeries,
        PowerSeries.coeff_mk, AlgHom.commutes, hGval] using hh
    refine ⟨fun n => q n * (n.factorial : ℚ), fun z => ?_⟩
    convert entireCauchyCoefficient_hasSum hg.differentiable z using 1
    funext n
    rw [hcoeffC n]
    have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    change ((q n * (n.factorial : ℚ) : ℚ) : ℂ) * z ^ n / (n.factorial : ℂ) = _
    push_cast
    field_simp [hn]
    ring
  · intro hfne hgzero
    have hx : x ≠ 0 := by
      intro hxzero
      have hazero (n : ℕ) : a n = 0 := by
        have hh := congrArg (PowerSeries.coeff K n) hxzero
        have hh' : a n / (n.factorial : K) = 0 := by
          simpa only [x, PowerSeries.coeff_mk, map_zero] using hh
        exact (div_eq_zero_iff.mp hh').resolve_right
          (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
      apply hfne
      funext z
      have hz : HasSum (fun _ : ℕ => (0 : ℂ)) (f z) := by
        simpa [hazero] using hs z
      exact hz.unique hasSum_zero
    have hP : P ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro σ _ hzero
      apply hx
      apply PowerSeries.map_injective σ.toRingHom σ.injective
      simpa only [map_zero] using hzero
    have hGzero : G = 0 := Subtype.ext (Subtype.ext (hGval.trans hgzero))
    apply hP
    apply PowerSeries.map_injective K.val.toRingHom K.val.injective
    rw [map_zero, ← hT, hGzero, map_zero]
  · intro hfzero
    have hidfun : factorialSeriesFunction (fun n => (a n : AlgebraicComplex)) = f := by
      funext z
      exact ((hf.arithmetic_of_expansion hs).expansion z).unique (hs z)
    unfold galoisNormFunction
    apply Finset.prod_eq_zero (Finset.mem_univ (1 : K ≃ₐ[ℚ] K))
    rw [show (fun n => (((1 : K ≃ₐ[ℚ] K) (a n)) : AlgebraicComplex)) =
      (fun n => (a n : AlgebraicComplex)) from rfl, hidfun, hfzero]

end GaloisNorm

end WideE
