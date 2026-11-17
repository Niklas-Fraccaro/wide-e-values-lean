import WideE.ArithmeticLifting
import WideE.Conjugates
import WideE.Division
import ActualLinearLiftingFromScalar
import OrdinaryRegularDenominatorClearing
import ActualStrictEConjugateBlocks
import ActualRationalProductQuotientOperator
import ActualBlockQuotientContradiction

/-! Ordinary scalar nonvanishing and exact linear lifting from the wide
Laurent-operator assertion. The argument uses the literal product of
the Galois conjugate functions and the ordinary operator of its quotient. -/

noncomputable section

set_option maxHeartbeats 1400000

namespace WideE

open StrictEUnit
open scoped BigOperators Matrix
attribute [local instance 2000] Algebra.toModule

local instance actualEntireCommRing (k : Subfield ℂ) :
    CommRing (subfieldEntireFunctionAlgebra k) :=
  (subfieldEntireFunctionAlgebra k).toCommRing

local instance actualEntireAddCommMonoid (k : Subfield ℂ) :
    AddCommMonoid (subfieldEntireFunctionAlgebra k) :=
  @NonUnitalNonAssocSemiring.toAddCommMonoid _ <|
    @NonAssocSemiring.toNonUnitalNonAssocSemiring _ <|
      @Semiring.toNonAssocSemiring _ (subfieldEntireFunctionAlgebra k).toCommSemiring.toSemiring

local instance actualEntireMul (k : Subfield ℂ) :
    Mul (subfieldEntireFunctionAlgebra k) :=
  @MulZeroClass.toMul _ <| @NonUnitalNonAssocSemiring.toMulZeroClass _ <|
    @NonAssocSemiring.toNonUnitalNonAssocSemiring _ <|
      @Semiring.toNonAssocSemiring _ (subfieldEntireFunctionAlgebra k).toCommSemiring.toSemiring

private def conjugateDerivativePrefix (a : ℕ → AlgebraicComplex)
    (ha : HasWideEArithmetic a) (σ : AlgebraicComplex ≃ₐ[ℚ] AlgebraicComplex) (r : ℕ) :
    Fin r → subfieldEntireFunctionAlgebra algebraicSubfield :=
  fun i => (subfieldEntireFunctionDerivation algebraicSubfield)^[i.val]
    (wideSeriesRealization (fun n => σ (a n)) (ha.map σ.toAlgHom))

private theorem conjugateDerivativePrefix_taylor (a : ℕ → AlgebraicComplex)
    (ha : HasWideEArithmetic a) (σ : AlgebraicComplex ≃ₐ[ℚ] AlgebraicComplex)
    (r : ℕ) (i : Fin r) :
    subfieldEntireTaylorAlgHom algebraicSubfield (conjugateDerivativePrefix a ha σ r i) =
      ordinaryDerivativePrefix r (PowerSeries.map σ.toRingHom (stage41_strictFormalSeries a)) i := by
  unfold conjugateDerivativePrefix ordinaryDerivativePrefix
  rw [stage26_subfieldTaylor_iterate, wideSeriesRealization_taylor, stage41_strictFormalSeries_map]
  rfl

/-- Independence of the derivative prefix is preserved coefficientwise. -/
private theorem conjugateDerivativePrefix_independent (a : ℕ → AlgebraicComplex)
    (ha : HasWideEArithmetic a) (σ : AlgebraicComplex ≃ₐ[ℚ] AlgebraicComplex)
    (r : ℕ) (b : Fin r → RatFunc AlgebraicComplex)
    (hdata : OrdinaryBorelMinimalCyclicData
      (HahnSeries.ofPowerSeries ℤ AlgebraicComplex (stage41_strictFormalSeries a)) r b) :
    LinearIndependent (RatFunc AlgebraicComplex) (fun i : Fin r =>
      (show LaurentSeries AlgebraicComplex from stage14_subfieldEntireLaurentAlgHom algebraicSubfield
        (conjugateDerivativePrefix a ha σ r i))) := by
  have heq (i : Fin r) : stage14_subfieldEntireLaurentAlgHom algebraicSubfield
      (conjugateDerivativePrefix a ha σ r i) =
        coefficientLaurentHom σ.toRingHom
          ((laurentOrdinaryDerivation : LaurentSeries AlgebraicComplex → LaurentSeries AlgebraicComplex)^[i.val]
            (HahnSeries.ofPowerSeries ℤ AlgebraicComplex (stage41_strictFormalSeries a))) := by
    rw [stage14_subfieldEntireLaurentAlgHom_apply, conjugateDerivativePrefix_taylor,
      coefficientLaurentHom_iterate_derivative, coefficientLaurentHom_ofPowerSeries,
      laurentOrdinaryDerivation_iterate_ofPowerSeries]
    rfl
  simpa only [heq] using coefficientConjugate_linearIndependent σ.toRingEquiv _ hdata.1

/-- The cleared equation for each actual conjugate comes from the mapped
formal equation. -/
private theorem conjugateDerivativePrefix_cleared (a : ℕ → AlgebraicComplex)
    (ha : HasWideEArithmetic a) (σ : AlgebraicComplex ≃ₐ[ℚ] AlgebraicComplex)
    (r : ℕ) (b : Fin r → RatFunc AlgebraicComplex)
    (hdata : OrdinaryBorelMinimalCyclicData
      (HahnSeries.ofPowerSeries ℤ AlgebraicComplex (stage41_strictFormalSeries a)) r b)
    (T : Polynomial AlgebraicComplex)
    (U : Matrix (Fin r) (Fin r) (Polynomial AlgebraicComplex))
    (hclear : ∀ i j, algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) (U i j) =
      algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) T *
        minimalDerivativeCompanion r b i j) :
    ∀ i, Polynomial.aeval (subfieldEntireCoordinate algebraicSubfield)
          (show Polynomial algebraicSubfield from T.map σ.toRingHom) *
        subfieldEntireFunctionDerivation algebraicSubfield (conjugateDerivativePrefix a ha σ r i) =
      ∑ j, Polynomial.aeval (subfieldEntireCoordinate algebraicSubfield)
          (show Polynomial algebraicSubfield from (U i j).map σ.toRingHom) *
          conjugateDerivativePrefix a ha σ r j := by
  have hs := (minimal_companion_powerSeries_clearing (stage41_strictFormalSeries a) r b hdata T U hclear).2
  have hm := coefficientMapped_powerSeries_cleared σ.toRingHom
    (ordinaryDerivativePrefix r (stage41_strictFormalSeries a)) T U hs
  intro i
  apply subfieldEntireTaylorAlgHom_injective algebraicSubfield
  simp only [map_mul, map_sum, stage26_subfieldTaylor_polynomial,
    subfieldEntireTaylorAlgHom_derivation, conjugateDerivativePrefix_taylor]
  simpa only [ordinaryDerivativePrefix, ordinaryBorel_map_iterate_derivative] using hm i

private theorem inverseLinear_cancel
    {K : Type*} [Field K] (F G : LaurentSeries K)
    (hmul : algebraMap (Polynomial K) (LaurentSeries K) (Polynomial.X - Polynomial.C (1 : K)) * G = F) :
    algebraMap (RatFunc K) (LaurentSeries K) (ordinaryPointInverseLinear (1 : K)) * F = G := by
  have hne : algebraMap (Polynomial K) (LaurentSeries K) (Polynomial.X - Polynomial.C (1 : K)) ≠ 0 := by
    simpa only [map_zero] using
      (Polynomial.algebraMap_hahnSeries_injective (Γ := ℤ) (R := K)).ne
        (Polynomial.X_sub_C_ne_zero (1 : K))
  dsimp only [ordinaryPointInverseLinear]
  rw [map_inv₀, ← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K),
    ← hmul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- The ordinary operator of the actual wide quotient is an operator on the
literal scaled product used by the ordinary gauge argument. -/
private theorem rational_product_quotient_ordinary_annihilator
    (hLaurent : WideLaurentOperatorExistence) {ι S : Type*} [Fintype S]
    (F : ι → subfieldEntireFunctionAlgebra algebraicSubfield)
    (idx : S → ι) {H : ℂ → ℂ} (hH : IsWideEFunction H) (hHne : H ≠ 0)
    (c : ℕ → ℚ)
    (hs : HasFactorialExpansion H (fun n => algebraMap ℚ AlgebraicComplex (c n))) (hzero : H 1 = 0)
    (hprod : ∀ z, (∏ s, (F (idx s)).val.val z) = H z) :
    ∃ m : ℕ, ∃ p : Fin (m + 1) → Polynomial algebraicSubfield,
      (p (Fin.last m)).eval 1 ≠ 0 ∧
        (∑ i, algebraMap (Polynomial algebraicSubfield) (LaurentSeries algebraicSubfield) (p i) *
          (laurentOrdinaryDerivation : LaurentSeries algebraicSubfield →
            LaurentSeries algebraicSubfield)^[i.val]
            (algebraMap (RatFunc algebraicSubfield) (LaurentSeries algebraicSubfield)
              (ordinaryPointInverseLinear (1 : algebraicSubfield)) *
            ∏ s, stage14_subfieldEntireLaurentAlgHom algebraicSubfield (F (idx s)))) = 0 := by
  classical
  obtain ⟨g, hg, hmul⟩ := wideEFunction_divAtOne_of_rational_representation hH
    (fun n => algebraMap ℚ AlgebraicComplex (c n)) (fun n => ⟨c n, rfl⟩) hs hzero
  have hgNe : g ≠ 0 := by
    intro hg0
    apply hHne
    funext z
    simpa only [hg0, Pi.zero_apply, mul_zero] using (hmul z).symm
  obtain ⟨m, p, hOrd, hEq⟩ := (hLaurent g hg hgNe).polynomialAnnihilator hg
  refine ⟨m, p, hOrd, ?_⟩
  obtain ⟨a, hd, hsg, _⟩ := hg
  let H₀ := taylorRealization H hH.differentiable hs
  let G := taylorRealization g hd hsg
  have hprodL := actual_entire_product_laurent_same_source algebraicSubfield F idx H₀ hprod
  have hmulL := actual_polynomial_mul_laurent_same_source algebraicSubfield H₀ G
    (Polynomial.X - Polynomial.C (1 : algebraicSubfield))
    (by intro z; simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_C, Polynomial.eval₂_one, map_one] using hmul z)
  rw [hprodL, inverseLinear_cancel _ _ hmulL]
  exact actual_polynomial_relation_laurent_same_tuple algebraicSubfield G m p hEq

/-- Ordinary minimal derivative data for the chosen expansion of a nonzero
wide function rule out vanishing at one. -/
def WideRegularMinimalNonvanishingAtOne : Prop :=
  ∀ (f : ℂ → ℂ), IsWideEFunction f → f ≠ 0 →
    ∀ (a : ℕ → AlgebraicComplex), HasFactorialExpansion f a →
      ∀ (r : ℕ), 0 < r → ∀ (b : Fin r → RatFunc AlgebraicComplex),
        OrdinaryBorelMinimalCyclicData
          (HahnSeries.ofPowerSeries ℤ AlgebraicComplex (stage41_strictFormalSeries a)) r b →
        (∀ i, ∃ S : PowerSeries AlgebraicComplex,
          HahnSeries.ofPowerSeries ℤ AlgebraicComplex S = ordinaryPointRationalMap 1 (b i)) →
        f 1 ≠ 0

private theorem nonvanishing_from_galois_blocks (hLaurent : WideLaurentOperatorExistence)
    (K : IntermediateField ℚ AlgebraicComplex)
    [FiniteDimensional ℚ K] [IsGalois ℚ K] [Fintype (K ≃ₐ[ℚ] K)]
    (a : ℕ → K) {f : ℂ → ℂ} (hf : IsWideEFunction f) (hfne : f ≠ 0)
    (hs : HasFactorialExpansion f (fun n => (a n : AlgebraicComplex)))
    (r : ℕ) (hr : 0 < r) (b : Fin r → RatFunc AlgebraicComplex)
    (hmin : OrdinaryBorelMinimalCyclicData
      (HahnSeries.ofPowerSeries ℤ AlgebraicComplex
        (stage41_strictFormalSeries (fun n => (a n : AlgebraicComplex)))) r b)
    (T : Polynomial AlgebraicComplex)
    (U : Matrix (Fin r) (Fin r) (Polynomial AlgebraicComplex))
    (hT : T.eval 1 ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) (U i j) =
      algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) T *
        minimalDerivativeCompanion r b i j) : f 1 ≠ 0 := by
  classical
  intro hzero
  let k := algebraicSubfield
  let I := Fin r × (K ≃ₐ[ℚ] K)
  let N := Fintype.card I
  let e : I ≃ Fin N := Fintype.equivFin I
  have ha : HasWideEArithmetic (fun n => (a n : AlgebraicComplex)) := hf.arithmetic_of_expansion hs
  let F₀ : I → subfieldEntireFunctionAlgebra k :=
    fun i => conjugateDerivativePrefix (fun n => (a n : AlgebraicComplex)) ha
      (strictEGaloisCoefficientLift K i.2) r i.1
  let A₀ : Matrix I I (RatFunc k) := strictEGaloisBlockCompanion K r b
  let t : Polynomial k := strictEGaloisCommonClearing K T
  let U₀ : Matrix I I (Polynomial k) := strictEGaloisClearedBlockMatrix K T U
  let F : Fin N → subfieldEntireFunctionAlgebra k := fun i => F₀ (e.symm i)
  let A : Matrix (Fin N) (Fin N) (RatFunc k) := fun i j => A₀ (e.symm i) (e.symm j)
  let V : Matrix (Fin N) (Fin N) (Polynomial k) := fun i j => U₀ (e.symm i) (e.symm j)
  let block : Fin N → (K ≃ₐ[ℚ] K) := fun i => (e.symm i).2
  let idx : (K ≃ₐ[ℚ] K) → Fin N := fun σ => e (⟨0, hr⟩, σ)
  have ht : t.eval 1 ≠ 0 := strictEGaloisCommonClearing_ordinaryAtOne K T hT
  have hV (i j : Fin N) : algebraMap (Polynomial k) (RatFunc k) (V i j) =
      algebraMap (Polynomial k) (RatFunc k) t * A i j :=
    strictEGaloisBlockCompanion_clearing K b T U hclear (e.symm i) (e.symm j)
  have hactual : ∀ i, Polynomial.aeval (subfieldEntireCoordinate k) t *
      subfieldEntireFunctionDerivation k (F i) =
        ∑ j, Polynomial.aeval (subfieldEntireCoordinate k) (V i j) * F j := by
    apply actualEntire_cleared_reindex e k F₀ t U₀
    exact finiteBlock_actual_cleared k (fun σ i => F₀ (i, σ))
      (strictEGaloisBlockDenominator K T)
      (fun σ i j => algebraicCoefficientPolynomialMap (strictEGaloisCoefficientLift K σ) (U i j))
      (fun σ => conjugateDerivativePrefix_cleared (fun n => (a n : AlgebraicComplex)) ha
        (strictEGaloisCoefficientLift K σ) r b hmin T U hclear)
  have hsystem : ∀ i, laurentOrdinaryDerivation (stage14_subfieldEntireLaurentAlgHom k (F i)) =
      ∑ j, algebraMap (RatFunc k) (LaurentSeries k) (A i j) *
        stage14_subfieldEntireLaurentAlgHom k (F j) :=
    actualEntire_cleared_system_to_laurent k F A t V ht hV hactual
  have hblock (i j : Fin N) (hij : block i ≠ block j) : A i j = 0 :=
    blockDiagonal_reindex_offBlock e
      (fun σ : K ≃ₐ[ℚ] K => minimalDerivativeCompanion r
        (fun u => coefficientRatFuncHom (strictEGaloisCoefficientLift K σ).toAlgHom.toRingHom (b u))) i j hij
  have hli (σ : K ≃ₐ[ℚ] K) : LinearIndependent (RatFunc k)
      (fun j : {j // block j = block (idx σ)} => stage14_subfieldEntireLaurentAlgHom k (F j.val)) :=
    reindexed_block_fiber_linearIndependent (R := RatFunc k) e
      (fun i => stage14_subfieldEntireLaurentAlgHom k (F₀ i))
      (fun τ => conjugateDerivativePrefix_independent (fun n => (a n : AlgebraicComplex)) ha
        (strictEGaloisCoefficientLift K τ) r b hmin) (idx σ)
  obtain ⟨hNorm, ⟨c, hc⟩, hNormNe, hNormZero⟩ := galoisNorm_properties K a hf hs
  have hprod (z : ℂ) :
      (∏ σ : K ≃ₐ[ℚ] K, (F (idx σ)).val.val z) = galoisNormFunction K a z := by
    unfold galoisNormFunction
    apply Finset.prod_congr rfl
    intro σ _
    dsimp only [F, idx]
    rw [Equiv.symm_apply_apply]
    change factorialSeriesFunction
      (fun n => strictEGaloisCoefficientLift K σ (a n : AlgebraicComplex)) z = _
    simp only [strictEGaloisCoefficientLift_commutes]
  obtain ⟨m, p, hord, hsource⟩ :=
    rational_product_quotient_ordinary_annihilator hLaurent F idx hNorm (hNormNe hfne)
      c hc (hNormZero hzero) hprod
  exact actual_block_quotient_ordinary_annihilator_contradiction k F A hsystem t V ht hV
    block hblock idx hli m p hord hsource

/-- The wide Laurent-operator assertion suffices for ordinary minimal
nonvanishing. The finite Galois field and ordinary denominator are constructed
from the given expansion and minimal equation. -/
theorem wideRegularMinimalNonvanishingAtOne_of_laurentOperatorExistence
    (hLaurent : WideLaurentOperatorExistence) : WideRegularMinimalNonvanishingAtOne := by
  intro f hf hfne a hs r hr b hmin hreg
  classical
  have hfield : HasFixedCoefficientField a := by
    obtain ⟨a', hd, hs', _, _, hfield⟩ := hf
    simpa only [hs.unique hs' hd] using hfield
  obtain ⟨F, hF, haF⟩ := hfield
  letI : FiniteDimensional ℚ F := hF
  let K := IntermediateField.normalClosure ℚ F AlgebraicComplex
  letI : FiniteDimensional ℚ K := inferInstanceAs (FiniteDimensional ℚ
    (IntermediateField.normalClosure ℚ F AlgebraicComplex))
  letI : IsGalois ℚ K := inferInstanceAs (IsGalois ℚ (IntermediateField.normalClosure ℚ F AlgebraicComplex))
  letI : Fintype (K ≃ₐ[ℚ] K) := AlgEquiv.fintype ℚ K
  let aK (n : ℕ) : K := ⟨a n, IntermediateField.le_normalClosure F (haF n)⟩
  obtain ⟨T, hT, U, hU⟩ := exists_ordinary_minimal_companion_clearing (1 : AlgebraicComplex) r b hreg
  exact nonvanishing_from_galois_blocks hLaurent K aK hf hfne hs r hr b hmin T U hT hU

theorem wideLinearOrdinaryLiftingAtOne_of_regularMinimalNonvanishing
    (hscalar : WideRegularMinimalNonvanishingAtOne) : WideLinearOrdinaryLiftingAtOne := by
  intro n _ f t B ht hf hs c hc
  classical
  letI : SMul (RatFunc AlgebraicComplex) (LaurentSeries AlgebraicComplex) := Algebra.toSMul
  letI : Module (RatFunc AlgebraicComplex) (LaurentSeries AlgebraicComplex) := Algebra.toModule
  letI : HSMul (RatFunc AlgebraicComplex) (LaurentSeries AlgebraicComplex)
      (LaurentSeries AlgebraicComplex) := ⟨fun a x => algebraMap _ _ a * x⟩
  have he (i : Fin n) : ∃ a, HasFactorialExpansion (f i) a := by
    obtain ⟨a, _, hs', _⟩ := hf i
    exact ⟨a, hs'⟩
  choose a ha using he
  let k := algebraicSubfield
  let F : Fin n → subfieldEntireFunctionAlgebra k :=
    fun i => taylorRealization (f i) (hf i).differentiable (ha i)
  let Y : Fin n → LaurentSeries AlgebraicComplex :=
    fun i => stage14_subfieldEntireLaurentAlgHom k (F i)
  let A : Fin n → Fin n → RatFunc AlgebraicComplex := fun i j =>
    (algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) t)⁻¹ *
      algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) (B i j)
  have ht0 : t ≠ 0 := by
    intro htZero
    apply ht
    simp [htZero]
  have hsys := actualFamily_clearedSystem_normalized k F t B ht0 hs
  have hY : ∀ i, laurentOrdinaryDerivation (Y i) = ∑ j, A i j • Y j := hsys.1
  have hclear : ∀ i j, algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) (B i j) =
      algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) t * A i j := hsys.2
  rcases ordinary_relation_or_prescribed_regular_minimal
      (1 : AlgebraicComplex) Y A hY t B ht hclear c with hrel | hcyc
  · obtain ⟨p, hp, hpc⟩ := hrel
    refine ⟨p, hpc, ?_⟩
    exact (actualFamily_polynomial_relation_iff k F p).mp hp
  · obtain ⟨m, hm, _, p, hp, b, hmin, hreg⟩ := hcyc
    let g : ℂ → ℂ := fun z => ∑ i, (p i).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z * f i z
    have hg : IsWideEFunction g := isWideEFunction_polynomialCombination p f hf
    have hExpansion : ∃ ag, HasFactorialExpansion g ag := by
      obtain ⟨ag, _, hsg, _⟩ := hg
      exact ⟨ag, hsg⟩
    obtain ⟨ag, hsg⟩ := hExpansion
    let G := taylorRealization g hg.differentiable hsg
    have himage : stage14_subfieldEntireLaurentAlgHom k G =
        ∑ i, algebraMap (Polynomial AlgebraicComplex) (RatFunc AlgebraicComplex) (p i) • Y i :=
      actualFamily_polynomialCombination_laurent k F G p (fun z => rfl)
    have hminG : OrdinaryBorelMinimalCyclicData (stage14_subfieldEntireLaurentAlgHom k G) m b := by
      rw [himage]
      exact hmin
    have hLne : stage14_subfieldEntireLaurentAlgHom k G ≠ 0 := by
      simpa using hminG.1.ne_zero (⟨0, hm⟩ : Fin m)
    have hgNe : g ≠ 0 := by
      intro hZero
      have hG : G = 0 := Subtype.ext (Subtype.ext hZero)
      exact hLne (by rw [hG, map_zero])
    have hvalue : g 1 = 0 := by
      dsimp only [g]
      simp_rw [Polynomial.eval₂_at_one, hp]
      exact hc
    have hsource : stage14_subfieldEntireLaurentAlgHom k G =
        HahnSeries.ofPowerSeries ℤ AlgebraicComplex (stage41_strictFormalSeries ag) := by
      rw [stage14_subfieldEntireLaurentAlgHom_apply]
      exact congrArg (HahnSeries.ofPowerSeries ℤ AlgebraicComplex)
        (taylorRealization_factorialSeries hg.differentiable hsg)
    rw [hsource] at hminG
    exact False.elim ((hscalar g hg hgNe ag hsg m hm b hminG hreg) hvalue)

/-- Exact wide lifting follows from the Laurent-operator assertion by applying
it to the rational Galois norm quotient. -/
theorem wideLinearOrdinaryLiftingAtOne_of_laurentOperatorExistence
    (hLaurent : WideLaurentOperatorExistence) : WideLinearOrdinaryLiftingAtOne :=
  wideLinearOrdinaryLiftingAtOne_of_regularMinimalNonvanishing
    (wideRegularMinimalNonvanishingAtOne_of_laurentOperatorExistence hLaurent)

/-- Division at one for the wide class reduces to the Laurent-operator assertion. -/
theorem wideEFunction_divAtOne_of_laurentOperatorExistence
    (hLaurent : WideLaurentOperatorExistence) {f : ℂ → ℂ} (hf : IsWideEFunction f)
    (hz : f 1 = 0) :
    ∃ g : ℂ → ℂ, IsWideEFunction g ∧ ∀ z : ℂ, (z - 1) * g z = f z :=
  wideEFunction_divAtOne_of_arithmetic_inputs hLaurent
    (wideLinearOrdinaryLiftingAtOne_of_laurentOperatorExistence hLaurent) hf hz

end WideE
