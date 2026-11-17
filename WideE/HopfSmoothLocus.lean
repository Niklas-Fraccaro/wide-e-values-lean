import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import AlgebraicPoint

/-! Translation by a rational point of an affine group and its effect on smoothness. -/

noncomputable section

open scoped TensorProduct
open TensorProduct

namespace WideE

section Translation

variable {k H : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H]

local notation "Δ" => (Coalgebra.comul (R := k) (A := H))
local notation "ε" => (Coalgebra.counit (R := k) (A := H))
local notation "σ" => (HopfAlgebra.antipode (R := k) (A := H))

private def leftEvaluation (p : H →ₗ[k] k) : H ⊗[k] H →ₗ[k] H :=
  (TensorProduct.lid k H).toLinearMap.comp (TensorProduct.map p LinearMap.id)

private theorem leftEvaluation_tmul (p : H →ₗ[k] k) (a b : H) :
    leftEvaluation p (a ⊗ₜ[k] b) = p a • b := rfl

private def leftTranslationLinear (p : H →ₗ[k] k) : H →ₗ[k] H := (leftEvaluation p).comp Δ

private theorem leftTranslationLinear_counit (a : H) : leftTranslationLinear ε a = a := by
  change TensorProduct.lid k H ((ε).rTensor H (Δ a)) = a
  rw [Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]

private theorem counit_leftTranslationLinear (p : H →ₗ[k] k) (a : H) :
    ε (leftTranslationLinear p a) = p a := by
  have h (z : H ⊗[k] H) :
      ε (leftEvaluation p z) = p (TensorProduct.rid k H ((ε).lTensor H z)) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      rw [leftEvaluation_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_smul,
        map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
  change ε (leftEvaluation p (Δ a)) = p a
  rw [h, Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul]

private theorem evaluate_comul_right (p q : H →ₗ[k] k) (z : H ⊗[k] H) :
    leftEvaluation q (Δ (leftEvaluation p z)) =
      leftEvaluation p (TensorProduct.map LinearMap.id (leftEvaluation q) ((Δ).lTensor H z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    simp only [leftEvaluation_tmul, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
      LinearMap.id_apply, map_smul]

private theorem evaluate_assoc (p q : H →ₗ[k] k) (z : H ⊗[k] H) (b : H) :
    leftEvaluation p (TensorProduct.map LinearMap.id (leftEvaluation q)
      (TensorProduct.assoc k H H H (z ⊗ₜ[k] b))) = q (leftEvaluation p z) • b := by
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [zero_tmul, LinearEquiv.map_zero, LinearMap.map_zero, zero_smul]
  | add x y hx hy => simp only [add_tmul, LinearEquiv.map_add, map_add, add_smul, hx, hy]
  | tmul x y =>
    simp only [TensorProduct.assoc_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
      leftEvaluation_tmul, map_smul, smul_smul, smul_eq_mul]

private theorem evaluate_comul_left (p q : H →ₗ[k] k) (z : H ⊗[k] H) :
    leftEvaluation p (TensorProduct.map LinearMap.id (leftEvaluation q)
      (TensorProduct.assoc k H H H ((Δ).rTensor H z))) =
      leftEvaluation (q.comp (leftTranslationLinear p)) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
  | add x y hx hy => simp only [LinearEquiv.map_add, map_add, hx, hy]
  | tmul x y =>
    rw [LinearMap.rTensor_tmul, evaluate_assoc, leftEvaluation_tmul]
    rfl

private theorem leftTranslationLinear_comp (p q : H →ₗ[k] k) (a : H) :
    leftTranslationLinear q (leftTranslationLinear p a) =
      leftTranslationLinear (q.comp (leftTranslationLinear p)) a := by
  change leftEvaluation q (Δ (leftEvaluation p (Δ a))) = _
  rw [evaluate_comul_right, ← Coalgebra.coassoc_apply (R := k) a, evaluate_comul_left]
  rfl

private theorem evalAntipode_right (p : H →ₐ[k] k) (z : H ⊗[k] H) :
    (p.toLinearMap.comp σ) (leftEvaluation p.toLinearMap z) =
      p (LinearMap.mul' k H ((σ).lTensor H z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    simp only [leftEvaluation_tmul, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      LinearMap.lTensor_tmul, LinearMap.mul'_apply, map_smul, map_mul, smul_eq_mul]

private theorem evalAntipode_left (p : H →ₐ[k] k) (z : H ⊗[k] H) :
    p (leftEvaluation (p.toLinearMap.comp σ) z) = p (LinearMap.mul' k H ((σ).rTensor H z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    simp only [leftEvaluation_tmul, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      LinearMap.rTensor_tmul, LinearMap.mul'_apply, map_smul, map_mul, smul_eq_mul]

private theorem convolutionAntipode_right (p : H →ₐ[k] k) :
    (p.toLinearMap.comp σ).comp (leftTranslationLinear p.toLinearMap) = ε := by
  apply LinearMap.ext
  intro a
  change (p.toLinearMap.comp σ) (leftEvaluation p.toLinearMap (Δ a)) = ε a
  rw [evalAntipode_right, HopfAlgebra.mul_antipode_lTensor_comul_apply, AlgHom.commutes]
  rfl

private theorem convolutionAntipode_left (p : H →ₐ[k] k) :
    p.toLinearMap.comp (leftTranslationLinear (p.toLinearMap.comp σ)) = ε := by
  apply LinearMap.ext
  intro a
  change p (leftEvaluation (p.toLinearMap.comp σ) (Δ a)) = ε a
  rw [evalAntipode_left, HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]
  rfl

/-- Pullback of left translation by a rational point. -/
def hopfTranslate (p : H →ₐ[k] k) : H →ₐ[k] H :=
  (Algebra.TensorProduct.lid k H).toAlgHom.comp
    ((Algebra.TensorProduct.map p (AlgHom.id k H)).comp (Bialgebra.comulAlgHom k H))

/-- Left translation is an algebra isomorphism, with inverse given by the antipode. -/
def hopfTranslation (p : H →ₐ[k] k) : H ≃ₐ[k] H where
  toFun := hopfTranslate p
  invFun := leftTranslationLinear (p.toLinearMap.comp σ)
  left_inv a := by
    change leftTranslationLinear (p.toLinearMap.comp σ) (leftTranslationLinear p.toLinearMap a) = a
    rw [leftTranslationLinear_comp, convolutionAntipode_right, leftTranslationLinear_counit]
  right_inv a := by
    change leftTranslationLinear p.toLinearMap (leftTranslationLinear (p.toLinearMap.comp σ) a) = a
    rw [leftTranslationLinear_comp, convolutionAntipode_left, leftTranslationLinear_counit]
  map_mul' := map_mul (hopfTranslate p)
  map_add' := map_add (hopfTranslate p)
  commutes' := AlgHom.commutes (hopfTranslate p)

@[simp] theorem hopfTranslation_toAlgHom (p : H →ₐ[k] k) :
    (hopfTranslation p).toAlgHom = hopfTranslate p := rfl

@[simp] theorem hopfTranslation_counit (p : H →ₐ[k] k) (a : H) :
    Bialgebra.counitAlgHom k H (hopfTranslation p a) = p a :=
  counit_leftTranslationLinear p.toLinearMap a

/-- The inverse rational point obtained by composing with the antipode. -/
def hopfInversePoint (p : H →ₐ[k] k) : H →ₐ[k] k :=
  (Bialgebra.counitAlgHom k H).comp (hopfTranslation p).symm.toAlgHom

@[simp] theorem hopfInversePoint_apply (p : H →ₐ[k] k) (a : H) :
    hopfInversePoint p a = p (σ a) :=
  counit_leftTranslationLinear (p.toLinearMap.comp σ) a

@[simp] theorem hopfTranslation_inversePoint (p : H →ₐ[k] k) :
    hopfTranslation (hopfInversePoint p) = (hopfTranslation p).symm := by
  have h : (hopfInversePoint p).toLinearMap = p.toLinearMap.comp σ :=
    LinearMap.ext (hopfInversePoint_apply p)
  apply AlgEquiv.ext
  intro a
  change leftTranslationLinear (hopfInversePoint p).toLinearMap a =
    leftTranslationLinear (p.toLinearMap.comp σ) a
  rw [h]

end Translation

section SmoothLocus

universe u

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

/-- The prime corresponding to a rational point of the affine group. -/
def hopfPointPrime (p : H →ₐ[k] k) : PrimeSpectrum H :=
  ⟨RingHom.ker p.toRingHom, RingHom.ker_isPrime _⟩

private theorem smoothLocus_comap_algEquiv (e : H ≃ₐ[k] H) (x : PrimeSpectrum H) :
    PrimeSpectrum.comap e.toRingEquiv.toRingHom x ∈ Algebra.smoothLocus k H ↔
      x ∈ Algebra.smoothLocus k H := by
  let y := PrimeSpectrum.comap e.toRingEquiv.toRingHom x
  have he : Submonoid.map e y.asIdeal.primeCompl = x.asIdeal.primeCompl := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      change e (e.symm z) ∉ x.asIdeal
      rwa [AlgEquiv.apply_symm_apply]
  exact Algebra.FormallySmooth.iff_of_equiv
    (IsLocalization.algEquivOfAlgEquiv (Localization.AtPrime y.asIdeal)
      (Localization.AtPrime x.asIdeal) e he)

private theorem translation_comap_counit (p : H →ₐ[k] k) :
    PrimeSpectrum.comap (hopfTranslation p).toRingEquiv.toRingHom
      (hopfPointPrime (Bialgebra.counitAlgHom k H)) = hopfPointPrime p := by
  apply PrimeSpectrum.ext
  ext a
  change Bialgebra.counitAlgHom k H (hopfTranslation p a) = 0 ↔ p a = 0
  rw [hopfTranslation_counit]

/-- Translation identifies the smoothness condition at a rational point with the
same condition at the identity of the group. -/
theorem hopfPoint_mem_smoothLocus_iff (p : H →ₐ[k] k) :
    hopfPointPrime p ∈ Algebra.smoothLocus k H ↔
      hopfPointPrime (Bialgebra.counitAlgHom k H) ∈ Algebra.smoothLocus k H := by
  rw [← translation_comap_counit p]
  exact smoothLocus_comap_algEquiv (hopfTranslation p) _

variable [IsAlgClosed k] [Algebra.FiniteType k H]

/-- A finite-type affine group over an algebraically closed field is smooth
if it has a smooth rational point. -/
theorem hopfSmooth_of_smooth_point (p : H →ₐ[k] k)
    (hp : hopfPointPrime p ∈ Algebra.smoothLocus k H) : Algebra.Smooth k H := by
  letI : Algebra.FinitePresentation k H := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hId := (hopfPoint_mem_smoothLocus_iff p).mp hp
  have hMax (x : PrimeSpectrum H) (hx : x.asIdeal.IsMaximal) : x ∈ Algebra.smoothLocus k H := by
    letI := hx
    let q := StrictEUnit.maximalIdealPoint (k := k) x.asIdeal
    have hq : hopfPointPrime q = x :=
      PrimeSpectrum.ext (StrictEUnit.maximalIdealPoint_ker x.asIdeal)
    rw [← hq]
    exact (hopfPoint_mem_smoothLocus_iff q).mpr hId
  have hAll : Algebra.smoothLocus k H = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp
      (Algebra.isOpen_smoothLocus (R := k) (A := H)).isClosed_compl
    have hxI : x ∈ (Algebra.smoothLocus k H)ᶜ := hx
    rw [hI, PrimeSpectrum.mem_zeroLocus] at hxI
    obtain ⟨m, hm, hxm⟩ := x.asIdeal.exists_le_maximal x.isPrime.ne_top
    let y : PrimeSpectrum H := ⟨m, hm.isPrime⟩
    have hy : y ∈ (Algebra.smoothLocus k H)ᶜ := by
      rw [hI, PrimeSpectrum.mem_zeroLocus]
      exact fun a ha => hxm (hxI ha)
    exact hy (hMax y hm)
  exact ⟨Algebra.smoothLocus_eq_univ_iff.mp hAll, inferInstance⟩

/-- For a finite-type affine group, a nonempty smooth locus already implies smoothness. -/
theorem hopfSmooth_of_nonempty_smoothLocus (h : (Algebra.smoothLocus k H).Nonempty) :
    Algebra.Smooth k H := by
  letI : Algebra.FinitePresentation k H := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : IsJacobsonRing H := isJacobsonRing_of_finiteType (A := k) (B := H)
  obtain ⟨x, hx, hClosed⟩ := PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing _
    Algebra.isOpen_smoothLocus h
  letI := (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hClosed
  let q := StrictEUnit.maximalIdealPoint (k := k) x.asIdeal
  have hq : hopfPointPrime q = x := PrimeSpectrum.ext (StrictEUnit.maximalIdealPoint_ker x.asIdeal)
  exact hopfSmooth_of_smooth_point q (hq.symm ▸ hx)

end SmoothLocus

section Reduced

open scoped IntermediateField.algebraAdjoinAdjoin

variable {k L H : Type u} [Field k] [CharZero k]

/-- A characteristic-zero field extension is formally smooth by factoring it through
the rational function field on a transcendence basis. -/
theorem formallySmooth_charZero_field [Field L] [Algebra k L] : Algebra.FormallySmooth k L := by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' k L
  let D := Algebra.adjoin k (Set.range x)
  let F := IntermediateField.adjoin k (Set.range x)
  letI : Algebra.FormallySmooth k D := Algebra.FormallySmooth.of_equiv hx.1.aevalEquiv
  letI : Algebra.FormallySmooth D F := Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors D)
  letI : Algebra.FormallySmooth k F := Algebra.FormallySmooth.comp k D F
  letI : Algebra.IsAlgebraic F L := hx.isAlgebraic_field
  letI : CharZero F := Algebra.charZero_of_charZero k F
  letI : Algebra.FormallyEtale F L := Algebra.FormallyEtale.of_isSeparable F L
  exact Algebra.FormallySmooth.comp k F L

/-- At a minimal prime of a reduced algebra in characteristic zero the local ring is
a field, so that prime belongs to the smooth locus. -/
theorem minimalPrime_mem_smoothLocus [CommRing H] [Algebra k H] [IsReduced H]
    (p : Ideal H) (hp : p ∈ minimalPrimes H) :
    (⟨p, hp.1.1⟩ : PrimeSpectrum H) ∈ Algebra.smoothLocus k H := by
  letI : p.IsPrime := hp.1.1
  let L := Localization.AtPrime p
  letI : Ring.KrullDimLE 0 L := Ring.KrullDimLE.of_isLocalization p hp L
  letI : Field L := (Ring.KrullDimLE.isField_of_isReduced (R := L)).toField
  exact formallySmooth_charZero_field (k := k) (L := L)

/-- A reduced affine group of finite type over an algebraically closed field of
characteristic zero is smooth. -/
theorem hopfSmooth_of_isReduced [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
    [Algebra.FiniteType k H] [IsReduced H] : Algebra.Smooth k H := by
  letI : Nontrivial H := (Bialgebra.counitAlgHom k H).toRingHom.domain_nontrivial
  obtain ⟨⟨p, hp⟩⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal H)) bot_ne_top
  exact hopfSmooth_of_nonempty_smoothLocus
    ⟨⟨p, hp.1.1⟩, minimalPrime_mem_smoothLocus p hp⟩

end Reduced

/-- The open-and-closed subscheme selected by an idempotent of a smooth affine
scheme is smooth over the same base. -/
theorem smooth_quotient_idempotent {k H : Type u} [CommRing k] [CommRing H] [Algebra k H]
    [Algebra.Smooth k H] {e : H} (he : IsIdempotentElem e) :
    Algebra.Smooth k (H ⧸ Ideal.span {1 - e}) := by
  let C := H ⧸ Ideal.span {1 - e}
  letI := IsLocalization.Away.quotient_of_isIdempotentElem he
  letI : Algebra.Smooth H C := Algebra.Smooth.of_isLocalization_Away e
  exact Algebra.Smooth.comp k H C

end WideE
