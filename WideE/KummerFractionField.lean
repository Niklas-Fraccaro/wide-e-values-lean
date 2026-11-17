import WideE.KummerCoordinates
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot

/-! Recover the finite Kummer algebra from a power coordinate in its fraction field. -/

noncomputable section

namespace WideE

open LaurentPolynomial

private theorem laurentMap_injective_at_transcendental
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (f : LaurentPolynomial K →ₐ[K] E) (h : Transcendental K (f (T 1))) :
    Function.Injective f := by
  have he : f.comp Polynomial.toLaurentAlg = Polynomial.aeval (f (T 1)) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.toLaurentAlg_apply, Polynomial.toLaurent_X,
      Polynomial.aeval_X]
  have hi : Function.Injective (f.comp Polynomial.toLaurentAlg) :=
    he ▸ transcendental_iff_injective.mp h
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (Polynomial.X : Polynomial K)) f.toRingHom).mpr
  intro p g
  refine ⟨fun h => congrArg f h, fun h => ?_⟩
  apply congrArg (algebraMap (Polynomial K) (LaurentPolynomial K))
  exact hi h

section

variable {K Q E : Type*} [Field K] [CommRing Q] [Field E]
  [Algebra (LaurentPolynomial K) Q] [Algebra.IsIntegral (LaurentPolynomial K) Q]
  [Algebra Q E] [IsFractionRing Q E] [IsIntegrallyClosed Q]
  [Algebra (LaurentPolynomial K) E] [IsScalarTower (LaurentPolynomial K) Q E]
  [Algebra K E] [IsScalarTower K (LaurentPolynomial K) E]

/-- If the given fraction field has a generating coordinate whose power is the base
coordinate, the integral closure is the explicit Kummer algebra. -/
theorem kummerEquiv_of_fractionFieldPower
    (hBase : Function.Injective (algebraMap (LaurentPolynomial K) Q)) {q : ℕ} (hq : 0 < q)
    (t : E) (ht : t ^ q = algebraMap (LaurentPolynomial K) E (T 1))
    (htGen : IntermediateField.adjoin K ({t} : Set E) = ⊤) :
    Nonempty (Q ≃ₐ[LaurentPolynomial K] KummerExtension K q) := by
  let R := LaurentPolynomial K
  let S := KummerExtension K q
  let u := KummerExtension.power K q 1
  have hb : Function.Injective (algebraMap R E) := by
    rw [IsScalarTower.algebraMap_eq R Q E]
    exact (IsFractionRing.injective Q E).comp hBase
  have hTrans : Transcendental K t := by
    let z : E := algebraMap R E (T 1)
    have he : Polynomial.aeval z =
        (IsScalarTower.toAlgHom K R E).comp Polynomial.toLaurentAlg := by
      apply Polynomial.algHom_ext
      change Polynomial.aeval z Polynomial.X =
        algebraMap R E ((Polynomial.X : Polynomial K).toLaurent)
      rw [Polynomial.aeval_X, Polynomial.toLaurent_X]
    have hz : Transcendental K z := transcendental_iff_injective.mpr
      (he.symm ▸ hb.comp Polynomial.toLaurent_injective)
    intro ha
    apply hz
    change IsAlgebraic K (algebraMap R E (T 1))
    rw [← ht]
    exact isAlgebraic_iff_isIntegral.mpr (ha.isIntegral.pow q)
  have hroot : Polynomial.aeval t (KummerExtension.polynomial K q) = 0 := by
    rw [KummerExtension.aeval_polynomial, ht, sub_self]
  let f : S →ₐ[R] E := (AdjoinRoot.liftHom _ t hroot).comp
    (KummerExtension.adjoinRootEquiv K q hq).symm.toAlgHom
  have hfu : f u = t := by
    change AdjoinRoot.liftHom _ t hroot ((KummerExtension.adjoinRootEquiv K q hq).symm u) = t
    rw [show u = _ from (KummerExtension.adjoinRootEquiv_root K q hq).symm,
      AlgEquiv.symm_apply_apply, AdjoinRoot.liftHom_root]
  let e : S ≃ₐ[K] LaurentPolynomial K :=
    { KummerExtension.toLaurent K q with commutes' := fun _ => rfl }
  let fk := f.restrictScalars K
  let g := fk.comp e.symm.toAlgHom
  have hg (a : KummerExtension K q) : g (e a) = f a := by
    simp only [g, fk, AlgHom.comp_apply, AlgEquiv.coe_algHom,
      AlgEquiv.symm_apply_apply, AlgHom.restrictScalars_apply]
  have hgu : g (T 1) = t := by
    have he : e u = T 1 := KummerExtension.toLaurent_power K q 1
    rw [← he, hg, hfu]
  have hgi := laurentMap_injective_at_transcendental g (hgu.symm ▸ hTrans)
  have hfi : Function.Injective f :=
    fun a b h => e.injective (hgi ((hg a).trans (h.trans (hg b).symm)))
  letI : IsDomain S := inferInstanceAs (IsDomain (LaurentPolynomial K))
  letI : IsIntegrallyClosed S := inferInstanceAs (IsIntegrallyClosed (LaurentPolynomial K))
  let F := FractionRing S
  let fF : F →ₐ[K] E := IsFractionRing.liftAlgHom (g := fk) hfi
  have hLift (x : S) : fF (algebraMap S F x) = f x :=
    IsFractionRing.lift_algebraMap hfi x
  have hS : Function.Surjective fF := by
    apply AlgHom.fieldRange_eq_top.mp
    apply top_le_iff.mp
    rw [← htGen, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact AlgHom.mem_fieldRange.mpr ⟨algebraMap S F u, (hLift u).trans hfu⟩
  letI : Algebra S E := f.toRingHom.toAlgebra
  letI : IsScalarTower R S E := IsScalarTower.of_algHom f
  let fFS : F →ₐ[S] E := { fF.toRingHom with commutes' := hLift }
  let eF := AlgEquiv.ofBijective fFS ⟨fF.injective, hS⟩
  letI : IsFractionRing S E :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors S) eF
  letI : Module.Finite R S := KummerExtension.finite K q hq
  letI : IsIntegralClosure S R E := IsIntegralClosure.of_isIntegrallyClosedIn
  letI : IsIntegralClosure Q R E := IsIntegralClosure.of_isIntegrallyClosedIn
  exact ⟨IsIntegralClosure.equiv R Q E S⟩

variable [IsAlgClosed K]

/-- A generator whose power gives a unit times either orientation of the base coordinate
also determines the same Kummer algebra. -/
theorem kummerEquiv_of_fractionFieldMonomial
    (hBase : Function.Injective (algebraMap (LaurentPolynomial K) Q)) {q : ℕ} (hq : 0 < q)
    (t : E) {a : K} (ha : a ≠ 0) {n : ℤ} (hn : n = 1 ∨ n = -1)
    (ht : t ^ q = algebraMap (LaurentPolynomial K) E (C a * T n))
    (htGen : IntermediateField.adjoin K ({t} : Set E) = ⊤) :
    Nonempty (Q ≃ₐ[LaurentPolynomial K] KummerExtension K q) := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a⁻¹ hq
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow hq.ne'] at hb
    exact (inv_ne_zero ha) hb.symm
  let v := t * algebraMap K E b
  have hv : v ^ q = algebraMap (LaurentPolynomial K) E (T n) := by
    dsimp only [v]
    rw [mul_pow, ht, ← map_pow, hb, map_mul, C_eq_algebraMap, ← IsScalarTower.algebraMap_apply,
      mul_right_comm, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
  have hvGen : IntermediateField.adjoin K ({v} : Set E) = ⊤ := by
    apply top_le_iff.mp
    rw [← htGen, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    have hvmem : v ∈ IntermediateField.adjoin K ({v} : Set E) :=
      IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
    have hbinv : algebraMap K E b⁻¹ ∈ IntermediateField.adjoin K ({v} : Set E) :=
      (IntermediateField.adjoin K ({v} : Set E)).algebraMap_mem _
    have h := mul_mem hvmem hbinv
    rwa [show v * algebraMap K E b⁻¹ = t by
      dsimp only [v]
      rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hb0, map_one, mul_one]] at h
  rcases hn with rfl | rfl
  · exact kummerEquiv_of_fractionFieldPower hBase hq v hv hvGen
  · apply kummerEquiv_of_fractionFieldPower hBase hq v⁻¹
    · rw [inv_pow, hv]
      apply inv_eq_of_mul_eq_one_right
      rw [← map_mul, ← T_add, neg_add_cancel, T_zero, map_one]
    · apply top_le_iff.mp
      rw [← hvGen, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      have hmem : v⁻¹ ∈ IntermediateField.adjoin K ({v⁻¹} : Set E) :=
        IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
      simpa only [inv_inv] using inv_mem hmem

end

end WideE
