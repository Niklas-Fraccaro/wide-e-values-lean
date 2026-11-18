import WideE.KummerIntermediateField
import WideE.KummerFractionField
import Mathlib.RingTheory.Ideal.GoingUp

/-! Recover Laurent power coordinates from a map to a Kummer cover. -/

noncomputable section

namespace WideE

open LaurentPolynomial

section FractionCoordinates

variable {k A E : Type*} [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Field E]
  [Algebra (LaurentPolynomial k) A] [Algebra.IsIntegral (LaurentPolynomial k) A]
  [Algebra A E] [IsFractionRing A E]
  [Algebra (LaurentPolynomial k) E] [IsScalarTower (LaurentPolynomial k) A E]
  [Algebra k A] [IsScalarTower k (LaurentPolynomial k) A]
  [Algebra k E] [IsScalarTower k A E]

local notation "R" => LaurentPolynomial k
local notation "L" => FractionRing (LaurentPolynomial k)

omit [IsAlgClosed k] [Algebra k A] [IsScalarTower k R A] in
private theorem injective_of_domain_integral {B : Type*} [CommRing B]
    (g : A →+* B) (h : Function.Injective (g.comp (algebraMap R A))) : Function.Injective g := by
  apply (RingHom.injective_iff_ker_eq_bot g).mpr
  have hker : (RingHom.ker g).comap (algebraMap R A) = ⊥ := by
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).mp h
  exact Ideal.eq_bot_of_comap_eq_bot hker

/-- An algebra map to a positive Kummer cover determines a genuine power
coordinate on the fraction field of the given integral Laurent domain. -/
theorem exists_fractionPower_of_kummerMap {q : ℕ} (hq : 0 < q) (f : A →ₐ[R] KummerExtension k q) :
    Function.Injective (algebraMap R A) ∧
      ∃ d : ℕ, 0 < d ∧ d ∣ q ∧ ∃ t : E,
        t ^ d = algebraMap R E (T 1) ∧ IntermediateField.adjoin k ({t} : Set E) = ⊤ := by
  let φ := (algebraMap R L).comp ((KummerExtension.toLaurent k q).toRingHom.comp f.toRingHom)
  have hf (r : R) : φ (algebraMap R A r) = algebraMap R L (kummerAlgHom k q r) := by
    change algebraMap R L (KummerExtension.toLaurent k q (f (algebraMap R A r))) = _
    rw [f.commutes]
    rfl
  have hbase : Function.Injective (φ.comp (algebraMap R A)) := by
    have h := (IsFractionRing.injective R L).comp (kummerAlgHom_injective k hq)
    intro x y he
    apply h
    exact (hf x).symm.trans (he.trans (hf y))
  have hfI := injective_of_domain_integral φ hbase
  refine ⟨fun x y he => hbase (congrArg φ he), ?_⟩
  let j : A →ₐ[k] L := {
    toRingHom := φ
    commutes' c := by
      change φ (algebraMap k A c) = algebraMap k L c
      rw [IsScalarTower.algebraMap_apply k R A, hf, (kummerAlgHom k q).commutes]
      exact (IsScalarTower.algebraMap_apply k R L c).symm }
  let g : E →ₐ[k] L := IsFractionRing.liftAlgHom (g := j) hfI
  let z := laurentFractionCoordinate k
  have hgz : g (algebraMap R E (T 1)) = z ^ q := by
    rw [IsScalarTower.algebraMap_apply R A E]
    change IsFractionRing.lift hfI (algebraMap A E (algebraMap R A (T 1))) = z ^ q
    rw [IsFractionRing.lift_algebraMap hfI]
    change φ (algebraMap R A (T 1)) = z ^ q
    rw [hf, kummerAlgHom_apply, kummer_T, mul_one]
    change algebraMap R L (T (q : ℤ)) = (algebraMap R L (T 1)) ^ q
    rw [← map_pow, T_pow, mul_one]
  have hzq : z ^ q ∈ g.fieldRange := AlgHom.mem_fieldRange.mpr ⟨_, hgz⟩
  obtain ⟨i, hi, ⟨d, hd⟩, hF⟩ := intermediateField_eq_laurentPowerField k g.fieldRange hq hzq
  have hzd : z ^ i ∈ g.fieldRange := hF.symm ▸ IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
  obtain ⟨t, ht⟩ := AlgHom.mem_fieldRange.mp hzd
  have hdpos : 0 < d := Nat.pos_of_ne_zero fun h => hq.ne' (by rw [hd, h, mul_zero])
  refine ⟨d, hdpos, ⟨i, hd.trans (Nat.mul_comm _ _)⟩, t, ?_, ?_⟩
  · apply g.injective
    calc
      g (t ^ d) = g t ^ d := map_pow g _ _
      _ = z ^ q := by rw [ht, ← pow_mul, ← hd]
      _ = g (algebraMap R E (T 1)) := hgz.symm
  · apply IntermediateField.map_injective g
    rw [IntermediateField.adjoin_map, Set.image_singleton, ← g.fieldRange_eq_map, hF, ht]
    rfl

end FractionCoordinates

section NormalAlgebra

variable {k A : Type*} [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A]
  [Algebra (LaurentPolynomial k) A] [Algebra.IsIntegral (LaurentPolynomial k) A]

local notation "R" => LaurentPolynomial k

/-- A normal integral Laurent domain admitting a Kummer point is itself
isomorphic to a Kummer algebra of degree dividing the given exponent. -/
theorem exists_kummerEquiv_of_integral_kummerMap [IsIntegrallyClosed A] {q : ℕ} (hq : 0 < q)
    (f : A →ₐ[R] KummerExtension k q) :
    ∃ d : ℕ, 0 < d ∧ d ∣ q ∧ Nonempty (A ≃ₐ[R] KummerExtension k d) := by
  let E := FractionRing A
  letI : Algebra k A := ((algebraMap R A).comp (algebraMap k R)).toAlgebra
  letI : Algebra R E := ((algebraMap A E).comp (algebraMap R A)).toAlgebra
  letI : Algebra k E := ((algebraMap R E).comp (algebraMap k R)).toAlgebra
  letI : SMul k A := Algebra.toSMul
  letI : SMul R A := Algebra.toSMul
  letI : SMul A E := Algebra.toSMul
  letI : SMul R E := Algebra.toSMul
  letI : SMul k E := Algebra.toSMul
  letI : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower R A E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower k A E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower k R E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hBase, d, hd, hdq, t, ht, hgen⟩ := exists_fractionPower_of_kummerMap (E := E) hq f
  exact ⟨d, hd, hdq, kummerEquiv_of_fractionFieldPower hBase hd t ht hgen⟩

end NormalAlgebra

end WideE
