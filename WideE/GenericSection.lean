import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-! Spreading a generic section of an affine finite-type scheme to a nonempty
principal open. This applies to the generic-point step in §7. -/

noncomputable section

namespace WideE

open scoped BigOperators

variable {R F S : Type*} [CommRing R] [IsDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F] [CommRing S] [Algebra R S]

/-- The map from the ring of a nonempty principal open to the fraction field. -/
def principalOpenToFraction {a : R} (ha : a ≠ 0) : Localization.Away a →ₐ[R] F :=
  IsLocalization.liftAlgHom (M := Submonoid.powers a) (f := Algebra.ofId R F) (by
    rintro ⟨b, n, rfl⟩
    change IsUnit (algebraMap R F (a ^ n))
    rw [map_pow]
    exact (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr ha)).pow n)

omit [IsDomain R] in
theorem principalOpenToFraction_injective {a : R} (ha : a ≠ 0) :
    Function.Injective (principalOpenToFraction (F := F) ha) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers a)
    (principalOpenToFraction (F := F) ha).toRingHom).mpr
  intro x y
  change algebraMap R (Localization.Away a) x = algebraMap R (Localization.Away a) y ↔
    principalOpenToFraction (F := F) ha (algebraMap R (Localization.Away a) x) =
    principalOpenToFraction (F := F) ha (algebraMap R (Localization.Away a) y)
  rw [AlgHom.commutes, AlgHom.commutes]
  constructor
  · intro h
    have h' := congrArg (fun x : Localization.Away a => principalOpenToFraction (F := F) ha x) h
    simpa only [AlgHom.commutes] using h'
  · intro h
    exact congrArg (algebraMap R (Localization.Away a)) (IsFractionRing.injective R F h)

/-- A rational section over the fraction field restricts to one principal
open, with the chosen rational section recovered on the generic point. -/
theorem exists_principalOpen_section [Algebra.FiniteType R S] (p : S →ₐ[R] F) :
    ∃ (a : R) (ha : a ≠ 0), ∃ s : S →ₐ[R] Localization.Away a,
      (principalOpenToFraction ha).comp s = p := by
  classical
  obtain ⟨g, hg⟩ := (inferInstance : Algebra.FiniteType R S).out
  choose w hw using fun i : g => IsLocalization.surj (nonZeroDivisors R) (p i)
  let b (i : g) := ((w i).2 : R)
  let a := ∏ i : g, b i
  have ha : a ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => nonZeroDivisors.coe_ne_zero (w i).2)
  let φ : Localization.Away a →ₐ[R] F := principalOpenToFraction ha
  have hGen : (g : Set S) ⊆ φ.range.comap p := by
    intro x hx
    let i : g := ⟨x, hx⟩
    have hd : b i ∣ a := Finset.dvd_prod_of_mem b (Finset.mem_univ i)
    have hUnit : IsUnit (algebraMap R (Localization.Away a) (b i)) :=
      isUnit_of_dvd_unit (map_dvd _ hd) (IsLocalization.Away.algebraMap_isUnit a)
    let v := algebraMap R (Localization.Away a) (w i).1 * ↑hUnit.unit⁻¹
    change p x ∈ φ.range
    refine ⟨v, ?_⟩
    have hv : v * algebraMap R (Localization.Away a) (b i) =
        algebraMap R (Localization.Away a) (w i).1 := by
      rw [← hUnit.unit_spec, mul_assoc, Units.inv_mul, mul_one]
    have hφ := congrArg φ hv
    rw [map_mul, AlgHom.commutes, AlgHom.commutes] at hφ
    have hn : algebraMap R F (b i) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr (nonZeroDivisors.coe_ne_zero (w i).2)
    exact mul_right_cancel₀ hn (hφ.trans (hw i).symm)
  have hTop : (⊤ : Subalgebra R S) ≤ φ.range.comap p := by
    rw [← hg]
    exact Algebra.adjoin_le_iff.mpr hGen
  have hAll (x : S) : p x ∈ φ.range := hTop (show x ∈ (⊤ : Subalgebra R S) by simp)
  let e := AlgEquiv.ofInjective φ (principalOpenToFraction_injective ha)
  refine ⟨a, ha, e.symm.toAlgHom.comp (p.codRestrict φ.range hAll), ?_⟩
  apply AlgHom.ext
  intro x
  exact congrArg Subtype.val (e.apply_symm_apply (p.codRestrict φ.range hAll x))

end WideE
