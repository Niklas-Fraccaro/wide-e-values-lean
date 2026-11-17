import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.Ring

/-! Extension of a rational projective point over a principal ideal domain.
The resulting coordinates generate the unit ideal and satisfy every original
homogeneous equation. -/

open scoped BigOperators

noncomputable section

namespace WideE

variable {R F ι : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [Algebra R F] [IsFractionRing R F] [Fintype ι]

/-- Clear the denominators and divide out the common ideal generator. -/
theorem exists_primitive_coordinates (x : ι → F) (hx : x ≠ 0) :
    ∃ y : ι → R, Ideal.span (Set.range y) = ⊤ ∧
      ∃ c : Fˣ, ∀ i, algebraMap R F (y i) = (c : F) * x i := by
  classical
  let M := nonZeroDivisors R
  let d := IsLocalization.commonDenom M Finset.univ x
  let a (i : ι) := IsLocalization.integerMultiple M Finset.univ x ⟨i, Finset.mem_univ i⟩
  have ha (i : ι) : algebraMap R F (a i) = algebraMap R F (d : R) * x i := by
    rw [← Algebra.smul_def]
    exact IsLocalization.map_integerMultiple M Finset.univ x ⟨i, Finset.mem_univ i⟩
  let I := Ideal.span (Set.range a)
  let b := Submodule.IsPrincipal.generator I
  have hIb : Ideal.span ({b} : Set R) = I := Ideal.span_singleton_generator I
  have hd : algebraMap R F (d : R) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr (nonZeroDivisors.coe_ne_zero d)
  have hb : b ≠ 0 := by
    intro hzero
    apply hx
    funext i
    have hmem : a i ∈ Ideal.span ({b} : Set R) :=
      hIb.symm ▸ Ideal.subset_span (Set.mem_range_self i)
    have hi := Ideal.mem_span_singleton.mp hmem
    rw [hzero, zero_dvd_iff] at hi
    have h := ha i
    rw [hi, map_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hd
  have hDiv (i : ι) : b ∣ a i := by
    apply Ideal.mem_span_singleton.mp
    rw [hIb]
    exact Ideal.subset_span (Set.mem_range_self i)
  choose y hy using hDiv
  let J := Ideal.span (Set.range y)
  let μ : R →ₗ[R] R := LinearMap.smulRight LinearMap.id b
  have hμ (z : R) : μ z = b * z := by simp [μ, smul_eq_mul, mul_comm]
  have hLe : (I : Submodule R R) ≤ Submodule.map μ (J : Submodule R R) := by
    apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    exact Submodule.mem_map.mpr ⟨y i, Ideal.subset_span (Set.mem_range_self i),
      (hμ (y i)).trans (hy i).symm⟩
  have hmem : b ∈ I := hIb ▸ Ideal.mem_span_singleton_self b
  obtain ⟨w, hw, hwb⟩ := Submodule.mem_map.mp (hLe hmem)
  have hw1 : w = 1 := mul_left_cancel₀ hb (by rw [← hμ, hwb, mul_one])
  have hJ : J = ⊤ := (Ideal.eq_top_iff_one J).mpr (hw1 ▸ hw)
  have hbF : algebraMap R F b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hb
  let u := Units.mk0 (algebraMap R F (d : R) / algebraMap R F b) (div_ne_zero hd hbF)
  refine ⟨y, hJ, u, fun i => ?_⟩
  apply mul_left_cancel₀ hbF
  rw [← map_mul, ← hy i, ha i]
  change algebraMap R F (d : R) * x i =
    algebraMap R F b * (algebraMap R F (d : R) / algebraMap R F b * x i)
  rw [← mul_assoc, mul_div_cancel₀ _ hbF]

/-- Scaling finite projective coordinates scales each homogeneous equation
by the corresponding power. -/
theorem homogeneous_eval₂_scale {K L : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (p : MvPolynomial ι K) {d : ℕ} (hp : p.IsHomogeneous d)
    (a : L) (x : ι → L) :
    p.eval₂ φ (fun i => a * x i) = a ^ d * p.eval₂ φ x := by
  classical
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hDeg : (∑ i : ι, m i) = d := by
    rw [← Finsupp.sum_fintype m (fun _ n => n) (fun _ => rfl)]
    change m.degree = d
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hm)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hDeg]
  ring

/-- A rational solution to homogeneous projective equations over a PID
extends to a solution with primitive integral coordinates. -/
theorem projective_equations_extend_to_pid {α : Type*} (p : α → MvPolynomial ι R)
    (d : α → ℕ) (hHom : ∀ i, (p i).IsHomogeneous (d i)) (x : ι → F) (hx : x ≠ 0)
    (hEq : ∀ i, (p i).eval₂ (algebraMap R F) x = 0) :
    ∃ y : ι → R, Ideal.span (Set.range y) = ⊤ ∧ ∀ i, (p i).eval y = 0 := by
  obtain ⟨y, hy, a, ha⟩ := exists_primitive_coordinates (R := R) x hx
  refine ⟨y, hy, fun i => ?_⟩
  apply (IsFractionRing.injective R F)
  rw [map_zero, MvPolynomial.eval₂_comp, show (algebraMap R F ∘ y) = fun j => (a : F) * x j
    from funext ha, homogeneous_eval₂_scale _ _ (hHom i), hEq, mul_zero]

end WideE
