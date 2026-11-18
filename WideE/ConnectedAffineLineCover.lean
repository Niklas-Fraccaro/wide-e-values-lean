import WideE.ConnectedKummerClassification
import WideE.TensorLocalization
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Unramified.Field

/-! Finite étale domain algebras over the affine line over the algebraic numbers. -/

noncomputable section

open scoped TensorProduct
open LaurentPolynomial

namespace WideE

universe u

private theorem isIntegrallyClosedIn_of_localizationAway
    {A B : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Algebra A B]
    (a : A) (ha : a ≠ 0) [IsLocalization.Away a B] : IsIntegrallyClosedIn A B := by
  let F := FractionRing A
  have hu : IsUnit (algebraMap A F a) :=
    isUnit_iff_ne_zero.mpr (fun h => ha ((IsFractionRing.injective A F) (h.trans (map_zero _).symm)))
  let f : B →ₐ[A] F :=
    { IsLocalization.Away.lift a hu with commutes' := IsLocalization.Away.lift_eq a hu }
  have hB := IsLocalization.injective B (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  have hf : Function.Injective f := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers a) f.toRingHom).mpr
    intro x y
    change algebraMap A B x = algebraMap A B y ↔ f (algebraMap A B x) = f (algebraMap A B y)
    rw [f.commutes, f.commutes, hB.eq_iff, (IsFractionRing.injective A F).eq_iff]
  exact f.isIntegrallyClosedIn hf inferInstance

private theorem affineLine_zeroFiber_isReduced {K A : Type u} [Field K] [CommRing A]
    [Algebra (Polynomial K) A] [Algebra.Etale (Polynomial K) A] :
    IsReduced (A ⧸ Ideal.span {algebraMap (Polynomial K) A Polynomial.X}) := by
  let R := Polynomial K
  let I : Ideal A := Ideal.span {algebraMap R A Polynomial.X}
  let B := A ⧸ I
  letI : Algebra K A := ((algebraMap R A).comp (algebraMap K R)).toAlgebra
  letI : IsScalarTower K R A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f : R →ₐ[K] B := IsScalarTower.toAlgHom K R B
  let e : R →ₐ[K] K := Polynomial.aeval (0 : K)
  have hf : f Polynomial.X = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have he : (Algebra.ofId K B).comp e = f := by
    apply Polynomial.algHom_ext
    change algebraMap K B (Polynomial.aeval (0 : K) Polynomial.X) = f Polynomial.X
    rw [Polynomial.aeval_X, map_zero, hf]
  letI : Algebra R K := e.toRingHom.toAlgebra
  letI : IsScalarTower R K B := IsScalarTower.of_algebraMap_eq fun p => (DFunLike.congr_fun he p).symm
  letI : Algebra.FiniteType K B := Algebra.FiniteType.of_restrictScalars_finiteType R K B
  letI : Algebra.FormallyUnramified K B := Algebra.FormallyUnramified.of_comp R K B
  exact Algebra.FormallyUnramified.isReduced_of_field K B

private theorem affineLine_coordinate_not_isUnit {K A : Type*} [Field K] [CommRing A] [IsDomain A]
    [Algebra (Polynomial K) A] [Module.Finite (Polynomial K) A]
    (hInj : Function.Injective (algebraMap (Polynomial K) A)) :
    ¬ IsUnit (algebraMap (Polynomial K) A Polynomial.X) := by
  let R := Polynomial K
  let m := RingHom.ker (Polynomial.evalRingHom (0 : K))
  letI : m.IsPrime := RingHom.ker_isPrime _
  letI : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  have hker : RingHom.ker (algebraMap R A) ≤ m := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hInj]
    exact bot_le
  obtain ⟨p, hp, hOver⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain m hker
  have hx : algebraMap R A Polynomial.X ∈ p := by
    change Polynomial.X ∈ Ideal.comap (algebraMap R A) p
    rw [hOver]
    simp [m]
  exact fun hu => hp.ne_top (Ideal.eq_top_of_isUnit_mem p hx hu)

private theorem exponent_eq_one_of_reduced_coordinateFiber
    {A : Type*} [CommRing A] [IsDomain A] {x u : A} {d : ℕ} (hd : 0 < d)
    (hx : x ≠ 0) (hnu : ¬ IsUnit x) [IsReduced (A ⧸ Ideal.span {x})] (hu : u ^ d = x) : d = 1 := by
  let I : Ideal A := Ideal.span {x}
  have hxI : x ∈ I := Ideal.subset_span (by simp)
  have hnil : IsNilpotent (Ideal.Quotient.mk I u) := by
    refine ⟨d, ?_⟩
    rw [← map_pow, hu]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hxI
  have huI : u ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (isNilpotent_iff_eq_zero.mp hnil)
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp huI
  have hu0 : u ≠ 0 := fun he => hx (hu.symm.trans (he.symm ▸ zero_pow hd.ne'))
  by_contra hd1
  have hd' : 1 < d := by omega
  have hmul : u * (u ^ (d - 1) * v) = u * 1 := by
    rw [← mul_assoc, ← pow_succ', Nat.sub_one_add_one hd.ne', hu, mul_one]
    exact hv.symm
  have hunit : IsUnit (u ^ (d - 1)) :=
    isUnit_of_dvd_unit ⟨v, (mul_left_cancel₀ hu0 hmul).symm⟩ isUnit_one
  exact hnu (hu ▸ ((isUnit_pow_iff (Nat.sub_ne_zero_of_lt hd')).mp hunit).pow d)

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 120000 in
/-- A finite étale domain over the polynomial line over the algebraic numbers
is the polynomial line itself, via its given structure map. -/
theorem affineLine_finiteEtaleDomain_bijective (A : Type) [CommRing A] [IsDomain A]
    [Algebra (Polynomial AlgebraicComplex) A] [Module.Finite (Polynomial AlgebraicComplex) A]
    [Algebra.Etale (Polynomial AlgebraicComplex) A] :
    Function.Bijective (algebraMap (Polynomial AlgebraicComplex) A) := by
  let K := AlgebraicComplex
  let R := Polynomial K
  let L := LaurentPolynomial K
  let T := L ⊗[R] A
  let x := algebraMap R A Polynomial.X
  letI : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra K A := ((algebraMap R A).comp (algebraMap K R)).toAlgebra
  letI : IsScalarTower K R A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : NoZeroSMulDivisors R A := noZeroSMulDivisors_of_finiteEtale (K := K)
  have hinj : Function.Injective (algebraMap R A) := FaithfulSMul.algebraMap_injective R A
  have hx : x ≠ 0 := (map_ne_zero_iff _ hinj).mpr Polynomial.X_ne_zero
  let i : A →ₐ[R] T := Algebra.TensorProduct.includeRight
  letI : Algebra A T := i.toRingHom.toAlgebra
  letI : IsScalarTower R A T := IsScalarTower.of_algHom i
  letI : IsLocalization.Away x T := baseChange_isLocalizationAway (S := A) (T := L) Polynomial.X
  letI : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors A
    (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
  letI : IrreducibleSpace (PrimeSpectrum T) := PrimeSpectrum.irreducibleSpace
  letI : ConnectedSpace (PrimeSpectrum T) := IrreducibleSpace.connectedSpace _
  obtain ⟨d, hd, hRank, ⟨e⟩⟩ := exists_kummerEquiv_of_connected_finiteEtaleLaurent T
  let w := e.symm (KummerExtension.power K d 1)
  have hxT : algebraMap A T x = algebraMap L T (LaurentPolynomial.T 1) := by
    rw [← IsScalarTower.algebraMap_apply R A T, IsScalarTower.algebraMap_apply R L T]
    change algebraMap L T (Polynomial.toLaurent (Polynomial.X : R)) = _
    rw [Polynomial.toLaurent_X]
  have hw : w ^ d = algebraMap A T x := by
    rw [hxT, show w = e.symm (KummerExtension.power K d 1) from rfl, ← map_pow,
      KummerExtension.coordinate_pow, ← KummerExtension.algebraMap_coordinate, e.symm.commutes]
  letI : IsIntegrallyClosed A := isIntegrallyClosed_of_finite_unramified_pid R A
  letI : IsIntegrallyClosedIn A T := isIntegrallyClosedIn_of_localizationAway x hx
  obtain ⟨u, hu⟩ := IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow hd
    (show IsIntegral A (w ^ d) by rw [hw]; exact isIntegral_algebraMap)
  have hu' : u ^ d = x := IsLocalization.injective T (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
    (by rw [map_pow, hu, hw])
  letI : IsReduced (A ⧸ Ideal.span {x}) := affineLine_zeroFiber_isReduced
  have hd1 : d = 1 := exponent_eq_one_of_reduced_coordinateFiber hd hx
    (affineLine_coordinate_not_isUnit hinj) hu'
  letI : Module.Free R A := Module.free_of_finite_type_torsion_free'
  have hRankChange : Module.finrank L T = Module.finrank R A := Module.finrank_baseChange
  have hTop : (⊥ : Subalgebra R A) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one
    (hRankChange.symm.trans (hRank.symm.trans hd1))
  exact ⟨hinj, fun a => Algebra.mem_bot.mp (hTop.symm ▸ Algebra.mem_top (x := a))⟩

end WideE
