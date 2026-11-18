import WideE.JacobianDominance
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Localization.InvSubmonoid
import Mathlib.RingTheory.Localization.Away.Basic
import AlgebraicPoint

/-! A dominant affine map over an algebraically closed field lifts every point
on a nonempty principal open. -/

noncomputable section

namespace WideE

/-- For an injective map of domains of finite presentation, the image of the
prime spectrum contains a nonempty principal open around the generic point. -/
theorem exists_basicOpen_subset_range_comap {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] (f : R →+* S) (hf : Function.Injective f)
    (hfp : f.FinitePresentation) :
    ∃ d : R, d ≠ 0 ∧
      (PrimeSpectrum.basicOpen d : Set (PrimeSpectrum R)) ⊆ Set.range (PrimeSpectrum.comap f) := by
  let η : PrimeSpectrum R := ⊥
  have hη : η ∈ Set.range (PrimeSpectrum.comap f) := by
    refine ⟨⊥, PrimeSpectrum.ext ?_⟩
    change RingHom.ker f = ⊥
    exact (RingHom.injective_iff_ker_eq_bot f).mp hf
  obtain ⟨C, hC⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr
    (PrimeSpectrum.isConstructible_range_comap hfp)
  rw [← hC, PrimeSpectrum.ConstructibleSetData.toSet] at hη
  obtain ⟨c, hc, hηc⟩ := Set.mem_iUnion₂.mp hη
  change η ∈ PrimeSpectrum.zeroLocus (Set.range c.g) \ PrimeSpectrum.zeroLocus {c.f} at hηc
  have hg (j : Fin c.n) : c.g j = 0 :=
    Ideal.mem_bot.mp ((PrimeSpectrum.mem_zeroLocus η _).mp hηc.1 (Set.mem_range_self j))
  refine ⟨c.f, fun h => hηc.2 ((PrimeSpectrum.mem_zeroLocus η _).mpr ?_), ?_⟩
  · rintro _ rfl
    exact Ideal.mem_bot.mpr h
  · intro p hp
    rw [← hC, PrimeSpectrum.ConstructibleSetData.toSet]
    apply Set.mem_iUnion₂.mpr
    refine ⟨c, hc, ?_, ?_⟩
    · apply (PrimeSpectrum.mem_zeroLocus p _).mpr
      rintro _ ⟨j, rfl⟩
      rw [hg]
      exact Ideal.zero_mem _
    · intro h
      exact (PrimeSpectrum.mem_basicOpen _ _).mp hp
        ((PrimeSpectrum.mem_zeroLocus p _).mp h (Set.mem_singleton _))

section RationalPoints

variable {k R S : Type*} [Field k] [IsAlgClosed k]
  [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] [Algebra.FiniteType k S]

/-- A spectral preimage of a rational point admits a rational preimage. -/
theorem exists_algebraicPoint_lift_of_comap (f : R →ₐ[k] S) (p : R →ₐ[k] k)
    (z : PrimeSpectrum S) (hz : z.asIdeal.comap f.toRingHom = RingHom.ker p.toRingHom) :
    ∃ q : S →ₐ[k] k, q.comp f = p := by
  obtain ⟨m, hm, hzm⟩ := z.asIdeal.exists_le_maximal z.isPrime.ne_top
  letI := hm
  let q : S →ₐ[k] k := StrictEUnit.maximalIdealPoint m
  refine ⟨q, AlgHom.ext fun x => ?_⟩
  have hx : x - algebraMap k R (p x) ∈ z.asIdeal.comap f.toRingHom := by
    rw [hz, RingHom.mem_ker]
    change p (x - algebraMap k R (p x)) = 0
    rw [map_sub, p.commutes, Algebra.id.map_eq_id, RingHom.id_apply, sub_self]
  have hqx : q (f (x - algebraMap k R (p x))) = 0 := by
    change q.toRingHom (f (x - algebraMap k R (p x))) = 0
    rw [← RingHom.mem_ker, StrictEUnit.maximalIdealPoint_ker (k := k) m]
    exact hzm hx
  rw [map_sub, map_sub, f.commutes, q.commutes, Algebra.id.map_eq_id, RingHom.id_apply,
    sub_eq_zero] at hqx
  exact hqx

/-- An injective morphism of affine domains lifts all rational points in some
principal open around the generic point of the base. -/
theorem exists_principal_open_lift_of_injective [IsDomain R] [IsDomain S] [IsNoetherianRing R]
    (f : R →ₐ[k] S) (hf : Function.Injective f) :
    ∃ d : R, d ≠ 0 ∧ ∀ p : R →ₐ[k] k, p d ≠ 0 → ∃ q : S →ₐ[k] k, q.comp f = p := by
  letI : Algebra R S := f.toRingHom.toAlgebra
  letI : IsScalarTower k R S := IsScalarTower.of_algHom f
  letI : Algebra.FiniteType R S := Algebra.FiniteType.of_restrictScalars_finiteType k R S
  have hfp : f.toRingHom.FinitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨d, hd, hOpen⟩ := exists_basicOpen_subset_range_comap f.toRingHom hf hfp
  refine ⟨d, hd, fun p hp => ?_⟩
  let η : PrimeSpectrum R := ⟨RingHom.ker p.toRingHom, RingHom.ker_isPrime p.toRingHom⟩
  have hη : η ∈ PrimeSpectrum.basicOpen d := (PrimeSpectrum.mem_basicOpen _ _).mpr hp
  obtain ⟨z, hz⟩ := hOpen hη
  exact exists_algebraicPoint_lift_of_comap f p z (congrArg PrimeSpectrum.asIdeal hz)

end RationalPoints

section AffineImage

variable {k A ι : Type*} [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A]
  [Algebra k A] [Algebra.FiniteType k A] [Finite ι]

/-- Algebraically independent coordinate functions attain every tuple in
some nonempty principal open of affine space. -/
theorem exists_affine_image_principal_open (x : ι → A) (hx : AlgebraicIndependent k x) :
    ∃ d : MvPolynomial ι k, d ≠ 0 ∧ ∀ y : ι → k, MvPolynomial.aeval y d ≠ 0 →
      ∃ q : A →ₐ[k] k, ∀ i, q (x i) = y i := by
  obtain ⟨d, hd, hLift⟩ := exists_principal_open_lift_of_injective (MvPolynomial.aeval x) hx
  refine ⟨d, hd, fun y hy => ?_⟩
  obtain ⟨q, hq⟩ := hLift (MvPolynomial.aeval y) hy
  exact ⟨q, fun i => by
    simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using DFunLike.congr_fun hq (MvPolynomial.X i)⟩

/-- A prescribed nonzero function on the source can be kept nonzero in
the chosen lifts on a possibly smaller principal open of the target. -/
theorem exists_affine_image_principal_open_avoiding (x : ι → A) (hx : AlgebraicIndependent k x)
    (a : A) (ha : a ≠ 0) :
    ∃ d : MvPolynomial ι k, d ≠ 0 ∧ ∀ y : ι → k, MvPolynomial.aeval y d ≠ 0 →
      ∃ q : A →ₐ[k] k, (∀ i, q (x i) = y i) ∧ q a ≠ 0 := by
  let L := Localization.Away a
  letI : IsDomain L := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  letI : Algebra.FiniteType A L := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers a) L
  letI : Algebra.FiniteType k L := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType k A) (inferInstance : Algebra.FiniteType A L)
  let f := IsScalarTower.toAlgHom k A L
  have hf : Function.Injective f :=
    IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  have hComp : MvPolynomial.aeval (f ∘ x) = f.comp (MvPolynomial.aeval x) :=
    MvPolynomial.algHom_ext fun i => by
      rw [MvPolynomial.aeval_X, AlgHom.comp_apply, MvPolynomial.aeval_X]
      rfl
  have hx' : AlgebraicIndependent k (f ∘ x) := by
    rw [algebraicIndependent_iff_injective_aeval, hComp]
    exact hf.comp hx
  obtain ⟨d, hd, hLift⟩ := exists_affine_image_principal_open (f ∘ x) hx'
  refine ⟨d, hd, fun y hy => ?_⟩
  obtain ⟨q, hq⟩ := hLift y hy
  exact ⟨q.comp f, hq, ((IsLocalization.Away.algebraMap_isUnit (S := L) a).map q).ne_zero⟩

end AffineImage

end WideE
