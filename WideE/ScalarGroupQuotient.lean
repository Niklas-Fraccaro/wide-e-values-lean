import WideE.AdditivePolynomialHopf
import WideE.HopfSmoothLocus
import WideE.KummerCoordinates
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-! Faithful flatness of the coordinate map to an additive or multiplicative scalar group. -/

noncomputable section

open scoped TensorProduct
open TensorProduct

namespace WideE

private theorem flat_of_torsionFree_of_principalIdealRing
    {A M : Type*} [CommRing A] [IsPrincipalIdealRing A]
    [AddCommGroup M] [Module A M] [NoZeroSMulDivisors A M] : Module.Flat A M := by
  refine Module.Flat.iff_rTensor_injective'.mpr fun I =>
    (injective_iff_map_eq_zero _).mpr fun z hz => ?_
  let a := Submodule.IsPrincipal.generator I
  let b : I := ⟨a, Submodule.IsPrincipal.generator_mem I⟩
  have hRep (w : I ⊗[A] M) : ∃ x : M, b ⊗ₜ[A] x = w := by
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, tmul_zero _ _⟩
    | tmul i x =>
      obtain ⟨c, hc⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator
        (I : Submodule A A)).mp i.property
      have hi : i = c • b := Subtype.ext hc
      exact ⟨c • x, by rw [hi]; exact (smul_tmul c b x).symm⟩
    | add w w' hw hw' =>
      obtain ⟨x, rfl⟩ := hw
      obtain ⟨x', rfl⟩ := hw'
      exact ⟨x + x', tmul_add _ _ _⟩
  obtain ⟨x, rfl⟩ := hRep z
  have hax : a • x = 0 := by
    simpa only [LinearMap.rTensor_tmul, Submodule.subtype_apply, TensorProduct.lid_tmul,
      map_zero] using congrArg (TensorProduct.lid A M) hz
  rcases smul_eq_zero.mp hax with ha | hx
  · have hb : b = 0 := Subtype.ext ha
    rw [hb, zero_tmul]
  · rw [hx, tmul_zero]

section Translation

variable {k A H : Type*} [CommRing k] [CommRing A] [CommRing H]
  [HopfAlgebra k A] [HopfAlgebra k H]

theorem hopfTranslate_comp_bialgHom (j : A →ₐc[k] H) (r : H →ₐ[k] k) :
    (hopfTranslate r).comp (j : A →ₐ[k] H) =
      (j : A →ₐ[k] H).comp (hopfTranslate (r.comp (j : A →ₐ[k] H))) := by
  let f : A →ₐ[k] H := j
  have hc (a : A) : Bialgebra.comulAlgHom k H (f a) =
      Algebra.TensorProduct.map f f (Bialgebra.comulAlgHom k A a) :=
    (DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom j) a).symm
  apply AlgHom.ext
  intro a
  change Algebra.TensorProduct.lid k H
    (Algebra.TensorProduct.map r (AlgHom.id k H) (Bialgebra.comulAlgHom k H (f a))) =
    f (Algebra.TensorProduct.lid k A
      (Algebra.TensorProduct.map (r.comp f) (AlgHom.id k A) (Bialgebra.comulAlgHom k A a)))
  rw [hc]
  generalize Bialgebra.comulAlgHom k A a = z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul,
      AlgHom.id_apply, AlgHom.comp_apply, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Translation

section RationalPoints

universe u

variable {k A H : Type u} [Field k] [IsAlgClosed k] [CommRing A] [CommRing H]
  [HopfAlgebra k A] [HopfAlgebra k H]

omit [IsAlgClosed k] in
private theorem pointPrime_comap (f : A →ₐ[k] H) (r : H →ₐ[k] k) :
    PrimeSpectrum.comap f.toRingHom (hopfPointPrime r) = hopfPointPrime (r.comp f) := rfl

theorem lift_rationalPoint_of_mem_range [Algebra.FiniteType k H]
    (f : A →ₐ[k] H) (p : A →ₐ[k] k)
    (hp : hopfPointPrime p ∈ Set.range (PrimeSpectrum.comap f.toRingHom)) :
    ∃ r : H →ₐ[k] k, r.comp f = p := by
  obtain ⟨x, hx⟩ := hp
  obtain ⟨m, hm, hxm⟩ := x.asIdeal.exists_le_maximal x.isPrime.ne_top
  letI : m.IsMaximal := hm
  have hpMax : (hopfPointPrime p).asIdeal.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective p.toRingHom
      (fun c => ⟨algebraMap k A c, by simp⟩)
  let r := StrictEUnit.maximalIdealPoint (k := k) m
  have hk : RingHom.ker (r.comp f).toRingHom = RingHom.ker p.toRingHom := by
    change Ideal.comap f.toRingHom (RingHom.ker r.toRingHom) = (hopfPointPrime p).asIdeal
    rw [StrictEUnit.maximalIdealPoint_ker]
    exact (hpMax.eq_of_le (Ideal.comap_ne_top f.toRingHom hm.ne_top) (by
      rw [← congrArg PrimeSpectrum.asIdeal hx]
      exact Ideal.comap_mono hxm)).symm
  refine ⟨r, AlgHom.ext fun a => ?_⟩
  have hmem : a - algebraMap k A (p a) ∈ RingHom.ker (r.comp f).toRingHom := by
    rw [hk]
    change p (a - algebraMap k A (p a)) = 0
    simp
  change (r.comp f) (a - algebraMap k A (p a)) = 0 at hmem
  simpa [sub_eq_zero] using hmem

private theorem spectrum_scalarQuotient_surjective_of_open
    [IsDomain A] [Algebra.FiniteType k A] [Algebra.FiniteType k H]
    (j : A →ₐc[k] H) (hOpen : IsOpenMap (PrimeSpectrum.comap (j : A →ₐ[k] H).toRingHom))
    (hComm : ∀ p q : A →ₐ[k] k, q.comp (hopfTranslate p) = p.comp (hopfTranslate q)) :
    Function.Surjective (PrimeSpectrum.comap (j : A →ₐ[k] H).toRingHom) := by
  classical
  let f : A →ₐ[k] H := j
  let F := PrimeSpectrum.comap f.toRingHom
  let U := Set.range F
  have hU : IsOpen U := by
    change IsOpen (Set.range F)
    rw [← Set.image_univ]
    exact hOpen Set.univ isOpen_univ
  have hU' : U.Nonempty := ⟨_, ⟨hopfPointPrime (Bialgebra.counitAlgHom k H), rfl⟩⟩
  letI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  have closed_mem (x : PrimeSpectrum A) (hx : x.asIdeal.IsMaximal) : x ∈ U := by
    letI : x.asIdeal.IsMaximal := hx
    let p := StrictEUnit.maximalIdealPoint (k := k) x.asIdeal
    have hp : hopfPointPrime p = x := PrimeSpectrum.ext (StrictEUnit.maximalIdealPoint_ker _)
    let tr (q : A →ₐ[k] k) := PrimeSpectrum.comap (hopfTranslate q).toRingHom
    have hTr (q : A →ₐ[k] k) : IsHomeomorph (tr q) :=
      PrimeSpectrum.isHomeomorph_comap_of_bijective (hopfTranslation q).bijective
    have hopen : IsOpen (U ∩ tr p ⁻¹' U) := hU.inter (hU.preimage (hTr p).continuous)
    have hnonempty : (U ∩ tr p ⁻¹' U).Nonempty := by
      refine nonempty_preirreducible_inter hU (hU.preimage (hTr p).continuous) hU' ?_
      obtain ⟨v, hv⟩ := hU'
      obtain ⟨w, hw⟩ := (hTr p).surjective v
      exact ⟨w, by change tr p w ∈ U; rwa [hw]⟩
    obtain ⟨y, ⟨hy, hytr⟩, hyClosed⟩ :=
      PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing _ hopen hnonempty
    letI : y.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hyClosed
    let q := StrictEUnit.maximalIdealPoint (k := k) y.asIdeal
    have hq : hopfPointPrime q = y := PrimeSpectrum.ext (StrictEUnit.maximalIdealPoint_ker _)
    obtain ⟨r, hr⟩ := lift_rationalPoint_of_mem_range f q (hq.symm ▸ hy)
    have hswap : tr p (hopfPointPrime q) = tr q (hopfPointPrime p) := by
      change PrimeSpectrum.comap (hopfTranslate p).toRingHom (hopfPointPrime q) =
        PrimeSpectrum.comap (hopfTranslate q).toRingHom (hopfPointPrime p)
      rw [pointPrime_comap, pointPrime_comap, hComm]
    have hyqp : tr q (hopfPointPrime p) ∈ U := by
      change tr p y ∈ U at hytr
      rwa [← hq, hswap] at hytr
    obtain ⟨z, hz⟩ := hyqp
    let trH := PrimeSpectrum.comap (hopfTranslate r).toRingHom
    have hTrH : IsHomeomorph trH :=
      PrimeSpectrum.isHomeomorph_comap_of_bijective (hopfTranslation r).bijective
    obtain ⟨w, hw⟩ := hTrH.surjective z
    refine ⟨w, (hTr q).injective ?_⟩
    calc
      tr q (F w) = F (trH w) := by
        have hc : f.comp (hopfTranslate q) = (hopfTranslate r).comp f := by
          rw [← hr]
          exact (hopfTranslate_comp_bialgHom j r).symm
        have hc' : f.toRingHom.comp (hopfTranslate q).toRingHom =
            (hopfTranslate r).toRingHom.comp f.toRingHom := congrArg AlgHom.toRingHom hc
        change PrimeSpectrum.comap (hopfTranslate q).toRingHom
          (PrimeSpectrum.comap f.toRingHom w) =
          PrimeSpectrum.comap f.toRingHom (PrimeSpectrum.comap (hopfTranslate r).toRingHom w)
        rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply, hc']
      _ = tr q x := by rw [hw, ← hp]; exact hz
  intro x
  by_contra hx
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hU.isClosed_compl
  have hxI : x ∈ Uᶜ := hx
  rw [hI, PrimeSpectrum.mem_zeroLocus] at hxI
  obtain ⟨m, hm, hxm⟩ := x.asIdeal.exists_le_maximal x.isPrime.ne_top
  let y : PrimeSpectrum A := ⟨m, hm.isPrime⟩
  have hy : y ∈ Uᶜ := by
    rw [hI, PrimeSpectrum.mem_zeroLocus]
    exact fun a ha => hxm (hxI ha)
  exact hy (closed_mem y hm)

private theorem scalarGroupQuotient_faithfullyFlat
    [IsDomain A] [IsPrincipalIdealRing A] [Algebra.FiniteType k A]
    [IsDomain H] [Algebra.FiniteType k H]
    (j : A →ₐc[k] H) (hj : Function.Injective j)
    (hComm : ∀ p q : A →ₐ[k] k, q.comp (hopfTranslate p) = p.comp (hopfTranslate q)) :
    letI : Algebra A H := (j : A →ₐ[k] H).toRingHom.toAlgebra
    Module.FaithfullyFlat A H := by
  letI : Algebra A H := (j : A →ₐ[k] H).toRingHom.toAlgebra
  letI : IsScalarTower k A H := IsScalarTower.of_algHom (j : A →ₐ[k] H)
  letI : NoZeroSMulDivisors A H := NoZeroSMulDivisors.iff_algebraMap_injective.mpr hj
  letI : Module.Flat A H := flat_of_torsionFree_of_principalIdealRing
  letI : Algebra.FiniteType A H := Algebra.FiniteType.of_restrictScalars_finiteType k A H
  letI : Algebra.FinitePresentation A H := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  apply Module.FaithfullyFlat.of_specComap_surjective
  exact spectrum_scalarQuotient_surjective_of_open j
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation hComm

end RationalPoints

section ScalarGroups

universe u

variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [IsDomain H]
  [HopfAlgebra k H]

attribute [local instance] additivePolynomialHopf

private theorem algebraic_eq_counit_scalar {x : H} (hx : IsAlgebraic k x) :
    x = algebraMap k H (Bialgebra.counitAlgHom k H x) := by
  have hm := minpoly.monic hx.isIntegral
  have hd := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hx.isIntegral)
  have hroot := minpoly.aeval k x
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hd, hm, Polynomial.C_1, one_mul,
    map_add, Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg, ← map_neg] at hroot
  have hε : Bialgebra.counitAlgHom k H x = -(minpoly k x).coeff 0 := by
    simpa using congrArg (Bialgebra.counitAlgHom k H) hroot
  rwa [hε]

private theorem polynomialMap_injective_of_ne_counit_scalar (f : Polynomial k →ₐ[k] H)
    (hf : f Polynomial.X ≠ algebraMap k H (Bialgebra.counitAlgHom k H (f Polynomial.X))) :
    Function.Injective f := by
  have he : f = Polynomial.aeval (f Polynomial.X) :=
    Polynomial.algHom_ext (Polynomial.aeval_X _).symm
  rw [he]
  exact transcendental_iff_injective.mp fun hx => hf (algebraic_eq_counit_scalar hx)

/-- A nonzero primitive coordinate gives an injective additive group quotient. -/
theorem additiveGroupQuotient_injective (j : Polynomial k →ₐc[k] H)
    (hj : j Polynomial.X ≠ 0) : Function.Injective j := by
  have hε : Bialgebra.counitAlgHom k H (j Polynomial.X) = 0 :=
    (DFunLike.congr_fun (BialgHomClass.counitAlgHom_comp j) Polynomial.X).trans
      (Polynomial.aeval_X (0 : k))
  apply polynomialMap_injective_of_ne_counit_scalar (j : Polynomial k →ₐ[k] H)
  change j Polynomial.X ≠ algebraMap k H (Bialgebra.counitAlgHom k H (j Polynomial.X))
  rwa [hε, map_zero]

/-- A group-like coordinate distinct from the identity gives an injective
multiplicative group quotient. -/
theorem multiplicativeGroupQuotient_injective (j : LaurentPolynomial k →ₐc[k] H)
    (hj : j (LaurentPolynomial.T 1) ≠ 1) : Function.Injective j := by
  let f : LaurentPolynomial k →ₐ[k] H := j
  have hε : Bialgebra.counitAlgHom k H (j (LaurentPolynomial.T 1)) = 1 :=
    (DFunLike.congr_fun (BialgHomClass.counitAlgHom_comp j) (LaurentPolynomial.T 1)).trans
      (LaurentPolynomial.counit_T (R := k) 1)
  have hi : Function.Injective (f.comp Polynomial.toLaurentAlg) := by
    apply polynomialMap_injective_of_ne_counit_scalar
    simp only [AlgHom.comp_apply, Polynomial.toLaurentAlg_apply, Polynomial.toLaurent_X]
    change j (LaurentPolynomial.T 1) ≠
      algebraMap k H (Bialgebra.counitAlgHom k H (j (LaurentPolynomial.T 1)))
    rwa [hε, map_one]
  change Function.Injective f.toRingHom
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (Polynomial.X : Polynomial k)) f.toRingHom).mpr
  intro p q
  exact ⟨congrArg f, fun h => congrArg (algebraMap (Polynomial k) (LaurentPolynomial k)) (hi h)⟩

variable [Algebra.FiniteType k H]

/-- An injective Hopf map from the additive line defines a faithfully flat algebra. -/
theorem additiveGroupQuotient_faithfullyFlat (j : Polynomial k →ₐc[k] H)
    (hj : Function.Injective j) :
    letI : Algebra (Polynomial k) H := (j : Polynomial k →ₐ[k] H).toRingHom.toAlgebra
    Module.FaithfullyFlat (Polynomial k) H := by
  refine scalarGroupQuotient_faithfullyFlat j hj fun p q => Polynomial.algHom_ext ?_
  simp only [AlgHom.comp_apply, hopfTranslate, AlgEquiv.coe_algHom,
    additivePolynomialHopf_comul_X, map_add, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.lid_tmul, AlgHom.id_apply, map_one, one_smul, map_smul, smul_eq_mul,
    mul_one, add_comm]

/-- An injective Hopf map from the multiplicative line defines a faithfully flat algebra. -/
theorem multiplicativeGroupQuotient_faithfullyFlat (j : LaurentPolynomial k →ₐc[k] H)
    (hj : Function.Injective j) :
    letI : Algebra (LaurentPolynomial k) H :=
      (j : LaurentPolynomial k →ₐ[k] H).toRingHom.toAlgebra
    Module.FaithfullyFlat (LaurentPolynomial k) H := by
  letI : IsPrincipalIdealRing (LaurentPolynomial k) :=
    StrictEUnit.laurentPolynomial_isPrincipalIdealRing k
  letI : Algebra.Etale (Polynomial k) (LaurentPolynomial k) :=
    Algebra.Etale.of_isLocalization_Away (Polynomial.X : Polynomial k)
  letI : IsScalarTower k (Polynomial k) (LaurentPolynomial k) :=
    IsScalarTower.of_algebraMap_eq fun c => (Polynomial.toLaurent_C c).symm
  letI : Algebra.FiniteType k (LaurentPolynomial k) :=
    Algebra.FiniteType.trans (S := Polynomial k) inferInstance inferInstance
  have hΔ : Bialgebra.comulAlgHom k (LaurentPolynomial k) (LaurentPolynomial.T 1) =
      (LaurentPolynomial.T 1 : LaurentPolynomial k) ⊗ₜ[k] LaurentPolynomial.T 1 :=
    LaurentPolynomial.comul_T 1
  refine scalarGroupQuotient_faithfullyFlat j hj fun p q => laurentAlgHom_ext ?_
  simp only [AlgHom.comp_apply, hopfTranslate, AlgEquiv.coe_algHom, hΔ,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul, AlgHom.id_apply,
    map_smul, smul_eq_mul, mul_comm]

end ScalarGroups

end WideE
