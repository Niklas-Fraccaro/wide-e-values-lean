import WideE.ClosedOrbit
import WideE.HopfPointGroup
import WideE.PuncturedOrbitEvaluation
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import AlgebraicPoint

/-! Closed projective orbits via the scaled action on nonzero affine vectors. -/

noncomputable section

open Set TopologicalSpace Topology
open scoped Matrix TensorProduct

namespace WideE

section RationalPoints

variable {k A B : Type*} [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

private def rationalPrime (p : A →ₐ[k] k) : PrimeSpectrum A :=
  ⟨RingHom.ker p.toRingHom, RingHom.ker_isPrime _⟩

private theorem rationalPrime_comap (f : A →ₐ[k] B) (p : B →ₐ[k] k) :
    PrimeSpectrum.comap f.toRingHom (rationalPrime p) = rationalPrime (p.comp f) := rfl

private theorem rationalPrime_maximal (p : A →ₐ[k] k) : (rationalPrime p).asIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective p.toRingHom fun a => ⟨algebraMap k A a, p.commutes a⟩

private theorem rationalPrime_injective : Function.Injective (rationalPrime (k := k) (A := A)) := by
  intro p q h
  apply AlgHom.ext
  intro a
  have hp : a - algebraMap k A (p a) ∈ (rationalPrime p).asIdeal := by
    change p (a - algebraMap k A (p a)) = 0
    rw [map_sub, AlgHom.commutes, Algebra.id.map_eq_id, RingHom.id_apply, sub_self]
  rw [h] at hp
  change q (a - algebraMap k A (p a)) = 0 at hp
  rw [map_sub, AlgHom.commutes, Algebra.id.map_eq_id, RingHom.id_apply, sub_eq_zero] at hp
  exact hp.symm

private theorem rationalPrime_dense [IsAlgClosed k] [Algebra.FiniteType k A] :
    Dense (range (rationalPrime (k := k) (A := A))) := by
  letI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  apply dense_iff_inter_open.mpr
  intro S hS hne
  obtain ⟨x, hx, hC⟩ := PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing S hS hne
  letI : x.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hC
  refine ⟨x, hx, StrictEUnit.maximalIdealPoint x.asIdeal, ?_⟩
  exact PrimeSpectrum.ext (StrictEUnit.maximalIdealPoint_ker x.asIdeal)

end RationalPoints

section ConePoints

variable {k H ι : Type*} [Field k] [CommRing H] [Algebra k H] [Fintype ι]

local notation "L" => LaurentPolynomial H
local notation "P" => MvPolynomial ι k

private theorem puncturedOrbitEvaluation_atPoint (U : Matrix ι ι H) (v : ι → k) (e : L →ₐ[k] k) :
    e.comp (puncturedOrbitEvaluation U v) = MvPolynomial.aeval
      (e (LaurentPolynomial.T 1) • ((U.map (e.comp (IsScalarTower.toAlgHom k H L))) *ᵥ v)) := by
  let p := e.comp (IsScalarTower.toAlgHom k H L)
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, puncturedOrbitEvaluation_X, map_mul, MvPolynomial.aeval_X,
    Pi.smul_apply, smul_eq_mul, mul_comm]
  change e (LaurentPolynomial.T 1) * p (orbitVector U v i) = _
  congr 1
  rw [orbitVector]
  have h := RingHom.map_mulVec p.toRingHom U (algebraMap k H ∘ v) i
  change p ((U *ᵥ (algebraMap k H ∘ v)) i) = _ at h
  have hp : p.toRingHom ∘ (algebraMap k H ∘ v) = v := funext fun j => p.commutes (v j)
  rw [hp] at h
  exact h

private theorem puncturedOrbitEvaluation_laurentPoint (U : Matrix ι ι H) (v : ι → k)
    (p : H →ₐ[k] k) (c : kˣ) :
    (evalLaurentPoint p c).comp (puncturedOrbitEvaluation U v) =
      MvPolynomial.aeval ((c : k) • ((U.map p) *ᵥ v)) := by
  rw [puncturedOrbitEvaluation_atPoint]
  have hC : (evalLaurentPoint p c).comp (IsScalarTower.toAlgHom k H L) = p :=
    AlgHom.ext fun b => LaurentPolynomial.eval₂_C p.toRingHom c b
  rw [evalLaurentPoint_T_one, hC]

private theorem exists_orbitPoint_of_mem_range [IsAlgClosed k] [Algebra.FiniteType k H]
    (U : Matrix ι ι H) (v w : ι → k)
    (hw : rationalPrime (MvPolynomial.aeval w) ∈ range
      (PrimeSpectrum.comap (puncturedOrbitEvaluation U v).toRingHom)) :
    ∃ (p : H →ₐ[k] k) (c : kˣ), w = (c : k) • ((U.map p) *ᵥ v) := by
  letI : Algebra.FiniteType k L := laurentPolynomial_finiteType (H := H)
  let f := puncturedOrbitEvaluation U v
  obtain ⟨x, hx⟩ := hw
  obtain ⟨m, hm, hxM⟩ := x.asIdeal.exists_le_maximal x.isPrime.ne_top
  letI : m.IsMaximal := hm
  let e : L →ₐ[k] k := StrictEUnit.maximalIdealPoint m
  have hM : (rationalPrime e).asIdeal = m := StrictEUnit.maximalIdealPoint_ker m
  have hLe : (rationalPrime (MvPolynomial.aeval w)).asIdeal ≤
      (PrimeSpectrum.comap f.toRingHom (rationalPrime e)).asIdeal := by
    rw [← hx]
    change x.asIdeal.comap f.toRingHom ≤ (rationalPrime e).asIdeal.comap f.toRingHom
    rw [hM]
    exact Ideal.comap_mono hxM
  have hEq : rationalPrime (MvPolynomial.aeval w) = PrimeSpectrum.comap f.toRingHom (rationalPrime e) :=
    PrimeSpectrum.ext ((rationalPrime_maximal _).eq_of_le (PrimeSpectrum.comap f.toRingHom
      (rationalPrime e)).isPrime.ne_top hLe)
  have hEval := rationalPrime_injective (hEq.trans (rationalPrime_comap f e))
  let c := ((LaurentPolynomial.isUnit_T (R := H) 1).map e).unit
  have hc : (c : k) = e (LaurentPolynomial.T 1) := IsUnit.unit_spec _
  refine ⟨e.comp (IsScalarTower.toAlgHom k H L), c, funext fun i => ?_⟩
  have h := AlgHom.congr_fun (hEval.trans (puncturedOrbitEvaluation_atPoint U v e)) (MvPolynomial.X i)
  simpa only [MvPolynomial.aeval_X, hc] using h

end ConePoints

section Orbits

variable {k H ι : Type*} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [Fintype ι] [DecidableEq ι]

private abbrev NonzeroVector (k ι : Type*) [Zero k] := {v : ι → k // v ≠ 0}

private def puncturedAffinePrime (v : NonzeroVector k ι) : PrimeSpectrum (MvPolynomial ι k) :=
  rationalPrime (MvPolynomial.aeval v.val)

local instance : TopologicalSpace (NonzeroVector k ι) :=
  TopologicalSpace.induced puncturedAffinePrime inferInstance

omit [IsAlgClosed k] [Fintype ι] [DecidableEq ι] in
private theorem puncturedAffinePrime_inducing : IsInducing (puncturedAffinePrime (k := k) (ι := ι)) :=
  ⟨rfl⟩

local instance : Group (H →ₐ[k] k) := hopfPointGroup

omit [IsAlgClosed k] in
private theorem matrixUnit_mulVec_ne_zero (M : (Matrix ι ι k)ˣ) (v : NonzeroVector k ι) :
    M.val *ᵥ v.val ≠ 0 := by
  intro h
  have hEq := congrArg (M.inv *ᵥ ·) h
  change M.inv *ᵥ (M.val *ᵥ v.val) = M.inv *ᵥ (0 : ι → k) at hEq
  rw [Matrix.mulVec_mulVec, M.inv_val, Matrix.one_mulVec, Matrix.mulVec_zero] at hEq
  exact v.2 hEq

variable (U : (Matrix ι ι H)ˣ)
  (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
  (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)

local notation "Γ" => ((H →ₐ[k] k) × kˣ)

private def puncturedOrbitAction : MulAction Γ (NonzeroVector k ι) where
  smul p v := ⟨(p.2 : k) • ((hopfPointMatrix U hD he p.1).val *ᵥ v.val),
    smul_ne_zero p.2.ne_zero (matrixUnit_mulVec_ne_zero _ v)⟩
  one_smul v := Subtype.ext (by
    change (1 : k) • ((hopfPointMatrix U hD he 1).val *ᵥ v.val) = v.val
    rw [map_one, one_smul, Units.val_one, Matrix.one_mulVec])
  mul_smul p q v := Subtype.ext (by
    change ((p.2 * q.2 : kˣ) : k) • ((hopfPointMatrix U hD he (p.1 * q.1)).val *ᵥ v.val) =
      (p.2 : k) • ((hopfPointMatrix U hD he p.1).val *ᵥ
        ((q.2 : k) • ((hopfPointMatrix U hD he q.1).val *ᵥ v.val)))
    rw [map_mul, Units.val_mul, Units.val_mul, Matrix.mulVec_smul, smul_smul, Matrix.mulVec_mulVec])

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem puncturedOrbitAction_continuous :
    letI := puncturedOrbitAction U hD he
    ContinuousConstSMul Γ (NonzeroVector k ι) := by
  letI := puncturedOrbitAction U hD he
  refine ⟨fun g => ?_⟩
  let M := (g.2 : k) • (hopfPointMatrix U hD he g.1).val
  apply puncturedAffinePrime_inducing.continuous_iff.mpr
  have h : puncturedAffinePrime ∘ (g • ·) =
      PrimeSpectrum.comap (matrixPolynomialSubstitution M).toRingHom ∘ puncturedAffinePrime := by
    funext v
    change rationalPrime (MvPolynomial.aeval ((g • v : NonzeroVector k ι).val)) =
      PrimeSpectrum.comap _ (rationalPrime (MvPolynomial.aeval v.val))
    rw [rationalPrime_comap]
    apply congrArg rationalPrime
    apply AlgHom.ext
    intro q
    change MvPolynomial.aeval ((g.2 : k) • ((hopfPointMatrix U hD he g.1).val *ᵥ v.val)) q = _
    rw [← Matrix.smul_mulVec_assoc, AlgHom.comp_apply, MvPolynomial.aeval_def, MvPolynomial.aeval_def]
    rw [eval₂_matrixPolynomialSubstitution, Algebra.id.map_eq_id]
    change MvPolynomial.eval₂ (RingHom.id k) (M *ᵥ v.val) q =
      MvPolynomial.eval₂ (RingHom.id k) (M.map id *ᵥ v.val) q
    rw [Matrix.map_id]
  rw [h]
  exact (PrimeSpectrum.comap _).continuous.comp puncturedAffinePrime_inducing.continuous

private theorem orbit_eq_preimage (v : NonzeroVector k ι) :
    letI := puncturedOrbitAction U hD he
    MulAction.orbit Γ v = puncturedAffinePrime ⁻¹' range
      (PrimeSpectrum.comap (puncturedOrbitEvaluation U.val v.val).toRingHom) := by
  letI := puncturedOrbitAction U hD he
  ext w
  constructor
  · rintro ⟨⟨p, c⟩, rfl⟩
    refine ⟨rationalPrime (evalLaurentPoint p c), ?_⟩
    rw [rationalPrime_comap, puncturedOrbitEvaluation_laurentPoint]
    rfl
  · intro hw
    obtain ⟨p, c, h⟩ := exists_orbitPoint_of_mem_range U.val v.val w.val hw
    exact ⟨(p, c), Subtype.ext h.symm⟩

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem prime_image_orbit (v : NonzeroVector k ι) :
    letI := puncturedOrbitAction U hD he
    puncturedAffinePrime '' MulAction.orbit Γ v =
      PrimeSpectrum.comap (puncturedOrbitEvaluation U.val v.val).toRingHom ''
        range (rationalPrime (k := k) (A := LaurentPolynomial H)) := by
  letI := puncturedOrbitAction U hD he
  ext x
  constructor
  · rintro ⟨_, ⟨⟨p, c⟩, rfl⟩, rfl⟩
    refine ⟨rationalPrime (evalLaurentPoint p c), ⟨_, rfl⟩, ?_⟩
    rw [rationalPrime_comap, puncturedOrbitEvaluation_laurentPoint]
    rfl
  · rintro ⟨_, ⟨e, rfl⟩, rfl⟩
    let c := ((LaurentPolynomial.isUnit_T (R := H) 1).map e).unit
    have hc : (c : k) = e (LaurentPolynomial.T 1) := IsUnit.unit_spec _
    let p := e.comp (IsScalarTower.toAlgHom k H (LaurentPolynomial H))
    refine ⟨(p, c) • v, ⟨(p, c), rfl⟩, ?_⟩
    rw [rationalPrime_comap, puncturedOrbitEvaluation_atPoint]
    change rationalPrime (MvPolynomial.aeval ((c : k) • ((U.val.map p) *ᵥ v.val))) = _
    rw [hc]

include hD he in
/-- Some projective orbit consists of every nonzero vector of its affine cone, up to scale. -/
theorem exists_closed_projectiveOrbit [Nonempty ι] :
    ∃ v : ι → k, v ≠ 0 ∧ ∀ w : ι → k, w ≠ 0 →
      (∀ q ∈ orbitConeIdeal U.val v, MvPolynomial.aeval w q = 0) →
      ∃ (p : H →ₐ[k] k) (c : kˣ), w = (c : k) • ((U.val.map p) *ᵥ v) := by
  classical
  letI := puncturedOrbitAction U hD he
  letI := puncturedOrbitAction_continuous U hD he
  letI : IsNoetherianRing (MvPolynomial ι k) := inferInstance
  letI := puncturedAffinePrime_inducing (k := k) (ι := ι) |>.noetherianSpace
  letI : Nonempty (NonzeroVector k ι) := ⟨⟨fun _ => 1, fun e => one_ne_zero
    (congrFun e (Classical.choice ‹Nonempty ι›))⟩⟩
  letI : Algebra.FiniteType k (LaurentPolynomial H) := laurentPolynomial_finiteType (H := H)
  obtain ⟨v, hClosed⟩ := exists_closed_orbit (G := Γ) (X := NonzeroVector k ι) fun v => by
    let f := puncturedOrbitEvaluation U.val v.val
    letI : Algebra (MvPolynomial ι k) (LaurentPolynomial H) := f.toRingHom.toAlgebra
    letI : IsScalarTower k (MvPolynomial ι k) (LaurentPolynomial H) := IsScalarTower.of_algHom f
    letI := Algebra.FiniteType.of_restrictScalars_finiteType k (MvPolynomial ι k) (LaurentPolynomial H)
    have hfp : f.toRingHom.FinitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    rw [orbit_eq_preimage U hD he]
    exact (PrimeSpectrum.isConstructible_range_comap hfp).preimage
      puncturedAffinePrime_inducing.continuous (fun _ _ _ => by intro _ _ _; exact NoetherianSpace.isCompact _)
  refine ⟨v.val, v.2, fun w hw h => ?_⟩
  let W : NonzeroVector k ι := ⟨w, hw⟩
  let f := (puncturedOrbitEvaluation U.val v.val).toRingHom
  have hZero : puncturedAffinePrime W ∈ closure (range (PrimeSpectrum.comap f)) := by
    rw [PrimeSpectrum.closure_range_comap, puncturedOrbitEvaluation_ker, PrimeSpectrum.mem_zeroLocus]
    exact h
  have hDense := rationalPrime_dense (k := k) (A := LaurentPolynomial H)
  have hSame : range (PrimeSpectrum.comap f) ⊆ closure (puncturedAffinePrime '' MulAction.orbit Γ v) := by
    rw [prime_image_orbit U hD he]
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact image_closure_subset_closure_image (PrimeSpectrum.comap f).continuous ⟨y, hDense y, rfl⟩
  have hW : W ∈ MulAction.orbit Γ v := by
    rw [← hClosed.closure_eq, puncturedAffinePrime_inducing.closure_eq_preimage_closure_image]
    exact closure_minimal hSame isClosed_closure hZero
  obtain ⟨⟨p, c⟩, hp⟩ := hW
  exact ⟨p, c, (congrArg Subtype.val hp).symm⟩

end Orbits

end WideE
