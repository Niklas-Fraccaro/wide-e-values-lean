import WideE.ProjectiveOrbitTwist
import WideE.ProjectiveSection

/-! Primitive coordinates for a given generic point of the twisted equations. -/

open scoped TensorProduct Matrix

noncomputable section

namespace WideE

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 80000

attribute [local instance] MvPolynomial.gradedAlgebra

section ProjectiveIdeal

variable {R F ι : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [Algebra R F] [IsFractionRing R F] [Fintype ι]

/-- The primitive extension solves every homogeneous ideal equation and lies
on the same projective line at the generic point. -/
theorem projectiveIdeal_extend_to_pid (J : Ideal (MvPolynomial ι R))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι R))
    (x : ι → F) (hx : x ≠ 0) (hEq : ∀ p ∈ J, p.eval₂ (algebraMap R F) x = 0) :
    ∃ (y : ι → R) (c : Fˣ), Ideal.span (Set.range y) = ⊤ ∧
      (algebraMap R F ∘ y) = (c : F) • x ∧ ∀ p ∈ J, p.eval y = 0 := by
  obtain ⟨y, hy, c, hc⟩ := exists_primitive_coordinates (R := R) x hx
  refine ⟨y, c, hy, funext hc, ?_⟩
  intro p hp
  have h : MvPolynomial.eval y (∑ d ∈ Finset.range (p.totalDegree + 1),
      MvPolynomial.homogeneousComponent d p) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro d _
    let p' := MvPolynomial.homogeneousComponent d p
    have hp' : p' ∈ J := by
      have hm := (Ideal.IsHomogeneous.mem_iff _ hJ).mp hp d
      change (MvPolynomial.decomposition.decompose' p d : MvPolynomial ι R) ∈ J at hm
      rwa [MvPolynomial.decomposition.decompose'_apply] at hm
    apply IsFractionRing.injective R F
    rw [map_zero, MvPolynomial.eval₂_comp, show (algebraMap R F ∘ y) = fun i => (c : F) * x i from
      funext hc, homogeneous_eval₂_scale _ _ (MvPolynomial.homogeneousComponent_isHomogeneous d p),
      hEq p' hp', mul_zero]
  rwa [MvPolynomial.sum_homogeneousComponent] at h

end ProjectiveIdeal

section TwistPoints

variable {k R S F ι : Type*} [Field k] [CommRing R] [CommRing S] [Field F]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
  [Algebra k F] [Algebra R F] [IsScalarTower k R F] [Fintype ι] [DecidableEq ι]

/-- A generic torsor point carries a solution of the original equations to
a solution of the descended equations by the inverse frame matrix. -/
theorem exists_twistedPolynomialIdeal_fractionPoint
    (I : Ideal (MvPolynomial ι k)) (J : Ideal (MvPolynomial ι R)) (g : (Matrix ι ι S)ˣ)
    (hJ : J.map (MvPolynomial.map (algebraMap R S)) = twistedPolynomialIdeal I g.val)
    (p : S →ₐ[R] F) (v : ι → k) (hv : v ≠ 0) (hEq : ∀ q ∈ I, q.eval v = 0) :
    ∃ x : ι → F, x ≠ 0 ∧ g.val.map p.toRingHom *ᵥ x = (algebraMap k F ∘ v) ∧
      ∀ q ∈ J, q.eval₂ (algebraMap R F) x = 0 := by
  let W : (Matrix ι ι F)ˣ := Units.map p.toRingHom.mapMatrix.toMonoidHom g
  let x := (W⁻¹).val *ᵥ (algebraMap k F ∘ v)
  have hMap : W.val *ᵥ x = (algebraMap k F ∘ v) := by
    change W.val *ᵥ ((W⁻¹).val *ᵥ (algebraMap k F ∘ v)) = _
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  refine ⟨x, ?_, hMap, ?_⟩
  · intro hx
    rw [hx, Matrix.mulVec_zero] at hMap
    apply hv
    funext i
    apply (algebraMap k F).injective
    simpa only [Function.comp_apply, Pi.zero_apply, map_zero] using (congrFun hMap i).symm
  · have hScalar : p.toRingHom.comp (algebraMap k S) = algebraMap k F :=
      RingHom.ext (p.restrictScalars k).commutes
    let ev := MvPolynomial.eval₂Hom p.toRingHom x
    have hTwisted : twistedPolynomialIdeal I g.val ≤ RingHom.ker ev := by
      unfold twistedPolynomialIdeal
      rw [Ideal.map_map]
      apply (Ideal.map_le_iff_le_comap).mpr
      intro q hq
      change (matrixPolynomialSubstitution g.val (MvPolynomial.map (algebraMap k S) q)).eval₂
        p.toRingHom x = 0
      rw [eval₂_matrixPolynomialSubstitution, show g.val.map p.toRingHom *ᵥ x = _ from hMap,
        MvPolynomial.eval₂_map, hScalar, ← MvPolynomial.eval₂_comp, hEq q hq, map_zero]
    intro q hq
    have h := Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap R S)) hq
    rw [hJ] at h
    have hz := RingHom.mem_ker.mp (hTwisted h)
    change (MvPolynomial.map (algebraMap R S) q).eval₂ p.toRingHom x = 0 at hz
    have hCoeff : p.toRingHom.comp (algebraMap R S) = algebraMap R F := RingHom.ext p.commutes
    rwa [MvPolynomial.eval₂_map, hCoeff] at hz

/-- A generic point gives primitive base coordinates whose image under the
generic frame is a unit multiple of the original vector. -/
theorem exists_twistedPolynomialIdeal_primitivePoint [IsDomain R] [IsPrincipalIdealRing R]
    [IsFractionRing R F] (I : Ideal (MvPolynomial ι k)) (J : Ideal (MvPolynomial ι R))
    (g : (Matrix ι ι S)ˣ) (hHom : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι R))
    (hJ : J.map (MvPolynomial.map (algebraMap R S)) = twistedPolynomialIdeal I g.val)
    (p : S →ₐ[R] F) (v : ι → k) (hv : v ≠ 0) (hEq : ∀ q ∈ I, q.eval v = 0) :
    ∃ (y : ι → R) (c : Fˣ), Ideal.span (Set.range y) = ⊤ ∧
      g.val.map p.toRingHom *ᵥ (algebraMap R F ∘ y) = (c : F) • (algebraMap k F ∘ v) ∧
      ∀ q ∈ J, q.eval y = 0 := by
  obtain ⟨x, hx, hgx, hxEq⟩ := exists_twistedPolynomialIdeal_fractionPoint I J g hJ p v hv hEq
  obtain ⟨y, c, hy, hc, hyEq⟩ := projectiveIdeal_extend_to_pid J hHom x hx hxEq
  refine ⟨y, c, hy, ?_, hyEq⟩
  rw [hc, Matrix.mulVec_smul, hgx]

end TwistPoints

end WideE
