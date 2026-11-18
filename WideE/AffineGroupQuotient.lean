import WideE.EquivariantOrbitFlatness
import WideE.GaloisKernelReduction
import WideE.ScalarGroupQuotient

/-! Faithful flatness of injective coordinate maps of connected affine groups. -/

noncomputable section

open scoped TensorProduct

namespace WideE

section Translation

variable {k H : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H]

/-- Left translation on the coordinate ring realizes multiplication on points. -/
theorem hopfPointMul_eq_comp_translate (p q : H →ₐ[k] k) :
    hopfPointMul p q = q.comp (hopfTranslate p) := by
  apply AlgHom.ext
  intro a
  change tensorPoint p q (Bialgebra.comulAlgHom k H a) =
    q (Algebra.TensorProduct.lid k H
      (Algebra.TensorProduct.map p (AlgHom.id k H) (Bialgebra.comulAlgHom k H a)))
  generalize Bialgebra.comulAlgHom k H a = z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    simp only [tensorPoint_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul,
      AlgHom.id_apply, Algebra.smul_def, map_mul, AlgHom.commutes]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Translation

section Quotient

universe u

variable {k Q H : Type u} [Field k] [IsAlgClosed k] [CommRing Q] [CommRing H]
  [HopfAlgebra k Q] [HopfAlgebra k H]

omit [IsAlgClosed k] in
private theorem exists_hopfTranslation_between_points
    (j : Q →ₐc[k] H) (p q : H →ₐ[k] k) :
    ∃ (eQ : Q ≃ₐ[k] Q) (eH : H ≃ₐ[k] H),
      eH.toAlgHom.comp (j : Q →ₐ[k] H) = (j : Q →ₐ[k] H).comp eQ.toAlgHom ∧
      p.comp eH.toAlgHom = q := by
  letI := hopfPointGroup (k := k) (H := H) (A := k)
  let r := q * p⁻¹
  refine ⟨hopfTranslation (r.comp (j : Q →ₐ[k] H)), hopfTranslation r,
    hopfTranslate_comp_bialgHom j r, ?_⟩
  rw [hopfTranslation_toAlgHom, ← hopfPointMul_eq_comp_translate]
  change (q * p⁻¹) * p = q
  rw [mul_assoc, inv_mul_cancel, mul_one]

/-- An open image of a group map to an integral affine group contains every
rational point. -/
theorem affineGroupMap_lift_kPoints_of_open [IsDomain Q]
    [Algebra.FiniteType k Q] [Algebra.FiniteType k H]
    (j : Q →ₐc[k] H) (hOpen : IsOpenMap (PrimeSpectrum.comap (j : Q →ₐ[k] H).toRingHom))
    (p : Q →ₐ[k] k) : ∃ r : H →ₐ[k] k, r.comp (j : Q →ₐ[k] H) = p := by
  classical
  let f : Q →ₐ[k] H := j
  let U := Set.range (PrimeSpectrum.comap f.toRingHom)
  have hU : IsOpen U := by
    change IsOpen (Set.range (PrimeSpectrum.comap f.toRingHom))
    rw [← Set.image_univ]
    exact hOpen Set.univ isOpen_univ
  have hUne : U.Nonempty := ⟨_, ⟨hopfPointPrime (Bialgebra.counitAlgHom k H), rfl⟩⟩
  let τ := PrimeSpectrum.comap (hopfTranslate p).toRingHom
  have hτ : IsHomeomorph τ :=
    PrimeSpectrum.isHomeomorph_comap_of_bijective (hopfTranslation p).bijective
  have hOp := hU.preimage hτ.continuous
  have hne : (U ∩ τ ⁻¹' U).Nonempty := by
    refine nonempty_preirreducible_inter hU hOp hUne ?_
    obtain ⟨x, hx⟩ := hUne
    obtain ⟨y, rfl⟩ := hτ.surjective x
    exact ⟨y, hx⟩
  letI : IsJacobsonRing Q := isJacobsonRing_of_finiteType (A := k) (B := Q)
  obtain ⟨y, ⟨hy, hyτ⟩, hyClosed⟩ :=
    PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing _ (hU.inter hOp) hne
  letI : y.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hyClosed
  let q := StrictEUnit.maximalIdealPoint (k := k) y.asIdeal
  have hq : hopfPointPrime q = y := PrimeSpectrum.ext (StrictEUnit.maximalIdealPoint_ker _)
  have hmul : hopfPointPrime (hopfPointMul p q) = τ y := by
    rw [hopfPointMul_eq_comp_translate, ← hq]
    rfl
  obtain ⟨a, ha⟩ := lift_rationalPoint_of_mem_range f q (hq.symm ▸ hy)
  obtain ⟨b, hb⟩ := lift_rationalPoint_of_mem_range f (hopfPointMul p q) (hmul.symm ▸ hyτ)
  letI := hopfPointGroup (k := k) (H := H) (A := k)
  letI := hopfPointGroup (k := k) (H := Q) (A := k)
  let ϕ := hopfPointPrecompose (A := k) j
  refine ⟨b * a⁻¹, ?_⟩
  change ϕ (b * a⁻¹) = p
  rw [map_mul, map_inv, show ϕ a = q from ha, show ϕ b = p * q from hb,
    mul_assoc, mul_inv_cancel, mul_one]

/-- An injective map of finite-type Hopf algebras into a domain is faithfully
flat over an algebraically closed field. -/
theorem affineGroupQuotient_faithfullyFlat [IsDomain H]
    [Algebra.FiniteType k Q] [Algebra.FiniteType k H]
    (j : Q →ₐc[k] H) (hj : Function.Injective j) :
    letI : Algebra Q H := (j : Q →ₐ[k] H).toRingHom.toAlgebra
    Module.FaithfullyFlat Q H := by
  let f : Q →ₐ[k] H := j
  letI : IsDomain Q := Function.Injective.isDomain f hj
  letI : Algebra Q H := f.toRingHom.toAlgebra
  letI : IsScalarTower k Q H := IsScalarTower.of_algHom f
  letI : Module.Flat Q H := flat_of_transitive_closedPoints f hj (exists_hopfTranslation_between_points j)
  letI : Algebra.FiniteType Q H := Algebra.FiniteType.of_restrictScalars_finiteType k Q H
  letI : IsNoetherianRing Q := Algebra.FiniteType.isNoetherianRing k Q
  letI : Algebra.FinitePresentation Q H := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact faithfullyFlat_of_lift_kPoints (k := k) (affineGroupMap_lift_kPoints_of_open j
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation)

end Quotient

end WideE
