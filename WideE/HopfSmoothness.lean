import WideE.HopfSmoothLocus
import WideE.PVTorsor
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Flat.Localization

/-! Reducedness of the relative Picard–Vessiot tensor and smoothness of its constant group. -/

noncomputable section

open scoped TensorProduct WideE IntermediateField.algebraAdjoinAdjoin
open TensorProduct

namespace WideE

attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule Subalgebra.toCommRing

set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 60000

universe u

/-- Tensor with the rational field by localizing a polynomial algebra. -/
private theorem tensorFractionField_isDomain {k E L ι : Type u} [Field k] [Field E] [Field L]
    [Algebra k E] [Algebra k L] {x : ι → E} (hx : AlgebraicIndependent k x) :
    IsDomain ((IntermediateField.adjoin k (Set.range x)) ⊗[k] L) := by
  classical
  let D := Algebra.adjoin k (Set.range x)
  let F := IntermediateField.adjoin k (Set.range x)
  let P := D ⊗[k] L
  let T := F ⊗[k] L
  let e : P ≃ₐ[k] MvPolynomial ι L :=
    (Algebra.TensorProduct.congr hx.aevalEquiv.symm (AlgEquiv.refl (R := k) (A₁ := L))).trans
      MvPolynomial.scalarRTensorAlgEquiv
  letI : IsDomain P := Equiv.isDomain e.toRingEquiv
  let i : P →ₐ[D] T :=
    Algebra.TensorProduct.map (Algebra.ofId D F) (AlgHom.id k L)
  letI := i.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom i
  let f : P →ₗ[D] T := (IsScalarTower.toAlgHom D P T).toLinearMap
  have hBase : IsBaseChange F f := by
    apply IsBaseChange.of_equiv (Algebra.TensorProduct.cancelBaseChange k D F F L).toLinearEquiv
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
    | tmul d a =>
      simp only [AlgEquiv.toLinearEquiv_apply, Algebra.TensorProduct.cancelBaseChange_tmul,
        smul_eq_mul, Algebra.smul_def, mul_one]
      rfl
  let M := Algebra.algebraMapSubmonoid P (nonZeroDivisors D)
  letI : IsLocalization M T :=
    (isLocalizedModule_iff_isLocalization (S := nonZeroDivisors D)).mp
      ((isLocalizedModule_iff_isBaseChange (nonZeroDivisors D) F f).mpr hBase)
  apply IsLocalization.isDomain_of_le_nonZeroDivisors (M := M)
  rintro _ ⟨d, hd, rfl⟩
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  have hi : Function.Injective (algebraMap D P) :=
    Algebra.TensorProduct.includeLeft_injective (S := D) (A := D) (B := L)
      (algebraMap k L).injective
  exact (map_ne_zero_iff _ hi).mpr (mem_nonZeroDivisors_iff_ne_zero.mp hd)

/-- A separating transcendence basis gives an embedding into an unramified
algebra of essentially finite type over a field. -/
private theorem tensor_field_isReduced {k E L : Type u} [Field k] [CharZero k]
    [Field E] [Field L] [Algebra k E] [Algebra k L] [Algebra.EssFiniteType k E] :
    IsReduced (E ⊗[k] L) := by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' k E
  let F := IntermediateField.adjoin k (Set.range x)
  let T := F ⊗[k] L
  letI : IsDomain T := tensorFractionField_isDomain hx.1
  let Q := FractionRing T
  letI : Algebra.IsAlgebraic F E := hx.isAlgebraic_field
  letI : CharZero F := Algebra.charZero_of_charZero k F
  letI : Algebra.FormallyEtale F E := Algebra.FormallyEtale.of_isSeparable F E
  letI : Algebra.EssFiniteType F E := Algebra.EssFiniteType.of_comp k F E
  letI : IsReduced (Q ⊗[F] E) := Algebra.FormallyUnramified.isReduced_of_field Q _
  let e := Algebra.TensorProduct.comm F E Q
  letI : IsReduced (E ⊗[F] Q) := isReduced_of_injective e.toRingEquiv e.injective
  let i : T →ₐ[F] Q := IsScalarTower.toAlgHom F T Q
  let j := Algebra.TensorProduct.map (AlgHom.id F E) i
  have hj : Function.Injective j := by
    change Function.Injective (TensorProduct.map (LinearMap.id : E →ₗ[F] E) i.toLinearMap)
    exact TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id (IsFractionRing.injective T Q)
  letI : IsReduced (E ⊗[F] T) := isReduced_of_injective j hj
  let e' := (Algebra.TensorProduct.cancelBaseChange k F E E L).symm
  exact isReduced_of_injective e'.toRingEquiv e'.injective

/-- Flatness embeds the relative tensor ring in the tensor of the fraction fields. -/
private theorem flatDomainTensor_isReduced {R A : Type u} [CommRing R] [IsDomain R] [CharZero R]
    [CommRing A] [IsDomain A] [Algebra R A] [Module.Flat R A] [Algebra.FiniteType R A]
    (hi : Function.Injective (algebraMap R A)) : IsReduced (A ⊗[R] A) := by
  let K := FractionRing R
  let L := FractionRing A
  let i : A →ₐ[R] L := IsScalarTower.toAlgHom R A L
  have hi' : Function.Injective i := IsFractionRing.injective A L
  let j : K →ₐ[R] L := IsFractionRing.liftAlgHom (g := Algebra.ofId R L) (hi'.comp hi)
  letI := j.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom j
  letI : CharZero K := IsFractionRing.charZero_of_isFractionRing R
  letI : Algebra.EssFiniteType A L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors A)
  letI : Algebra.EssFiniteType R L := Algebra.EssFiniteType.comp R A L
  letI : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_comp R K L
  letI : IsReduced (L ⊗[K] L) := tensor_field_isReduced (k := K)
  let e := (IsLocalization.algebraTensorEquiv (nonZeroDivisors R) K L L).symm
  letI : IsReduced (L ⊗[R] L) := isReduced_of_injective e.toRingEquiv e.injective
  letI : Module.Flat A L := IsLocalization.flat L (nonZeroDivisors A)
  letI : Module.Flat R L := Module.Flat.trans R A L
  let t := Algebra.TensorProduct.map i i
  apply isReduced_of_injective t
  change Function.Injective (TensorProduct.map i.toLinearMap i.toLinearMap)
  exact TensorProduct.map_injective_of_flat_flat _ _ hi' hi'

section Ordinary

variable {K : Type u} [Field K] [CharZero K] {r : ℕ}
  (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))

local instance smoothnessPVCommRing : CommRing (ordinaryPVAlgebra A) := (ordinaryPVAlgebra A).toCommRing
local instance smoothnessPVBaseAlgebra : Algebra (LaurentPolynomial K) (ordinaryPVAlgebra A) :=
  (ordinaryPVAlgebra A).algebra
local instance smoothnessPVCoeffAlgebra : Algebra K (ordinaryPVAlgebra A) :=
  (ordinaryPVAlgebra A).algebra'

/-- The actual constant algebra sits in a reduced relative tensor product. -/
theorem ordinaryPVGroup_isReduced : IsReduced (ordinaryPVGroup A) := by
  letI := ordinaryPV_faithfullyFlat A
  letI : CharZero (LaurentPolynomial K) := Algebra.charZero_of_charZero K (LaurentPolynomial K)
  letI : IsReduced (ordinaryPVAlgebra A ⊗[LaurentPolynomial K] ordinaryPVAlgebra A) :=
    flatDomainTensor_isReduced (fun _ _ h => ordinaryLaurentEmbedding_injective (congrArg Subtype.val h))
  constructor
  rintro x ⟨n, hn⟩
  let T := ordinaryPVAlgebra A ⊗[LaurentPolynomial K] ordinaryPVAlgebra A
  have hx : IsNilpotent (x : T) :=
    ⟨n, congrArg (fun a : ordinaryPVGroup A => (a : T)) hn⟩
  exact Subtype.ext hx.eq_zero

/-- Smoothness of the affine group of the actual ordinary Picard–Vessiot algebra. -/
theorem ordinaryPVGroup_smooth [IsAlgClosed K] : Algebra.Smooth K (ordinaryPVGroup A) := by
  letI := ordinaryPVHopf A
  letI := ordinaryPVGroup_finiteType A
  letI := ordinaryPVGroup_isReduced A
  exact hopfSmooth_of_isReduced

end Ordinary

end WideE
