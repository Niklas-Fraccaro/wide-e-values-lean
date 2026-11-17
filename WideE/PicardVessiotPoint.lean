import WideE.PicardVessiot
import AlgebraicFiber
import MatrixGeneratedChangeBasis

/-! The canonical point of the ordinary Picard–Vessiot algebra at one. -/

noncomputable section

open scoped TensorProduct WideE

namespace WideE

open StrictEUnit

private def pointedFiberChart {k B S H : Type*} [Field k] [CommRing B] [CommRing S] [CommRing H]
    [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S]
    [Algebra B k] [IsScalarTower k B k] [Algebra k H]
    (e : S ⊗[k] H ≃ₐ[S] S ⊗[B] S) (p : (k ⊗[B] S) →ₐ[k] k) :
    (k ⊗[B] S) ≃ₐ[k] H :=
  pointedTorsorEquiv (algebraicFiberCoaction e) p (algebraicFiberCanonical_bijective e)

variable (K : Type*) [Field K]

local instance : Algebra (LaurentPolynomial K) (PowerSeries K) :=
  (formalAtOne K).toRingHom.toAlgebra

private def ordinaryPowerInclusion : PowerSeries K →ₐ[LaurentPolynomial K] LaurentSeries K where
  toRingHom := (powerSeriesInLaurent K).toRingHom
  commutes' _ := rfl

variable {K} {r : ℕ} (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))

local instance : CommRing (ordinaryPVAlgebra A) := (ordinaryPVAlgebra A).toCommRing
local instance : AddCommMonoid (ordinaryPVAlgebra A) := (ordinaryPVAlgebra A).toSemiring.toAddCommMonoid
local instance : Algebra (LaurentPolynomial K) (ordinaryPVAlgebra A) := (ordinaryPVAlgebra A).algebra
local instance : Module (LaurentPolynomial K) (ordinaryPVAlgebra A) := Algebra.toModule
local instance : Algebra K (ordinaryPVAlgebra A) := (ordinaryPVAlgebra A).algebra'

private theorem ordinaryPVAlgebra_le_powerSeries :
    ordinaryPVAlgebra A ≤ (ordinaryPowerInclusion K).range := by
  let Y := ordinaryFundamentalPower A
  let f := ordinaryPowerInclusion K
  have hY : ordinaryFundamental A = Y.map f := rfl
  have hdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det _).mp
    (formalFundamentalMatrix_isUnit (A.map (formalAtOne K)))
  apply (matrixGeneratedAlgebra_le_iff _ _).mpr
  refine ⟨?_, fun i j => ⟨Y i j, rfl⟩⟩
  obtain ⟨d, hd⟩ := hdet
  have hd' : f (d : PowerSeries K) = (ordinaryFundamental A).det := by
    rw [hd, hY]
    exact f.toRingHom.map_det Y
  have hprod : (ordinaryFundamental A).det * f (↑d⁻¹ : PowerSeries K) = 1 := by
    rw [← hd', ← map_mul, Units.mul_inv, map_one]
  exact ⟨↑d⁻¹, (inv_eq_of_mul_eq_one_right hprod).symm⟩

/-- Write a Picard–Vessiot element as a regular power series at the ordinary point. -/
def ordinaryPVToPowerSeries : ordinaryPVAlgebra A →ₐ[LaurentPolynomial K] PowerSeries K :=
  (AlgEquiv.ofInjective (ordinaryPowerInclusion K)
    HahnSeries.ofPowerSeries_injective).symm.toAlgHom.comp
      (Subalgebra.inclusion (ordinaryPVAlgebra_le_powerSeries A))

@[simp] theorem ordinaryPVToPowerSeries_embed (x : ordinaryPVAlgebra A) :
    powerSeriesInLaurent K (ordinaryPVToPowerSeries A x) = x.val := by
  let e := AlgEquiv.ofInjective (ordinaryPowerInclusion K) HahnSeries.ofPowerSeries_injective
  let i := Subalgebra.inclusion (ordinaryPVAlgebra_le_powerSeries A)
  change (ordinaryPowerInclusion K) (e.symm (i x)) = x.val
  exact congrArg Subtype.val (e.apply_symm_apply (i x))

/-- Take the constant coefficient after expressing the element in the ordinary coordinate. -/
def ordinaryPVAtOne : ordinaryPVAlgebra A →ₐ[LaurentPolynomial K] K where
  toRingHom := (PowerSeries.constantCoeff K).comp (ordinaryPVToPowerSeries A).toRingHom
  commutes' f := by
    change PowerSeries.constantCoeff K (ordinaryPVToPowerSeries A (algebraMap _ _ f)) =
      evalAtOne K f
    rw [AlgHom.commutes]
    exact formalAtOne_constantCoeff K f

theorem ordinaryPVToPowerSeries_matrix :
    (ordinaryPVMatrix A).val.map (ordinaryPVToPowerSeries A) = ordinaryFundamentalPower A := by
  apply Matrix.ext
  intro i j
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  change powerSeriesInLaurent K (ordinaryPVToPowerSeries A ((ordinaryPVMatrix A).val i j)) =
    powerSeriesInLaurent K (ordinaryFundamentalPower A i j)
  rw [ordinaryPVToPowerSeries_embed]
  rfl

@[simp] theorem ordinaryPVAtOne_matrix :
    (ordinaryPVMatrix A).val.map (ordinaryPVAtOne A) = 1 := by
  change ((ordinaryPVMatrix A).val.map (ordinaryPVToPowerSeries A)).map
    (PowerSeries.constantCoeff K) = 1
  rw [ordinaryPVToPowerSeries_matrix, ordinaryFundamentalPower_atOne]

/-- The algebraic fiber is pointed by the normalized fundamental solution. -/
def ordinaryPVFiberPoint : (K ⊗[LaurentPolynomial K] ordinaryPVAlgebra A) →ₐ[K] K :=
  Algebra.TensorProduct.lift (AlgHom.id K K) (ordinaryPVAtOne A) (fun _ _ => Commute.all _ _)

@[simp] theorem ordinaryPVFiberPoint_tmul (a : K) (x : ordinaryPVAlgebra A) :
    ordinaryPVFiberPoint A (a ⊗ₜ[LaurentPolynomial K] x) = a * ordinaryPVAtOne A x :=
  rfl

set_option maxHeartbeats 1200000 in
/-- Trivialize the algebraic fiber at the point supplied by the formal normalization. -/
def ordinaryPVPointedChart [CharZero K] :
    K ⊗[LaurentPolynomial K] ordinaryPVAlgebra A ≃ₐ[K] ordinaryPVGroup A :=
  pointedFiberChart (ordinaryPV_chart A) (ordinaryPVFiberPoint A)

theorem ordinaryPVGroup_finiteType [CharZero K] : Algebra.FiniteType K (ordinaryPVGroup A) := by
  letI := candidate_finiteType (B := LaurentPolynomial K) (ordinaryFundamental A)
  exact Algebra.FiniteType.equiv (algebraicFiber_finiteType (B := LaurentPolynomial K))
    (ordinaryPVPointedChart A)

end WideE
