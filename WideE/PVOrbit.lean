import WideE.PVTorsor
import TensorConstants

/-! The ordinary point evaluates the PV coaction to its transition matrix. -/

open scoped TensorProduct WideE Matrix
open TensorProduct StrictEUnit

noncomputable section

namespace WideE

attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule Subalgebra.toCommRing

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 80000

section Point

variable {k S H : Type*} [CommRing k] [CommRing S] [CommRing H] [Algebra k S] [Algebra k H]

/-- Evaluate the torsor factor at a specified point. -/
def tensorEvaluationAt (p : S →ₐ[k] k) : S ⊗[k] H →ₐ[k] H :=
  Algebra.TensorProduct.lift ((Algebra.ofId k H).comp p) (AlgHom.id k H) (fun _ _ => Commute.all _ _)

@[simp] theorem tensorEvaluationAt_tmul (p : S →ₐ[k] k) (s : S) (h : H) :
    tensorEvaluationAt p (s ⊗ₜ[k] h) = algebraMap k H (p s) * h := rfl

end Point

section Counit

variable {k S H J : Type*} [Field k] [CommRing S] [CommRing H] [CommRing J]
  [Algebra k S] [Bialgebra k H] [Bialgebra k J]

private theorem tensorEvaluationAt_counit (p : S →ₐ[k] k) (π : H →ₐ[k] J)
    (hπ : ∀ h, Bialgebra.counitAlgHom k J (π h) = Bialgebra.counitAlgHom k H h)
    (z : S ⊗[k] H) :
    Bialgebra.counitAlgHom k J (tensorEvaluationAt p (Algebra.TensorProduct.map (AlgHom.id k S) π z)) =
      p (coactionCounit z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul s h =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, tensorEvaluationAt_tmul,
      map_mul, hπ, coactionCounit, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
      Algebra.ofId_apply, p.commutes]
    rw [(Bialgebra.counitAlgHom k J).commutes, Algebra.id.map_eq_id, RingHom.id_apply]
    rfl

end Counit

section Differential

variable {k S H J ι : Type*} [Field k] [CommRing S] [CommRing H] [CommRing J]
  [Algebra k S] [Algebra k H] [Algebra k J] [Fintype ι] [DecidableEq ι]

private theorem matrix_coaction_of_differential (p : S →ₐ[k] k)
    (δ : Derivation k S S) (hConstants : ∀ s, δ s = 0 → ∃ c : k, algebraMap k S c = s)
    (ρ : S →ₐ[k] S ⊗[k] J)
    (hρ : ∀ s, tensorDerivation δ (ρ s) = ρ (δ s))
    (U : (Matrix ι ι S)ˣ) (B : Matrix ι ι S)
    (hU : matrixDerivative δ U.val = B * U.val) (h₀ : U.val.map p = 1)
    (hB : B.map ρ = B.map (fun s => s ⊗ₜ[k] (1 : J))) :
    U.val.map ρ = U.val.map (fun s => s ⊗ₜ[k] (1 : J)) *
      (U.val.map ((tensorEvaluationAt p).comp ρ)).map (fun h => (1 : S) ⊗ₜ[k] h) := by
  let iL : S →ₐ[k] S ⊗[k] J := Algebra.TensorProduct.includeLeft
  let Y := Units.map iL.toRingHom.mapMatrix.toMonoidHom U
  let Z := U.val.map ρ
  let D := tensorDerivation (H := J) δ
  have hY : matrixDerivative D Y.val = B.map iL * Y.val := by
    have he := matrixDerivative_map δ D iL.toRingHom (fun s => tensorDerivation_tmul δ s (1 : J)) U.val
    rw [hU, map_mul] at he
    exact he
  have hZ : matrixDerivative D Z = B.map iL * Z := by
    have he := matrixDerivative_map δ D ρ.toRingHom hρ U.val
    rw [hU, map_mul] at he
    change matrixDerivative D Z = B.map ρ * Z at he
    exact hB ▸ he
  let W := (Y⁻¹).val * Z
  have hW : matrixDerivative D W = 0 :=
    fundamental_matrix_transition_constant D (B.map iL) Y Z hY hZ
  have hC (i j : ι) : ∃ c : J, (1 : S) ⊗ₜ[k] c = W i j :=
    (tensorDerivation_constants δ hConstants (W i j)).mp
      (congrArg (fun M : Matrix ι ι (S ⊗[k] J) => M i j) hW)
  choose C hC using hC
  let C₀ : Matrix ι ι J := C
  let iR : J →ₐ[k] S ⊗[k] J := Algebra.TensorProduct.includeRight
  have hW' : C₀.map iR = W := by
    ext i j
    exact hC i j
  have hEq : Z = Y.val * C₀.map iR := by
    rw [hW']
    change Z = Y.val * ((Y⁻¹).val * Z)
    rw [← mul_assoc, Units.mul_inv, one_mul]
  let E : S ⊗[k] J →ₐ[k] J := tensorEvaluationAt p
  have hYE : Y.val.map E = 1 := by
    have hm : Y.val.map E = (U.val.map p).map (algebraMap k J) := by
      ext i j
      change E (U.val i j ⊗ₜ[k] (1 : J)) = algebraMap k J (p (U.val i j))
      rw [tensorEvaluationAt_tmul, mul_one]
    rw [hm, h₀, Matrix.map_one _ (map_zero _) (map_one _)]
  have hCE : (C₀.map iR).map E = C₀ := by
    ext i j
    change E ((1 : S) ⊗ₜ[k] C i j) = C i j
    rw [tensorEvaluationAt_tmul, map_one, map_one, one_mul]
  have hZE : Z.map E = C₀ := by
    have hm := congrArg E.toRingHom.mapMatrix hEq
    rw [map_mul] at hm
    change Z.map E = Y.val.map E * (C₀.map iR).map E at hm
    simpa only [hYE, hCE, one_mul] using hm
  change Z = Y.val * (Z.map E).map iR
  rw [hZE]
  exact hEq

private theorem tensorDerivation_mapRight (δ : Derivation k S S) (π : H →ₐ[k] J)
    (z : S ⊗[k] H) :
    tensorDerivation δ (Algebra.TensorProduct.map (AlgHom.id k S) π z) =
    Algebra.TensorProduct.map (AlgHom.id k S) π (tensorDerivation δ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul s h => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, tensorDerivation_tmul]

end Differential

section Ordinary

variable {K : Type*} [Field K] [CharZero K] {r : ℕ}
  (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))

local notation "R" => (LaurentPolynomial K)
local notation "S" => (ordinaryPVAlgebra A)
local notation "G" => (ordinaryPVGroup A)
local notation "Y" => (Units.val (ordinaryPVMatrix A))

local instance orbitPVCommRing : CommRing S := (ordinaryPVAlgebra A).toCommRing
local instance orbitPVAddCommMonoid : AddCommMonoid S := (ordinaryPVAlgebra A).toSemiring.toAddCommMonoid
local instance orbitPVBaseAlgebra : Algebra R S := (ordinaryPVAlgebra A).algebra
local instance orbitPVCoeffAlgebra : Algebra K S := (ordinaryPVAlgebra A).algebra'
local instance orbitPVBaseModule : Module R S := Algebra.toModule
local instance orbitPVCoeffModule : Module K S := Algebra.toModule

section Quotient

variable {J : Type*} [CommRing J] [Algebra K J] (π : ordinaryPVGroup A →ₐ[K] J)

/-- Restrict the coaction to a given quotient of the constant algebra. -/
def ordinaryPVRestrictedCoaction : S →ₐ[R] S ⊗[K] J :=
  (Algebra.TensorProduct.map (AlgHom.id R S) π).comp (ordinaryPVCoaction A)

/-- Restrict the orbit of the normalized ordinary point to the constant quotient. -/
def ordinaryPVOrbit : S →ₐ[K] J :=
  (tensorEvaluationAt ((ordinaryPVAtOne A).restrictScalars K)).comp
    ((ordinaryPVRestrictedCoaction A π).restrictScalars K)

/-- The coaction on the matrix is given by its orbit at the ordinary point. -/
theorem ordinaryPVRestrictedCoaction_matrix :
    (Y).map (ordinaryPVRestrictedCoaction A π) =
      (Y).map (fun s => s ⊗ₜ[K] (1 : J)) *
        ((Y).map (ordinaryPVOrbit A π)).map (fun h => (1 : S) ⊗ₜ[K] h) := by
  let ρ := (ordinaryPVRestrictedCoaction A π).restrictScalars K
  let δ := ordinaryPVDerivation A
  let mapπ := Algebra.TensorProduct.map (AlgHom.id K S) π
  have hρ (s : S) : tensorDerivation δ (ρ s) = ρ (δ s) := by
    change tensorDerivation δ (mapπ (ordinaryPVCoaction A s)) = mapπ (ordinaryPVCoaction A (δ s))
    rw [tensorDerivation_mapRight, ordinaryPVCoaction_differential]
  refine matrix_coaction_of_differential ((ordinaryPVAtOne A).restrictScalars K) δ
    (ordinaryPV_constants A) ρ hρ (ordinaryPVMatrix A) (A.map (algebraMap R S))
    (ordinaryPVMatrix_derivation A) (ordinaryPVAtOne_matrix A) ?_
  ext i j
  exact (ordinaryPVRestrictedCoaction A π).commutes (A i j)

@[simp] theorem ordinaryPVOrbit_algebraMap (b : R) :
    ordinaryPVOrbit A π (algebraMap R S b) = algebraMap K J (evalAtOne K b) := by
  let p := (ordinaryPVAtOne A).restrictScalars K
  change tensorEvaluationAt p (ordinaryPVRestrictedCoaction A π (algebraMap R S b)) = _
  rw [AlgHom.commutes]
  change tensorEvaluationAt p ((algebraMap R S b) ⊗ₜ[K] (1 : J)) = _
  rw [tensorEvaluationAt_tmul, mul_one]
  exact congrArg (algebraMap K J) ((ordinaryPVAtOne A).commutes b)

end Quotient

/-- Restricting to a group quotient compatible with the counit preserves the ordinary point. -/
theorem ordinaryPVOrbit_counit {J : Type*} [CommRing J] [Bialgebra K J]
    (π : ordinaryPVGroup A →ₐ[K] J)
    (hπ : ∀ h, Bialgebra.counitAlgHom K J (π h) =
      letI := ordinaryPVHopf A; Bialgebra.counitAlgHom K G h) (s : S) :
    Bialgebra.counitAlgHom K J (ordinaryPVOrbit A π s) = ordinaryPVAtOne A s := by
  letI := ordinaryPVHopf A
  let p := (ordinaryPVAtOne A).restrictScalars K
  let ρ := ordinaryPVCoaction A
  have hε : coactionCounit (ρ s) = s := (ordinaryPVTorsor A).counital s
  have h := tensorEvaluationAt_counit p π hπ (ρ s)
  exact h.trans (congrArg p hε)

end Ordinary

end WideE
