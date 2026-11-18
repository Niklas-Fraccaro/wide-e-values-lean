import WideE.GaloisTorsor
import WideE.LinearDescent

/-! The matrix cocycle and the descended frame of a representation of a constant
Hopf group on an affine torsor. -/

open scoped TensorProduct Matrix

noncomputable section

namespace WideE

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000

section PointDifference

variable {k R S H L L' : Type*}
  [CommRing k] [CommRing R] [CommRing S] [CommRing H] [CommRing L] [CommRing L']
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S] [HopfAlgebra k H]
  [Algebra k L] [Algebra R L] [IsScalarTower k R L]
  [Algebra k L'] [Algebra R L'] [IsScalarTower k R L']

namespace AffineHopfTorsor

variable (T : AffineHopfTorsor k R S H)

/-- Action on points commutes with every homomorphism of target algebras. -/
theorem actPoint_postcompose_algHom (f : L →ₐ[R] L') (p : S →ₐ[R] L) (g : H →ₐ[k] L) :
    f.comp (T.actPoint p g) = T.actPoint (f.comp p) ((f.restrictScalars k).comp g) := by
  let left : S ⊗[k] H →ₐ[R] L := Algebra.TensorProduct.lift p g (fun _ _ => Commute.all _ _)
  let right : S ⊗[k] H →ₐ[R] L' :=
    Algebra.TensorProduct.lift (f.comp p) ((f.restrictScalars k).comp g) (fun _ _ => Commute.all _ _)
  have h : f.comp left = right := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [left, right, AlgHom.comp_apply, Algebra.TensorProduct.lift_tmul,
      AlgHom.restrictScalars_apply, map_mul]
  apply AlgHom.ext
  intro a
  exact DFunLike.congr_fun h (T.coaction a)

/-- The unique group element relating two torsor points commutes with a change of target. -/
theorem pointDifference_postcompose (f : L →ₐ[R] L') (p q : S →ₐ[R] L) :
    (f.restrictScalars k).comp (T.pointDifference p q) =
      T.pointDifference (f.comp p) (f.comp q) := by
  apply T.actPoint_injective (f.comp p)
  rw [← T.actPoint_postcompose_algHom, T.actPoint_pointDifference, T.actPoint_pointDifference]

omit [CommRing L'] [Algebra k L'] [Algebra R L'] [IsScalarTower k R L'] in
/-- Consecutive differences of torsor points multiply to the composite difference. -/
theorem pointDifference_trans (p q r : S →ₐ[R] L) :
    hopfPointMul (T.pointDifference p q) (T.pointDifference q r) =
      T.pointDifference p r := by
  apply T.actPoint_injective p
  rw [← T.actPoint_mul, T.actPoint_pointDifference, T.actPoint_pointDifference,
    T.actPoint_pointDifference]

end AffineHopfTorsor

end PointDifference

section Representation

variable {k H L ι : Type*} [CommRing k] [CommRing H] [CommRing L]
  [Bialgebra k H] [Algebra k L] [Fintype ι]

/-- A matrix with comultiplication given by matrix multiplication respects the
multiplication of group points over each value algebra. -/
theorem matrixRepresentation_map_hopfPointMul (U : Matrix ι ι H)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U i j) = ∑ l, U i l ⊗ₜ[k] U l j)
    (g h : H →ₐ[k] L) :
    U.map (hopfPointMul g h).toRingHom = U.map g.toRingHom * U.map h.toRingHom := by
  apply Matrix.ext
  intro i j
  let ev : H ⊗[k] H →ₐ[k] L := Algebra.TensorProduct.lift g h (fun _ _ => Commute.all _ _)
  change ev (Coalgebra.comul (R := k) (U i j)) = (U.map g.toRingHom * U.map h.toRingHom) i j
  rw [hU]
  simp only [map_sum, ev, Algebra.TensorProduct.lift_tmul, Matrix.mul_apply, Matrix.map_apply,
    AlgHom.coe_toRingHom]
  rfl

end Representation

section TorsorCocycle

variable {k R S H ι : Type*} [CommRing k] [CommRing R] [CommRing S] [CommRing H]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S] [HopfAlgebra k H]

local notation "S₂" => S ⊗[R] S
local notation "S₃" => S ⊗[R] (S ⊗[R] S)
local notation "q₁" => (Algebra.TensorProduct.includeLeft : S →ₐ[R] S₂)
local notation "q₂" => (Algebra.TensorProduct.includeRight : S →ₐ[R] S₂)
local notation "p₁₂" => linearDescent12 R S
local notation "p₁₃" => linearDescent13 R S
local notation "p₂₃" => linearDescent23 R S

namespace AffineHopfTorsor

variable (T : AffineHopfTorsor k R S H)

/-- The difference of the two universal points on the double overlap. -/
def overlapPoint : H →ₐ[k] S₂ := T.pointDifference q₁ q₂

/-- The universal group difference is the group factor of the canonical chart. -/
theorem overlapPoint_apply (a : H) : T.overlapPoint a = T.chart ((1 : S) ⊗ₜ[k] a) := by
  let ev : S₂ →ₐ[R] S₂ := Algebra.TensorProduct.lift q₁ q₂ (fun _ _ => Commute.all _ _)
  have h : ev = AlgHom.id R S₂ := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp only [ev, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul, AlgHom.id_apply]
  change ev (T.chart ((1 : S) ⊗ₜ[k] a)) = T.chart ((1 : S) ⊗ₜ[k] a)
  rw [h, AlgHom.id_apply]

/-- The three differences on the triple overlap satisfy the cocycle equation. -/
theorem overlapPoint_cocycle :
    ((p₁₃).restrictScalars k).comp T.overlapPoint =
      hopfPointMul (((p₁₂).restrictScalars k).comp T.overlapPoint)
        (((p₂₃).restrictScalars k).comp T.overlapPoint) := by
  let s₁ : S →ₐ[R] S₃ := (p₁₂).comp q₁
  let s₂ : S →ₐ[R] S₃ := (p₁₂).comp q₂
  let s₃ : S →ₐ[R] S₃ := (p₂₃).comp q₂
  have e₁ : (p₁₃).comp q₁ = s₁ := AlgHom.ext (fun _ => rfl)
  have e₂ : (p₂₃).comp q₁ = s₂ := AlgHom.ext (fun _ => rfl)
  have e₃ : (p₁₃).comp q₂ = s₃ := AlgHom.ext (fun _ => rfl)
  have h₁₂ : ((p₁₂).restrictScalars k).comp T.overlapPoint = T.pointDifference s₁ s₂ :=
    T.pointDifference_postcompose p₁₂ q₁ q₂
  have h₁₃ : ((p₁₃).restrictScalars k).comp T.overlapPoint = T.pointDifference s₁ s₃ := by
    change _ = T.pointDifference s₁ s₃
    rw [overlapPoint, T.pointDifference_postcompose, e₁, e₃]
  have h₂₃ : ((p₂₃).restrictScalars k).comp T.overlapPoint = T.pointDifference s₂ s₃ := by
    rw [overlapPoint, T.pointDifference_postcompose, e₂]
  rw [h₁₃, h₁₂, h₂₃, T.pointDifference_trans]

variable [Fintype ι] [DecidableEq ι]

/-- Evaluation of a representation on the universal difference is an effective
matrix descent datum on the affine torsor. -/
def matrixDescentDatum (U : (Matrix ι ι H)ˣ)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j) :
    MatrixDescentDatum R S ι where
  matrix := Units.map T.overlapPoint.toRingHom.mapMatrix.toMonoidHom U
  cocycle := by
    change (U.val.map T.overlapPoint.toRingHom).map (p₁₃).toRingHom =
      (U.val.map T.overlapPoint.toRingHom).map (p₁₂).toRingHom *
        (U.val.map T.overlapPoint.toRingHom).map (p₂₃).toRingHom
    have h (p : S₂ →ₐ[R] S₃) : (U.val.map T.overlapPoint.toRingHom).map p.toRingHom =
        U.val.map (((p.restrictScalars k).comp T.overlapPoint).toRingHom) := rfl
    rw [h, h, h, T.overlapPoint_cocycle]
    exact matrixRepresentation_map_hopfPointMul U.val hU _ _

/-- Over a principal ideal domain, the matrix datum obtained from the torsor has
an invertible matrix of descended coordinates. -/
theorem exists_trivializingRepresentationMatrix [IsDomain R] [IsPrincipalIdealRing R]
    (U : (Matrix ι ι H)ˣ)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j) :
    ∃ g : (Matrix ι ι S)ˣ,
      g.val.map q₁ = U.val.map T.overlapPoint.toRingHom * g.val.map q₂ := by
  letI := T.faithfullyFlat
  exact (T.matrixDescentDatum U hU).exists_trivializingMatrix

local notation "Tg" => S ⊗[k] H
local notation "iS" => (Algebra.TensorProduct.includeLeft : S →ₐ[k] Tg)
local notation "iH" => (Algebra.TensorProduct.includeRight : H →ₐ[k] Tg)

/-- The overlap identity is the equivariance of the frame written in the
coaction coordinates of the torsor. -/
theorem representationFrame_coaction (U : (Matrix ι ι H)ˣ) (g : (Matrix ι ι S)ˣ)
    (hg : g.val.map q₁ = U.val.map T.overlapPoint.toRingHom * g.val.map q₂) :
    g.val.map T.coaction.toRingHom = (U⁻¹).val.map (iH).toRingHom * g.val.map (iS).toRingHom := by
  let e := T.chart.symm.toAlgHom.toRingHom
  have h := congrArg (fun M : Matrix ι ι S₂ => M.map e) hg
  change (g.val.map (q₁).toRingHom).map e =
    (U.val.map T.overlapPoint.toRingHom * g.val.map (q₂).toRingHom).map e at h
  rw [Matrix.map_mul] at h
  have hLeft : (g.val.map (q₁).toRingHom).map e = g.val.map (iS).toRingHom := by
    apply Matrix.ext
    intro i j
    change T.chart.symm (g.val i j ⊗ₜ[R] (1 : S)) = g.val i j ⊗ₜ[k] (1 : H)
    rw [T.chart_symm_apply, map_one, mul_one]
  have hRight : (g.val.map (q₂).toRingHom).map e = g.val.map T.coaction.toRingHom := by
    apply Matrix.ext
    intro i j
    change T.chart.symm ((1 : S) ⊗ₜ[R] g.val i j) = T.coaction (g.val i j)
    rw [T.chart_symm_apply, ← Algebra.TensorProduct.one_def, one_mul]
  have hGroup : (U.val.map T.overlapPoint.toRingHom).map e = U.val.map (iH).toRingHom := by
    apply Matrix.ext
    intro i j
    change T.chart.symm (T.overlapPoint (U.val i j)) = (1 : S) ⊗ₜ[k] U.val i j
    rw [T.overlapPoint_apply, AlgEquiv.symm_apply_apply]
  rw [hLeft, hRight, hGroup] at h
  have hInv : (U⁻¹).val.map (iH).toRingHom * U.val.map (iH).toRingHom = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero (iH).toRingHom) (map_one (iH).toRingHom)]
  rw [h, ← Matrix.mul_assoc, hInv, Matrix.one_mul]

/-- Over a PID the affine torsor has an equivariant frame for each matrix representation. -/
theorem exists_equivariantRepresentationFrame [IsDomain R] [IsPrincipalIdealRing R]
    (U : (Matrix ι ι H)ˣ)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j) :
    ∃ g : (Matrix ι ι S)ˣ,
      g.val.map T.coaction.toRingHom = (U⁻¹).val.map (iH).toRingHom * g.val.map (iS).toRingHom := by
  obtain ⟨g, hg⟩ := T.exists_trivializingRepresentationMatrix U hU
  exact ⟨g, T.representationFrame_coaction U g hg⟩

end AffineHopfTorsor

end TorsorCocycle

end WideE
