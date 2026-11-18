import WideE.HopfPointGroup
import WideE.HopfQuotient

/-! The Hopf quotient representing the stabilizer of a rational vector. -/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 70000

section Equations

variable {k H A ι : Type*} [CommRing k] [CommRing H] [Algebra k H]
variable [CommRing A] [Algebra k A] [Fintype ι]

/-- The coordinates of the equation that a matrix fixes a specified vector. -/
def vectorStabilizerEquation (U : Matrix ι ι H) (y : ι → k) (i : ι) : H :=
  (U *ᵥ (algebraMap k H ∘ y)) i - algebraMap k H (y i)

/-- The ideal defining the stabilizer of a rational vector. -/
def vectorStabilizerIdeal (U : Matrix ι ι H) (y : ι → k) : Ideal H :=
  Ideal.span (Set.range (vectorStabilizerEquation U y))

private theorem map_vectorStabilizerEquation (U : Matrix ι ι H) (y : ι → k)
    (p : H →ₐ[k] A) (i : ι) :
    p (vectorStabilizerEquation U y i) =
      (U.map p *ᵥ (algebraMap k A ∘ y)) i - algebraMap k A (y i) := by
  have hScalar : (p.toRingHom : H → A) ∘ (algebraMap k H ∘ y) = algebraMap k A ∘ y :=
    funext fun j => p.commutes (y j)
  rw [vectorStabilizerEquation, map_sub]
  rw [show p ((U *ᵥ (algebraMap k H ∘ y)) i) =
    (U.map p *ᵥ ((p.toRingHom : H → A) ∘ (algebraMap k H ∘ y))) i
      from RingHom.map_mulVec p.toRingHom U (algebraMap k H ∘ y) i]
  rw [hScalar, p.commutes]

/-- Points of the stabilizer quotient are precisely the points fixing the vector. -/
def vectorStabilizerPointEquiv (U : Matrix ι ι H) (y : ι → k) :
    ((H ⧸ vectorStabilizerIdeal U y) →ₐ[k] A) ≃
      {p : H →ₐ[k] A // U.map p *ᵥ (algebraMap k A ∘ y) = algebraMap k A ∘ y} where
  toFun p := ⟨p.comp (Ideal.Quotient.mkₐ k (vectorStabilizerIdeal U y)), by
    funext i
    let π := Ideal.Quotient.mkₐ k (vectorStabilizerIdeal U y)
    have h : π (vectorStabilizerEquation U y i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
    have heq : (p.comp π) (vectorStabilizerEquation U y i) = 0 :=
      (congrArg p h).trans (map_zero p)
    exact sub_eq_zero.mp ((map_vectorStabilizerEquation U y (p.comp π) i).symm.trans heq)⟩
  invFun p := Ideal.Quotient.liftₐ (vectorStabilizerIdeal U y) p.val (by
    change vectorStabilizerIdeal U y ≤ RingHom.ker p.val.toRingHom
    rw [vectorStabilizerIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change p.val (vectorStabilizerEquation U y i) = 0
    rw [map_vectorStabilizerEquation]
    exact sub_eq_zero.mpr (congrFun p.property i))
  left_inv p := by
    apply Ideal.Quotient.algHom_ext
    rfl
  right_inv p := Subtype.ext rfl

end Equations

section HopfIdeal

variable {k H ι : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H]
variable [Fintype ι] [DecidableEq ι]
variable (U : (Matrix ι ι H)ˣ)
  (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
  (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)

include hD he in
/-- The actual equations cutting out a vector stabilizer form a Hopf ideal. -/
theorem vectorStabilizerIdeal_isHopf (y : ι → k) :
    IsHopfIdeal k (vectorStabilizerIdeal U.val y) := by
  classical
  let I := vectorStabilizerIdeal U.val y
  let Q := H ⧸ I
  let π : H →ₐ[k] Q := Ideal.Quotient.mkₐ k I
  refine IsHopfIdeal.span_of_generators k _ ?_ ?_ ?_
  · rintro _ ⟨i, rfl⟩
    let B := Q ⊗[k] Q
    let l : Q →ₐ[k] B := Algebra.TensorProduct.includeLeft
    let r : Q →ₐ[k] B := Algebra.TensorProduct.includeRight
    letI : Group (H →ₐ[k] B) := hopfPointGroup
    let M : (H →ₐ[k] B) →* (Matrix ι ι B)ˣ := hopfPointMatrix U hD he
    let v : ι → B := algebraMap k B ∘ y
    have hL : (M (l.comp π)).val *ᵥ v = v :=
      ((vectorStabilizerPointEquiv U.val y) l).property
    have hR : (M (r.comp π)).val *ᵥ v = v :=
      ((vectorStabilizerPointEquiv U.val y) r).property
    have hFix : (M ((l.comp π) * (r.comp π))).val *ᵥ v = v := by
      rw [map_mul M, Units.val_mul, ← Matrix.mulVec_mulVec, hR, hL]
    have hTensor : tensorPoint (l.comp π) (r.comp π) = Algebra.TensorProduct.map π π := by
      apply Algebra.TensorProduct.ext'
      intro a b
      change (π a ⊗ₜ[k] (1 : Q)) * ((1 : Q) ⊗ₜ[k] π b) = π a ⊗ₜ[k] π b
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    change Algebra.TensorProduct.map π π
      (Bialgebra.comulAlgHom k H (vectorStabilizerEquation U.val y i)) = 0
    rw [← hTensor]
    change (hopfPointMul (l.comp π) (r.comp π)) (vectorStabilizerEquation U.val y i) = 0
    rw [map_vectorStabilizerEquation]
    exact sub_eq_zero.mpr (congrFun hFix i)
  · rintro _ ⟨i, rfl⟩
    letI : Group (H →ₐ[k] k) := hopfPointGroup
    let M : (H →ₐ[k] k) →* (Matrix ι ι k)ˣ := hopfPointMatrix U hD he
    change (1 : H →ₐ[k] k) (vectorStabilizerEquation U.val y i) = 0
    rw [map_vectorStabilizerEquation]
    change ((M 1).val *ᵥ (algebraMap k k ∘ y)) i - algebraMap k k (y i) = 0
    rw [map_one M, Units.val_one, Matrix.one_mulVec]
    exact sub_self _
  · rintro _ ⟨i, rfl⟩
    letI : Group (H →ₐ[k] Q) := hopfPointGroup
    let M : (H →ₐ[k] Q) →* (Matrix ι ι Q)ˣ := hopfPointMatrix U hD he
    let v : ι → Q := algebraMap k Q ∘ y
    have hFix : (M π).val *ᵥ v = v :=
      ((vectorStabilizerPointEquiv U.val y) (AlgHom.id k Q)).property
    have hInv : (M π⁻¹).val *ᵥ v = v := by
      calc
        (M π⁻¹).val *ᵥ v = (M π⁻¹).val *ᵥ ((M π).val *ᵥ v) := congrArg _ hFix.symm
        _ = v := by
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul M, inv_mul_cancel,
            map_one M, Units.val_one, Matrix.one_mulVec]
    change π (HopfAlgebra.antipode (R := k) (vectorStabilizerEquation U.val y i)) = 0
    rw [← hopfAntipodeAlgHom_apply]
    change π⁻¹ (vectorStabilizerEquation U.val y i) = 0
    rw [map_vectorStabilizerEquation]
    exact sub_eq_zero.mpr (congrFun hInv i)

end HopfIdeal

end WideE
