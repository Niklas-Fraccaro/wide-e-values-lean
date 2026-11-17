import WideE.ComponentPullback
import WideE.PVTorsor
import TypedMorphismMaps

/-! Base change of an affine torsor under a group over the constant field. -/

noncomputable section

open scoped TensorProduct
open TensorProduct

namespace WideE

open StrictEUnit

attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 40000

section BaseChange

variable {k B A S H : Type*} [CommRing k] [CommRing B] [CommRing A] [CommRing S] [CommRing H]
  [Algebra k B] [Algebra B A] [Algebra B S] [Algebra k A] [Algebra k S]
  [IsScalarTower k B A] [IsScalarTower k B S]

local notation "P" => A ⊗[B] S

section Coaction

variable [Algebra k H]

/-- Extend the coaction on the left by scalars and regroup its constant factor. -/
def coactionBaseChange (ρ : S →ₐ[B] S ⊗[k] H) : P →ₐ[A] P ⊗[k] H :=
  (fiberMixedAssoc (k:=k) (B:=B) (A:=A)).symm.toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id A A) ρ)

@[simp] theorem coactionBaseChange_tmul (ρ : S →ₐ[B] S ⊗[k] H) (a : A) (s : S) :
    coactionBaseChange ρ (a ⊗ₜ[B] s) =
      (fiberMixedAssoc (k:=k) (B:=B) (A:=A)).symm (a ⊗ₜ[B] ρ s) := rfl

private theorem mixedAssoc_inverse_tmul (a : A) (s : S) (h : H) :
    (fiberMixedAssoc (k:=k) (B:=B) (A:=A)).symm (a ⊗ₜ[B] (s ⊗ₜ[k] h)) =
      (a ⊗ₜ[B] s) ⊗ₜ[k] h := rfl

private theorem mixedAssoc_assoc (a : A) (z : S ⊗[k] H) (h : H) :
    fiberMixedAssoc (k:=k) (B:=B) (A:=A)
      (Algebra.TensorProduct.assoc k P H H
        ((fiberMixedAssoc (k:=k) (B:=B) (A:=A)).symm (a ⊗ₜ[B] z) ⊗ₜ[k] h)) =
      a ⊗ₜ[B] Algebra.TensorProduct.assoc k S H H (z ⊗ₜ[k] h) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, tmul_zero, zero_tmul]
  | add x y hx hy => simp only [tmul_add, add_tmul, TypedMaps.algEquiv_add, hx, hy]
  | tmul s g => rfl

private theorem coactionBaseChange_left (ρ : S →ₐ[B] S ⊗[k] H) (a : A) (z : S ⊗[k] H) :
    fiberMixedAssoc (k:=k) (B:=B) (A:=A)
      (Algebra.TensorProduct.assoc k P H H
        (Algebra.TensorProduct.map ((coactionBaseChange ρ).restrictScalars k) (AlgHom.id k H)
          ((fiberMixedAssoc (k:=k) (B:=B) (A:=A)).symm (a ⊗ₜ[B] z)))) =
      a ⊗ₜ[B] Algebra.TensorProduct.assoc k S H H
        (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, tmul_zero, zero_tmul]
  | add x y hx hy => simp only [tmul_add, TypedMaps.algEquiv_add, TypedMaps.algHom_add, hx, hy]
  | tmul s h =>
    simp only [mixedAssoc_inverse_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, AlgHom.restrictScalars_apply, coactionBaseChange_tmul]
    exact mixedAssoc_assoc a (ρ s) h

private theorem coactionBaseChange_right (Δ : H →ₐ[k] H ⊗[k] H) (a : A) (z : S ⊗[k] H) :
    fiberMixedAssoc (k:=k) (B:=B) (A:=A)
      (Algebra.TensorProduct.map (AlgHom.id P P) Δ
        ((fiberMixedAssoc (k:=k) (B:=B) (A:=A)).symm (a ⊗ₜ[B] z))) =
      a ⊗ₜ[B] Algebra.TensorProduct.map (AlgHom.id S S) Δ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, tmul_zero, zero_tmul]
  | add x y hx hy => simp only [tmul_add, TypedMaps.algEquiv_add, TypedMaps.algHom_add, hx, hy]
  | tmul s h => rfl

theorem coactionBaseChange_coassociative (ρ : S →ₐ[B] S ⊗[k] H) (Δ : H →ₐ[k] H ⊗[k] H)
    (hρ : ∀ s : S, Algebra.TensorProduct.assoc k S H H
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) (ρ s)) =
      Algebra.TensorProduct.map (AlgHom.id S S) Δ (ρ s)) (x : P) :
    Algebra.TensorProduct.assoc k P H H
      (Algebra.TensorProduct.map ((coactionBaseChange ρ).restrictScalars k) (AlgHom.id k H)
        (coactionBaseChange ρ x)) =
      Algebra.TensorProduct.map (AlgHom.id P P) Δ (coactionBaseChange ρ x) := by
  apply (fiberMixedAssoc (k:=k) (B:=B) (A:=A) (R:=S) (H:=H ⊗[k] H)).injective
  induction x using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero]
  | add x y hx hy => simp only [TypedMaps.algEquiv_add, TypedMaps.algHom_add, hx, hy]
  | tmul a s =>
    rw [coactionBaseChange_tmul, coactionBaseChange_left, coactionBaseChange_right, hρ]

private theorem fiberMultiplicationChart_forward (e : S ⊗[k] H ≃ₐ[S] S ⊗[B] S)
    (z : P ⊗[k] H) :
    algebraTensorBaseChangeEquiv (k:=B) A S S (fiberMultiplicationChart (A:=A) e z) =
      Algebra.TensorProduct.map (AlgHom.id A A) (e.toAlgHom.restrictScalars B)
        (fiberMixedAssoc (k:=k) (B:=B) (A:=A) z) :=
  (algebraTensorBaseChangeEquiv (k:=B) A S S).apply_symm_apply _

/-- The coaction from the extended multiplication chart is the scalar extension of the
original chart coaction. -/
theorem inverseMultiplicationCoaction_baseChange (e : S ⊗[k] H ≃ₐ[S] S ⊗[B] S) :
    inverseMultiplicationCoaction (fiberMultiplicationChart (A:=A) e) =
      coactionBaseChange (inverseMultiplicationCoaction e) := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algHom_zero]
  | add x y hx hy => simp only [TypedMaps.algHom_add, hx, hy]
  | tmul a s =>
    apply (fiberMultiplicationChart (A:=A) e).injective
    change (fiberMultiplicationChart (A:=A) e)
      ((fiberMultiplicationChart (A:=A) e).symm ((1 : P) ⊗ₜ[A] (a ⊗ₜ[B] s))) = _
    rw [AlgEquiv.apply_symm_apply]
    apply (algebraTensorBaseChangeEquiv (k:=B) A S S).injective
    rw [fiberMultiplicationChart_forward, coactionBaseChange_tmul, AlgEquiv.apply_symm_apply,
      Algebra.TensorProduct.map_tmul]
    change algebraTensorBaseChangeEquiv (k:=B) A S S
      (((1 : A) ⊗ₜ[B] (1 : S)) ⊗ₜ[A] (a ⊗ₜ[B] s)) =
      a ⊗ₜ[B] e (e.symm ((1 : S) ⊗ₜ[B] s))
    rw [algebraTensorBaseChangeEquiv_tmul, one_mul, AlgEquiv.apply_symm_apply]

end Coaction

section Counit

variable [Bialgebra k H]

private theorem mixedAssoc_counit (a : A) (z : S ⊗[k] H) :
    coactionCounit ((fiberMixedAssoc (k:=k) (B:=B) (A:=A)).symm (a ⊗ₜ[B] z)) =
      a ⊗ₜ[B] coactionCounit z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, tmul_zero]
  | add x y hx hy => simp only [tmul_add, TypedMaps.algEquiv_add, TypedMaps.algHom_add, hx, hy]
  | tmul s h =>
    let e := Bialgebra.counitAlgHom k H h
    change (a ⊗ₜ[B] s) * algebraMap k P e = a ⊗ₜ[B] (s * algebraMap k S e)
    have he : algebraMap k P e = (1 : A) ⊗ₜ[B] algebraMap k S e := by
      rw [IsScalarTower.algebraMap_apply k B P,
        Algebra.TensorProduct.algebraMap_apply' (R:=B) (A:=A) (B:=S),
        ← IsScalarTower.algebraMap_apply k B S]
    rw [he, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem coactionBaseChange_counital (ρ : S →ₐ[B] S ⊗[k] H)
    (hρ : ∀ s : S, coactionCounit (ρ s) = s) (x : P) :
    coactionCounit (coactionBaseChange ρ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algHom_zero]
  | add x y hx hy => simp only [TypedMaps.algHom_add, hx, hy]
  | tmul a s =>
    rw [coactionBaseChange_tmul, mixedAssoc_counit (k:=k) (B:=B) (H:=H), hρ]

end Counit

namespace AffineHopfTorsor

variable [HopfAlgebra k H]

@[simp] theorem inverseMultiplicationCoaction_chart (T : AffineHopfTorsor k B S H) :
    inverseMultiplicationCoaction T.chart = T.coaction := by
  apply AlgHom.ext
  intro s
  rw [inverseMultiplicationCoaction_apply, chart_symm_apply, ← Algebra.TensorProduct.one_def, one_mul]

/-- An arbitrary scalar extension remains a torsor under the same group over the
constant field. -/
def baseChange (T : AffineHopfTorsor k B S H) : AffineHopfTorsor k A P H where
  coaction := coactionBaseChange T.coaction
  coassociative := coactionBaseChange_coassociative T.coaction _ T.coassociative
  counital := coactionBaseChange_counital T.coaction T.counital
  canonical_bijective := by
    rw [← inverseMultiplicationCoaction_chart T, ← inverseMultiplicationCoaction_baseChange]
    exact relativeCandidateCanonical_bijective _
  faithfullyFlat := by
    letI := T.faithfullyFlat
    infer_instance
  group_finiteType := T.group_finiteType

@[simp] theorem baseChange_coaction_tmul (T : AffineHopfTorsor k B S H) (a : A) (s : S) :
    (T.baseChange (A:=A)).coaction (a ⊗ₜ[B] s) =
      (fiberMixedAssoc (k:=k) (B:=B) (A:=A)).symm (a ⊗ₜ[B] T.coaction s) := rfl

/-- The left-torsor-algebra chart of the extended action agrees with the actual
tensor extension of the original multiplication chart. -/
theorem baseChange_chart (T : AffineHopfTorsor k B S H) :
    (T.baseChange (A:=A)).chart = fiberMultiplicationChart (A:=A) T.chart := by
  apply AlgEquiv.symm_bijective.injective
  ext x
  change relativeCandidateCanonical (coactionBaseChange T.coaction) x = _
  rw [← inverseMultiplicationCoaction_chart T, ← inverseMultiplicationCoaction_baseChange,
    relativeCandidateCanonical_eq_inverse]
  rfl

/-- Over the new base, the acting group is obtained from its coordinate algebra
over the constants by scalar extension. -/
theorem baseChange_constantGroupChart (T : AffineHopfTorsor k B S H) :
    (Algebra.TensorProduct.cancelBaseChange k A P P H).trans (T.baseChange (A:=A)).chart =
      componentTorsorChart (A:=A) T.chart := by
  rw [baseChange_chart]
  rfl

end AffineHopfTorsor

end BaseChange

section Kummer

variable {K Q S H : Type*} [CommRing K] [CommRing Q] [CommRing S] [CommRing H]
  [Algebra K Q] [Algebra K S] [Algebra Q S] [IsScalarTower K Q S] [HopfAlgebra K H]
  [Algebra (LaurentPolynomial K) Q] [IsScalarTower K (LaurentPolynomial K) Q]
  {q : ℕ}

/-- The torsor carried by the inverse image of the chosen Kummer component. -/
def AffineHopfTorsor.kummerComponent (T : AffineHopfTorsor K Q S H)
    (j : Q →ₐ[LaurentPolynomial K] KummerExtension K q) :
    letI := j.toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom (j.restrictScalars K)
    AffineHopfTorsor K (KummerExtension K q) (KummerComponentPullback j S) H := by
  letI := j.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom (j.restrictScalars K)
  exact T.baseChange (A:=KummerExtension K q)

end Kummer

end WideE
