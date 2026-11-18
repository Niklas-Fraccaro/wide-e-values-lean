import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RingTheory.Flat.Basic

/-! Finite Galois fields of definition for prescribed affine points. -/

noncomputable section

namespace WideE

section Point

variable {F Ω H : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable [CommRing H] [Algebra F H] [Algebra.FiniteType F H]

/-- An affine point over a Galois extension is defined over a finite Galois
subfield containing any prescribed finite Galois subfield. -/
theorem exists_finiteGalois_field_of_definition (E : FiniteGaloisIntermediateField F Ω)
    (a : H →ₐ[F] Ω) :
    ∃ L : FiniteGaloisIntermediateField F Ω, E ≤ L ∧
      ∃ aL : H →ₐ[F] L, L.toIntermediateField.val.comp aL = a := by
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType F H).out
  let t := a '' (s : Set H)
  letI : Finite t := (s.finite_toSet.image a).to_subtype
  let D := FiniteGaloisIntermediateField.adjoin F t
  let L := E ⊔ D
  have ht : t ⊆ L.toIntermediateField :=
    (FiniteGaloisIntermediateField.subset_adjoin F t).trans
      (show D.toIntermediateField ≤ L.toIntermediateField from le_sup_right)
  have hL : (⊤ : Subalgebra F H) ≤ L.toIntermediateField.toSubalgebra.comap a := by
    rw [← hs, Algebra.adjoin_le_iff]
    intro x hx
    exact ht (Set.mem_image_of_mem a hx)
  let aL := a.codRestrict L.toIntermediateField.toSubalgebra (fun x => hL (show x ∈ (⊤ : Subalgebra F H) by simp))
  exact ⟨L, le_sup_left, aL, AlgHom.ext fun _ => rfl⟩

end Point

section Tensor

open scoped TensorProduct

variable {F Ω H J : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable [CommRing H] [Algebra F H] [CommRing J] [Algebra F J]

/-- Inclusion of scalar tensors over a finite Galois subfield. -/
def finiteGaloisTensorInclusion (J : Type*) [CommRing J] [Algebra F J]
    (E : FiniteGaloisIntermediateField F Ω) : E ⊗[F] J →ₐ[F] Ω ⊗[F] J :=
  Algebra.TensorProduct.map E.toIntermediateField.val (AlgHom.id F J)

omit [IsGalois F Ω] in
/-- Scalar-tensor inclusion along a field embedding is injective. -/
theorem finiteGaloisTensorInclusion_injective (E : FiniteGaloisIntermediateField F Ω) :
    Function.Injective (finiteGaloisTensorInclusion J E) := by
  change Function.Injective (E.toIntermediateField.val.toLinearMap.rTensor J)
  exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

omit [IsGalois F Ω] in
private theorem finiteGaloisTensorInclusion_range_mono
    {E L : FiniteGaloisIntermediateField F Ω} (h : E ≤ L) :
    (finiteGaloisTensorInclusion J E).range ≤ (finiteGaloisTensorInclusion J L).range := by
  rintro _ ⟨x, rfl⟩
  let j := Algebra.TensorProduct.map (IntermediateField.inclusion h) (AlgHom.id F J)
  have hComp : (finiteGaloisTensorInclusion J L).comp j = finiteGaloisTensorInclusion J E := by
    apply Algebra.TensorProduct.ext'
    intro a b
    rfl
  exact ⟨j x, DFunLike.congr_fun hComp x⟩

private theorem exists_in_finiteGaloisTensorRange (x : Ω ⊗[F] J) :
    ∃ L : FiniteGaloisIntermediateField F Ω, x ∈ (finiteGaloisTensorInclusion J L).range := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨⊥, ⟨0, map_zero _⟩⟩
  | tmul a b =>
    let L := FiniteGaloisIntermediateField.adjoin F ({a} : Set Ω)
    have ha : a ∈ L.toIntermediateField := FiniteGaloisIntermediateField.subset_adjoin F _ rfl
    exact ⟨L, ⟨(⟨a, ha⟩ : L) ⊗ₜ[F] b, rfl⟩⟩
  | add a b ha hb =>
    obtain ⟨E, hE⟩ := ha
    obtain ⟨L, hL⟩ := hb
    exact ⟨E ⊔ L, (finiteGaloisTensorInclusion J (E ⊔ L)).range.add_mem
      (finiteGaloisTensorInclusion_range_mono le_sup_left hE)
      (finiteGaloisTensorInclusion_range_mono le_sup_right hL)⟩

/-- Finitely many scalar tensors are defined over a common finite Galois field
containing any given finite Galois subfield. -/
theorem exists_finiteGalois_tensor_family (E : FiniteGaloisIntermediateField F Ω)
    {ι : Type*} (s : Finset ι) (x : ι → Ω ⊗[F] J) :
    ∃ L : FiniteGaloisIntermediateField F Ω, E ≤ L ∧
      ∀ i ∈ s, x i ∈ (finiteGaloisTensorInclusion J L).range := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨E, le_rfl, ?_⟩
    intro i hi
    simp at hi
  | insert i s _ ih =>
    obtain ⟨L, hEL, hL⟩ := ih
    obtain ⟨M, hM⟩ := exists_in_finiteGaloisTensorRange (x i)
    refine ⟨L ⊔ M, hEL.trans le_sup_left, fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact finiteGaloisTensorInclusion_range_mono le_sup_right hM
    · exact finiteGaloisTensorInclusion_range_mono le_sup_left (hL j hjs)

/-- Algebra maps from a finite-type source into a scalar extension have a
finite Galois field of definition. -/
theorem exists_finiteGalois_tensor_algHom_model [Algebra.FiniteType F H]
    (E : FiniteGaloisIntermediateField F Ω) (f : H →ₐ[F] Ω ⊗[F] J) :
    ∃ L : FiniteGaloisIntermediateField F Ω, E ≤ L ∧
      ∃ g : H →ₐ[F] L ⊗[F] J, (finiteGaloisTensorInclusion J L).comp g = f := by
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType F H).out
  obtain ⟨L, hEL, hL⟩ := exists_finiteGalois_tensor_family E s f
  let j := finiteGaloisTensorInclusion J L
  have hTop : (⊤ : Subalgebra F H) ≤ j.range.comap f := by
    rw [← hs, Algebra.adjoin_le_iff]
    exact hL
  let e := AlgEquiv.ofInjective j (finiteGaloisTensorInclusion_injective L)
  let g := e.symm.toAlgHom.comp (f.codRestrict j.range fun x => hTop (show x ∈ (⊤ : Subalgebra F H) by simp))
  refine ⟨L, hEL, g, AlgHom.ext fun x => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ⟨f x, hTop (show x ∈ (⊤ : Subalgebra F H) by simp)⟩)

end Tensor

section TensorEquiv

open scoped TensorProduct

variable {F Ω H J : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable [CommRing H] [Algebra F H] [CommRing J] [Algebra F J]

private def extendTensorMap (L : FiniteGaloisIntermediateField F Ω) (f : H →ₐ[F] L ⊗[F] J) :
    L ⊗[F] H →ₐ[L] L ⊗[F] J :=
  Algebra.TensorProduct.lift (Algebra.ofId L (L ⊗[F] J)) f (fun a x => Algebra.commutes a (f x))

omit [IsGalois F Ω] in
private theorem extendTensorMap_commutes (L : FiniteGaloisIntermediateField F Ω)
    (e : Ω ⊗[F] H →ₐ[Ω] Ω ⊗[F] J) (f : H →ₐ[F] L ⊗[F] J)
    (h : (finiteGaloisTensorInclusion J L).comp f =
      (e.restrictScalars F).comp Algebra.TensorProduct.includeRight) :
    (finiteGaloisTensorInclusion J L).comp ((extendTensorMap L f).restrictScalars F) =
      (e.restrictScalars F).comp (finiteGaloisTensorInclusion H L) := by
  apply Algebra.TensorProduct.ext'
  intro a x
  let t := L.toIntermediateField.val
  have h' : finiteGaloisTensorInclusion J L (f x) = e (1 ⊗ₜ[F] x) := DFunLike.congr_fun h x
  change finiteGaloisTensorInclusion J L (extendTensorMap L f (a ⊗ₜ[F] x)) = e (t a ⊗ₜ[F] x)
  rw [extendTensorMap, Algebra.TensorProduct.lift_tmul, map_mul, h']
  change (t a ⊗ₜ[F] (1 : J)) * e (1 ⊗ₜ[F] x) = e (t a ⊗ₜ[F] x)
  change algebraMap Ω (Ω ⊗[F] J) (t a) * e (1 ⊗ₜ[F] x) = _
  rw [← e.commutes, ← map_mul]
  congr 1
  change (t a ⊗ₜ[F] (1 : H)) * ((1 : Ω) ⊗ₜ[F] x) = t a ⊗ₜ[F] x
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- An algebra isomorphism between the scalar extensions of two finite-type
algebras is defined over a finite Galois subfield containing any prescribed one. -/
theorem exists_finiteGalois_tensor_algEquiv_model [Algebra.FiniteType F H] [Algebra.FiniteType F J]
    (E : FiniteGaloisIntermediateField F Ω) (e : Ω ⊗[F] H ≃ₐ[Ω] Ω ⊗[F] J) :
    ∃ L : FiniteGaloisIntermediateField F Ω, E ≤ L ∧
      ∃ eL : L ⊗[F] H ≃ₐ[L] L ⊗[F] J,
        (finiteGaloisTensorInclusion J L).comp (eL.toAlgHom.restrictScalars F) =
          (e.toAlgHom.restrictScalars F).comp (finiteGaloisTensorInclusion H L) := by
  let g := (e.toAlgHom.restrictScalars F).comp Algebra.TensorProduct.includeRight
  let h := (e.symm.toAlgHom.restrictScalars F).comp Algebra.TensorProduct.includeRight
  obtain ⟨M, hEM, gM, hgM⟩ := exists_finiteGalois_tensor_algHom_model E g
  obtain ⟨L, hML, hL, hhL⟩ := exists_finiteGalois_tensor_algHom_model M h
  let j := Algebra.TensorProduct.map (IntermediateField.inclusion hML) (AlgHom.id F J)
  let gL := j.comp gM
  have hj : (finiteGaloisTensorInclusion J L).comp j = finiteGaloisTensorInclusion J M := by
    apply Algebra.TensorProduct.ext'
    intro a x
    rfl
  have hgL : (finiteGaloisTensorInclusion J L).comp gL = g := by
    change ((finiteGaloisTensorInclusion J L).comp j).comp gM = g
    rw [hj, hgM]
  let f₁ := extendTensorMap L gL
  let f₂ := extendTensorMap L hL
  have h₁ (x : L ⊗[F] H) : finiteGaloisTensorInclusion J L (f₁ x) =
      e (finiteGaloisTensorInclusion H L x) :=
    DFunLike.congr_fun (extendTensorMap_commutes L e.toAlgHom gL hgL) x
  have h₂ (y : L ⊗[F] J) : finiteGaloisTensorInclusion H L (f₂ y) =
      e.symm (finiteGaloisTensorInclusion J L y) :=
    DFunLike.congr_fun (extendTensorMap_commutes L e.symm.toAlgHom hL hhL) y
  have hLeft : f₂.comp f₁ = AlgHom.id L _ := by
    apply AlgHom.ext
    intro x
    apply finiteGaloisTensorInclusion_injective L
    change finiteGaloisTensorInclusion H L (f₂ (f₁ x)) = finiteGaloisTensorInclusion H L x
    rw [h₂, h₁, e.symm_apply_apply]
  have hRight : f₁.comp f₂ = AlgHom.id L _ := by
    apply AlgHom.ext
    intro x
    apply finiteGaloisTensorInclusion_injective L
    change finiteGaloisTensorInclusion J L (f₁ (f₂ x)) = finiteGaloisTensorInclusion J L x
    rw [h₁, h₂, e.apply_symm_apply]
  exact ⟨L, hEM.trans hML, AlgEquiv.ofAlgHom f₁ f₂ hRight hLeft, AlgHom.ext h₁⟩

end TensorEquiv

end WideE
