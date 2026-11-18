import WideE.HopfPointGroup
import WideE.HopfRestriction
import Mathlib.RingTheory.Bialgebra.Hom

/-! The inherited Hopf algebra on a stable subalgebra over a field. -/

noncomputable section

open scoped TensorProduct

namespace WideE

section Antipode

variable {k H : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H]

local notation "S" => hopfAntipodeAlgHom k H
local notation "Δ" => Bialgebra.comulAlgHom k H

/-- In a commutative Hopf algebra, the antipode is an involution. -/
theorem hopfAntipodeAlgHom_comp_self : (S).comp S = AlgHom.id k H := by
  letI := hopfPointGroup (k := k) (H := H) (A := H)
  exact inv_inv (AlgHom.id k H)

/-- The antipode preserves comultiplication with the two factors reversed. -/
theorem hopfComulAlgHom_comp_antipode :
    (Δ).comp S = (Algebra.TensorProduct.comm k H H).toAlgHom.comp
      ((Algebra.TensorProduct.map S S).comp Δ) := by
  let A := H ⊗[k] H
  letI := hopfPointGroup (k := k) (H := H) (A := A)
  let l : H →ₐ[k] A := Algebra.TensorProduct.includeLeft
  let r : H →ₐ[k] A := Algebra.TensorProduct.includeRight
  have hL : tensorPoint l r = AlgHom.id k A := by
    apply Algebra.TensorProduct.ext'
    intro x y
    rw [tensorPoint_tmul]
    change (x ⊗ₜ[k] (1 : H)) * ((1 : H) ⊗ₜ[k] y) = x ⊗ₜ[k] y
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hD : l * r = Δ := by
    change (tensorPoint l r).comp Δ = Δ
    rw [hL, AlgHom.id_comp]
  have hR : tensorPoint (r.comp S) (l.comp S) = (Algebra.TensorProduct.comm k H H).toAlgHom.comp
      (Algebra.TensorProduct.map S S) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp only [tensorPoint_tmul, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul]
    change ((1 : H) ⊗ₜ[k] S x) * (S y ⊗ₜ[k] (1 : H)) =
      Algebra.TensorProduct.comm k H H (S x ⊗ₜ[k] S y)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Algebra.TensorProduct.comm_tmul]
  calc
    (Δ).comp S = (l * r)⁻¹ := by rw [hD]; rfl
    _ = r⁻¹ * l⁻¹ := mul_inv_rev l r
    _ = _ := by
      change (tensorPoint (r.comp S) (l.comp S)).comp Δ = _
      rw [hR, AlgHom.comp_assoc]

end Antipode

section Subalgebra

variable {k H : Type*} [Field k] [CommRing H] [HopfAlgebra k H]

/-- Closure conditions for a Hopf subalgebra inside a commutative Hopf algebra. -/
structure IsHopfSubalgebra (Q : Subalgebra k H) : Prop where
  comul : ∀ x : Q, Bialgebra.comulAlgHom k H x.val ∈ (Algebra.TensorProduct.map Q.val Q.val).range
  antipode : ∀ x : Q, hopfAntipodeAlgHom k H x.val ∈ Q

namespace IsHopfSubalgebra

variable {Q : Subalgebra k H} (h : IsHopfSubalgebra Q)

private def tensorInclusionEquiv :
    (Q ⊗[k] Q) ≃ₐ[k] (Algebra.TensorProduct.map Q.val Q.val).range :=
  AlgEquiv.ofInjective _ (tensorAlgHom_injective Q.val Q.val Subtype.val_injective Subtype.val_injective)

private def restrictComul : Q →ₐ[k] Q ⊗[k] Q :=
  (tensorInclusionEquiv (Q := Q)).symm.toAlgHom.comp
    (((Bialgebra.comulAlgHom k H).comp Q.val).codRestrict _ h.comul)

private theorem map_restrictComul (x : Q) :
    Algebra.TensorProduct.map Q.val Q.val (h.restrictComul x) = Bialgebra.comulAlgHom k H x.val :=
  congrArg Subtype.val ((tensorInclusionEquiv (Q := Q)).apply_symm_apply ⟨_, h.comul x⟩)

private def restrictAntipode : Q →ₐ[k] Q :=
  ((hopfAntipodeAlgHom k H).comp Q.val).codRestrict Q h.antipode

/-- The Hopf structure induced by the inclusion of a stable subalgebra. -/
def hopfAlgebra : HopfAlgebra k Q :=
  hopfOfInjective Q.val Subtype.val_injective h.restrictComul
    h.restrictAntipode.toLinearMap h.map_restrictComul (fun x => hopfAntipodeAlgHom_apply x.val)

/-- The actual coordinate inclusion of a Hopf subalgebra. -/
def bialgHom :
    letI := h.hopfAlgebra
    Q →ₐc[k] H := by
  letI := h.hopfAlgebra
  exact BialgHom.ofAlgHom Q.val rfl (LinearMap.ext h.map_restrictComul)

@[simp] theorem bialgHom_apply (x : Q) : h.bialgHom x = x.val := rfl

@[simp] theorem counit_apply (x : Q) :
    letI := h.hopfAlgebra
    Bialgebra.counitAlgHom k Q x = Bialgebra.counitAlgHom k H x.val := rfl

@[simp] theorem antipode_apply (x : Q) :
    letI := h.hopfAlgebra
    (hopfAntipodeAlgHom k Q x).val = hopfAntipodeAlgHom k H x.val := by
  letI := h.hopfAlgebra
  rw [hopfAntipodeAlgHom_apply]
  rfl

end IsHopfSubalgebra

end Subalgebra

end WideE
