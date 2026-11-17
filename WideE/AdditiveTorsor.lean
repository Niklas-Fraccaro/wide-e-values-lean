import WideE.AdditivePolynomialHopf
import WideE.PrimitiveTorsor

/-! Triviality of affine torsors under the constant additive group. -/

open scoped TensorProduct

noncomputable section

namespace WideE

attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule

variable {k B S : Type*} [Field k] [CommRing B] [CommRing S]
  [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S]

local instance : HopfAlgebra k (Polynomial k) := additivePolynomialHopf k

/-- A torsor under the additive group over an affine base has a polynomial coordinate. -/
theorem affineAdditiveTorsor_polynomial (T : AffineHopfTorsor k B S (Polynomial k)) :
    Nonempty (Polynomial B ≃ₐ[B] S) := by
  obtain ⟨s, hs⟩ := exists_primitive_torsor_coordinate T Polynomial.X (additivePolynomialHopf_comul_X k)
  let f : Polynomial B →ₐ[B] S := Polynomial.aeval s
  let e₀ := polyEquivTensor' B S
  let e₁ := polyEquivTensor' k S
  let e₂ := Polynomial.algEquivAevalXAddC s
  let f' : S ⊗[B] Polynomial B →ₐ[S] S ⊗[B] S :=
    Algebra.TensorProduct.map (AlgHom.id S S) f
  let g := (T.chart.symm.toAlgHom.comp f').comp e₀.toAlgHom
  have hg : g = e₁.toAlgHom.comp e₂.toAlgHom := by
    apply Polynomial.algHom_ext
    change T.chart.symm (f' (e₀ Polynomial.X)) = e₁ (e₂ Polynomial.X)
    have h₀ : e₀ Polynomial.X = (1 : S) ⊗ₜ[B] (Polynomial.X : Polynomial B) := by
      simp [e₀]
    have h₁ : e₁ Polynomial.X = (1 : S) ⊗ₜ[k] (Polynomial.X : Polynomial k) := by
      simp [e₁]
    have h₂ : e₂ Polynomial.X = Polynomial.X + Polynomial.C s := by
      simp [e₂, Polynomial.algEquivAevalXAddC]
    have hC : e₁ (Polynomial.C s) = s ⊗ₜ[k] (1 : Polynomial k) := e₁.commutes s
    rw [h₀, h₂, map_add, h₁, hC, add_comm]
    change T.chart.symm ((1 : S) ⊗ₜ[B] f Polynomial.X) = _
    rw [show f Polynomial.X = s from Polynomial.aeval_X s, T.chart_symm_apply,
      ← Algebra.TensorProduct.one_def, one_mul, hs]
  have hgBijective : Function.Bijective g := by
    rw [hg]
    exact e₁.bijective.comp e₂.bijective
  have hBase : Function.Bijective (f.toLinearMap.lTensor S) := by
    change Function.Bijective f'
    constructor
    · intro x y hxy
      obtain ⟨x', rfl⟩ := e₀.surjective x
      obtain ⟨y', rfl⟩ := e₀.surjective y
      have h : g x' = g y' := congrArg T.chart.symm hxy
      exact congrArg e₀ (hgBijective.1 h)
    · intro y
      obtain ⟨x, hx⟩ := hgBijective.2 (T.chart.symm y)
      exact ⟨e₀ x, T.chart.symm.injective hx⟩
  letI := T.faithfullyFlat
  exact ⟨AlgEquiv.ofBijective f
    ⟨(Module.FaithfullyFlat.lTensor_injective_iff_injective B S f.toLinearMap).mp hBase.1,
      (Module.FaithfullyFlat.lTensor_surjective_iff_surjective B S f.toLinearMap).mp hBase.2⟩⟩

/-- An affine torsor under the constant additive group has a section. -/
theorem affineAdditiveTorsor_has_section (T : AffineHopfTorsor k B S (Polynomial k)) :
    Nonempty (S →ₐ[B] B) := by
  obtain ⟨e⟩ := affineAdditiveTorsor_polynomial T
  exact ⟨(Polynomial.aeval (0 : B)).comp e.symm.toAlgHom⟩

end WideE
