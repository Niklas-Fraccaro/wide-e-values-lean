import WideE.HopfAntipode
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Passing the Hopf operations to a quotient of a commutative Hopf algebra. -/

noncomputable section

open scoped TensorProduct

namespace WideE

section Surjective

variable {k H Q : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H]
  [CommRing Q] [Algebra k Q]
  (f : H →ₐ[k] Q) (hf : Function.Surjective f)
  (d : Q →ₐ[k] Q ⊗[k] Q) (e : Q →ₐ[k] k) (s : Q →ₗ[k] Q)

local notation "M" => Algebra.TensorProduct.map (S := k)
local notation "Δ" => (Bialgebra.comulAlgHom k H)
local notation "ε" => (Bialgebra.counitAlgHom k H)
local notation "σ" => HopfAlgebra.antipode (R := k) (A := H)

variable (hd : d.comp f = (Algebra.TensorProduct.map f f).comp (Bialgebra.comulAlgHom k H))
  (he : e.comp f = Bialgebra.counitAlgHom k H)
  (hs : ∀ a : H, s (f a) = f (HopfAlgebra.antipode (R := k) a))

include hf hd in
private theorem quotientCoassoc (q : Q) :
    Algebra.TensorProduct.assoc k Q Q Q (M d (AlgHom.id k Q) (d q)) =
      M (AlgHom.id k Q) d (d q) := by
  obtain ⟨a, rfl⟩ := hf q
  rw [show d (f a) = M f f (Δ a) from AlgHom.congr_fun hd a]
  have hL : (M d (AlgHom.id k Q)).comp (M f f) =
      (M (M f f) f).comp (M Δ (AlgHom.id k H)) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp,
      AlgHom.id_comp, AlgHom.comp_id, hd]
  have hR : (M (AlgHom.id k Q) d).comp (M f f) =
      (M f (M f f)).comp (M (AlgHom.id k H) Δ) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp,
      AlgHom.id_comp, AlgHom.comp_id, hd]
  have hAssoc : (Algebra.TensorProduct.assoc k Q Q Q).toAlgHom.comp (M (M f f) f) =
      (M f (M f f)).comp (Algebra.TensorProduct.assoc k H H H).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro z b
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rfl
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  change ((Algebra.TensorProduct.assoc k Q Q Q).toAlgHom.comp
    ((M d (AlgHom.id k Q)).comp (M f f))) (Δ a) =
      ((M (AlgHom.id k Q) d).comp (M f f)) (Δ a)
  rw [hL, hR, ← AlgHom.comp_assoc, hAssoc, AlgHom.comp_assoc]
  exact congrArg (M f (M f f)) (Coalgebra.coassoc_apply (R := k) a)

include hf hd he in
private theorem quotientCounitLeft (q : Q) :
    M e (AlgHom.id k Q) (d q) = (Algebra.TensorProduct.lid k Q).symm q := by
  obtain ⟨a, rfl⟩ := hf q
  rw [show d (f a) = M f f (Δ a) from AlgHom.congr_fun hd a]
  change ((M e (AlgHom.id k Q)).comp (M f f)) (Δ a) = _
  rw [← Algebra.TensorProduct.map_comp, he, AlgHom.id_comp]
  rw [show M ε f = (M (AlgHom.id k k) f).comp (M ε (AlgHom.id k H)) by
    rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp, AlgHom.comp_id]]
  rw [AlgHom.comp_apply, show M ε (AlgHom.id k H) (Δ a) =
    (Algebra.TensorProduct.lid k H).symm a from Coalgebra.rTensor_counit_comul a]
  rfl

include hf hd he in
private theorem quotientCounitRight (q : Q) :
    M (AlgHom.id k Q) e (d q) = (Algebra.TensorProduct.rid k k Q).symm q := by
  obtain ⟨a, rfl⟩ := hf q
  rw [show d (f a) = M f f (Δ a) from AlgHom.congr_fun hd a]
  change ((M (AlgHom.id k Q) e).comp (M f f)) (Δ a) = _
  rw [← Algebra.TensorProduct.map_comp, he, AlgHom.id_comp]
  rw [show M f ε = (M f (AlgHom.id k k)).comp (M (AlgHom.id k H) ε) by
    rw [← Algebra.TensorProduct.map_comp, AlgHom.comp_id, AlgHom.id_comp]]
  rw [AlgHom.comp_apply, show M (AlgHom.id k H) ε (Δ a) =
    (Algebra.TensorProduct.rid k k H).symm a from Coalgebra.lTensor_counit_comul a]
  rfl

include hs in
private theorem quotientAntipodeMul (z : H ⊗[k] H) :
    LinearMap.mul' k Q (s.rTensor Q (M f f z)) =
      f (LinearMap.mul' k H ((σ).rTensor H z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul,
      LinearMap.mul'_apply, hs, map_mul]

include hs in
private theorem quotientMulAntipode (z : H ⊗[k] H) :
    LinearMap.mul' k Q (s.lTensor Q (M f f z)) =
      f (LinearMap.mul' k H ((σ).lTensor H z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul,
      LinearMap.mul'_apply, hs, map_mul]

/-- Compatible operations along a surjective algebra map give a Hopf algebra. -/
def hopfOfSurjective : HopfAlgebra k Q where
  toBialgebra := Bialgebra.ofAlgHom d e (AlgHom.ext (quotientCoassoc f hf d hd))
    (AlgHom.ext (quotientCounitLeft f hf d e hd he))
    (AlgHom.ext (quotientCounitRight f hf d e hd he))
  antipode := s
  mul_antipode_rTensor_comul := by
    apply LinearMap.ext
    intro q
    obtain ⟨a, rfl⟩ := hf q
    change LinearMap.mul' k Q (s.rTensor Q (d (f a))) = algebraMap k Q (e (f a))
    rw [show d (f a) = M f f (Δ a) from AlgHom.congr_fun hd a,
      show e (f a) = ε a from AlgHom.congr_fun he a, quotientAntipodeMul f s hs]
    simpa only [AlgHom.commutes] using congrArg f (HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) a)
  mul_antipode_lTensor_comul := by
    apply LinearMap.ext
    intro q
    obtain ⟨a, rfl⟩ := hf q
    change LinearMap.mul' k Q (s.lTensor Q (d (f a))) = algebraMap k Q (e (f a))
    rw [show d (f a) = M f f (Δ a) from AlgHom.congr_fun hd a,
      show e (f a) = ε a from AlgHom.congr_fun he a, quotientMulAntipode f s hs]
    simpa only [AlgHom.commutes] using congrArg f (HopfAlgebra.mul_antipode_lTensor_comul_apply (R := k) a)

end Surjective

section Ideal

variable {k H : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H]

/-- A Hopf ideal, expressed by the vanishing of the structure maps on the quotient. -/
structure IsHopfIdeal (k : Type*) [CommRing k] [HopfAlgebra k H] (I : Ideal H) : Prop where
  comul : I ≤ RingHom.ker ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I)
    (Ideal.Quotient.mkₐ k I)).comp (Bialgebra.comulAlgHom k H)).toRingHom
  counit : I ≤ RingHom.ker (Bialgebra.counitAlgHom k H).toRingHom
  antipode : I ≤ RingHom.ker ((Ideal.Quotient.mkₐ k I).comp (hopfAntipodeAlgHom k H)).toRingHom

variable (k) in
/-- For an ideal given by generators it suffices to check the structure maps on them. -/
theorem IsHopfIdeal.span_of_generators (s : Set H)
    (hD : ∀ x ∈ s, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (Ideal.span s))
      (Ideal.Quotient.mkₐ k (Ideal.span s)) (Bialgebra.comulAlgHom k H x) = 0)
    (he : ∀ x ∈ s, Bialgebra.counitAlgHom k H x = 0)
    (hS : ∀ x ∈ s, Ideal.Quotient.mkₐ k (Ideal.span s) (HopfAlgebra.antipode (R := k) x) = 0) :
    IsHopfIdeal k (Ideal.span s) where
  comul := Ideal.span_le.mpr hD
  counit := Ideal.span_le.mpr he
  antipode := Ideal.span_le.mpr fun x hx => by
    change Ideal.Quotient.mkₐ k (Ideal.span s) (hopfAntipodeAlgHom k H x) = 0
    rw [hopfAntipodeAlgHom_apply]
    exact hS x hx

namespace IsHopfIdeal

variable {I : Ideal H} (h : IsHopfIdeal k I)

local notation "Q" => H ⧸ I
local notation "π" => (Ideal.Quotient.mkₐ k I)

private def quotientComul : Q →ₐ[k] Q ⊗[k] Q :=
  Ideal.Quotient.liftₐ I ((Algebra.TensorProduct.map π π).comp (Bialgebra.comulAlgHom k H)) h.comul

private def quotientCounit : Q →ₐ[k] k :=
  Ideal.Quotient.liftₐ I (Bialgebra.counitAlgHom k H) h.counit

private def quotientAntipode : Q →ₐ[k] Q :=
  Ideal.Quotient.liftₐ I ((π).comp (hopfAntipodeAlgHom k H)) h.antipode

/-- The Hopf algebra of the closed subgroup defined by an ideal. -/
def quotientHopf : HopfAlgebra k Q :=
  hopfOfSurjective π (Ideal.Quotient.mkₐ_surjective k I)
    h.quotientComul h.quotientCounit h.quotientAntipode.toLinearMap rfl rfl fun a =>
      congrArg π (hopfAntipodeAlgHom_apply a)

/-- The quotient map of a Hopf ideal respects the bialgebra operations. -/
def quotientBialgHom :
    letI := h.quotientHopf
    H →ₐc[k] Q := by
  letI := h.quotientHopf
  exact .ofAlgHom π rfl rfl

@[simp] theorem quotientBialgHom_apply (a : H) : h.quotientBialgHom a = π a := rfl

end IsHopfIdeal

end Ideal

end WideE
