import WideE.GaloisTorsor
import Mathlib.RingTheory.Bialgebra.Hom

/-! Descent of coaction identities and an affine torsor chart from point differences. -/

open scoped TensorProduct

noncomputable section

namespace WideE

open StrictEUnit

set_option maxHeartbeats 1000000

section CoactionIdentities

variable {k R S Q H K : Type*} [CommRing k] [CommRing R] [CommRing S]
  [CommRing Q] [CommRing H] [CommRing K]
  [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
  [Algebra R Q] [Algebra k Q] [IsScalarTower k R Q]
  [HopfAlgebra k H] [HopfAlgebra k K]

local notation "M" => Algebra.TensorProduct.map

/-- The coaction identities descend along a surjective equivariant map
and a morphism of the acting Hopf algebras. -/
theorem quotient_coactionIdentities
    (T : AffineHopfTorsor k R S H) (π : S →ₐ[R] Q) (hπ : Function.Surjective π)
    (b : H →ₐc[k] K) (ρ : Q →ₐ[R] Q ⊗[k] K)
    (hρ : ρ.comp π = (M π (b : H →ₐ[k] K)).comp T.coaction) :
    (∀ q : Q, Algebra.TensorProduct.assoc k Q K K
      (M (ρ.restrictScalars k) (AlgHom.id k K) (ρ q)) =
      M (AlgHom.id Q Q) (Bialgebra.comulAlgHom k K) (ρ q)) ∧
    ∀ q : Q, coactionCounit (ρ q) = q := by
  let p := π.restrictScalars k
  let a : H →ₐ[k] K := b
  let t := T.coaction.restrictScalars k
  let r := ρ.restrictScalars k
  let F := M p a
  have hBase : r.comp p = F.comp t := AlgHom.ext fun x => DFunLike.congr_fun hρ x
  have hΔ : (Bialgebra.comulAlgHom k K).comp a =
      (M a a).comp (Bialgebra.comulAlgHom k H) :=
    (BialgHomClass.map_comp_comulAlgHom b).symm
  have hAssoc : (Algebra.TensorProduct.assoc k Q K K).toAlgHom.comp (M F a) =
      (M p (M a a)).comp (Algebra.TensorProduct.assoc k S H H).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro z c
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | tmul x h => rfl
  have hL : (M r (AlgHom.id k K)).comp F = (M F a).comp (M t (AlgHom.id k H)) := by
    change (M r (AlgHom.id k K)).comp (M p a) = (M F a).comp (M t (AlgHom.id k H))
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp,
      AlgHom.comp_id, AlgHom.id_comp, hBase]
  have hR : (M (AlgHom.id k Q) (Bialgebra.comulAlgHom k K)).comp F =
      (M p (M a a)).comp (M (AlgHom.id k S) (Bialgebra.comulAlgHom k H)) := by
    change (M (AlgHom.id k Q) (Bialgebra.comulAlgHom k K)).comp (M p a) = _
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp,
      AlgHom.id_comp, AlgHom.comp_id, hΔ]
  constructor
  · intro q
    obtain ⟨x, rfl⟩ := hπ q
    change Algebra.TensorProduct.assoc k Q K K (M r (AlgHom.id k K) (r (p x))) =
      M (AlgHom.id k Q) (Bialgebra.comulAlgHom k K) (r (p x))
    rw [show r (p x) = F (t x) from DFunLike.congr_fun hBase x]
    change ((Algebra.TensorProduct.assoc k Q K K).toAlgHom.comp
      ((M r (AlgHom.id k K)).comp F)) (t x) =
        ((M (AlgHom.id k Q) (Bialgebra.comulAlgHom k K)).comp F) (t x)
    rw [hL, hR, ← AlgHom.comp_assoc, hAssoc, AlgHom.comp_assoc]
    exact congrArg (M p (M a a)) (T.coassociative x)
  · intro q
    obtain ⟨x, rfl⟩ := hπ q
    have hε : (coactionCounit (k := k) (S := Q) (H := K)).comp F =
        p.comp (coactionCounit (k := k) (S := S) (H := H)) := by
      apply Algebra.TensorProduct.ext'
      intro s h
      change p s * algebraMap k Q (Bialgebra.counitAlgHom k K (a h)) =
        p (s * algebraMap k S (Bialgebra.counitAlgHom k H h))
      rw [map_mul, p.commutes,
        show Bialgebra.counitAlgHom k K (a h) = Bialgebra.counitAlgHom k H h
          from DFunLike.congr_fun (BialgHomClass.counitAlgHom_comp b) h]
    change coactionCounit (r (p x)) = p x
    rw [show r (p x) = F (t x) from DFunLike.congr_fun hBase x]
    change ((coactionCounit (k := k) (S := Q) (H := K)).comp F) (t x) = p x
    rw [hε, AlgHom.comp_apply]
    exact congrArg p (T.counital x)

end CoactionIdentities

section Canonical

variable {k R Q H : Type*} [CommRing k] [CommRing R] [CommRing Q] [CommRing H]
  [Algebra k R] [Algebra R Q] [Algebra k Q] [Algebra k H] [IsScalarTower k R Q]

local notation "D" => (Q ⊗[R] Q)
local notation "E" => (Q ⊗[k] H)
local notation "pL" => (IsScalarTower.toAlgHom R Q D)
local notation "pR" => (Algebra.TensorProduct.includeRight : Q →ₐ[R] D)
local notation "qL" => (IsScalarTower.toAlgHom R Q E)
local notation "qR" => (Algebra.TensorProduct.includeRight : H →ₐ[k] E)

/-- A difference point at the universal pair constructs an inverse of the
canonical map. Uniqueness at the group chart identifies the second composite. -/
theorem canonical_bijective_of_pointDifference (ρ : Q →ₐ[R] E)
    (hDiff : ∃ d : H →ₐ[k] D, (tensorPoint (pL) d).comp ρ = pR)
    (hUnique : Function.Injective (fun d : H →ₐ[k] E => (tensorPoint (qL) d).comp ρ)) :
    Function.Bijective (relativeCandidateCanonical ρ) := by
  obtain ⟨d, hd⟩ := hDiff
  let ψ := tensorPoint (pL) d
  let φ := relativeCandidateCanonical ρ
  have hLeft : φ.comp (pL) = qL := by
    apply AlgHom.ext
    intro q
    change relativeCandidateCanonical ρ (q ⊗ₜ[R] (1 : Q)) = q ⊗ₜ[k] (1 : H)
    rw [relativeCandidateCanonical_tmul, map_one, mul_one]
  have hRight : φ.comp (pR) = ρ := by
    apply AlgHom.ext
    intro q
    change relativeCandidateCanonical ρ ((1 : Q) ⊗ₜ[R] q) = ρ q
    rw [relativeCandidateCanonical_tmul, ← Algebra.TensorProduct.one_def, one_mul]
  have hOne : ψ.comp φ = AlgHom.id R D := by
    apply Algebra.TensorProduct.ext'
    intro q z
    change ψ (relativeCandidateCanonical ρ (q ⊗ₜ[R] z)) = q ⊗ₜ[R] z
    rw [relativeCandidateCanonical_tmul, map_mul]
    change tensorPoint (pL) d (q ⊗ₜ[k] (1 : H)) * ψ (ρ z) = _
    rw [tensorPoint_tmul, map_one, mul_one,
      show ψ (ρ z) = (1 : Q) ⊗ₜ[R] z from DFunLike.congr_fun hd z]
    change (q ⊗ₜ[R] (1 : Q)) * ((1 : Q) ⊗ₜ[R] z) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let d' := (φ.restrictScalars k).comp d
  have hMap : φ.comp ψ = tensorPoint (qL) d' := by
    apply Algebra.TensorProduct.ext'
    intro q h
    change φ (tensorPoint (pL) d (q ⊗ₜ[k] h)) = tensorPoint (qL) d' (q ⊗ₜ[k] h)
    rw [tensorPoint_tmul, tensorPoint_tmul, map_mul,
      show φ ((pL) q) = (qL) q from DFunLike.congr_fun hLeft q]
    rfl
  have hId : tensorPoint (qL) (qR) = AlgHom.id R E := by
    apply Algebra.TensorProduct.ext'
    intro q h
    change tensorPoint (qL) (qR) (q ⊗ₜ[k] h) = q ⊗ₜ[k] h
    rw [tensorPoint_tmul]
    change (q ⊗ₜ[k] (1 : H)) * ((1 : Q) ⊗ₜ[k] h) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hMove : (tensorPoint (qL) d').comp ρ = (tensorPoint (qL) (qR)).comp ρ := by
    rw [← hMap, AlgHom.comp_assoc, show ψ.comp ρ = pR from hd, hRight, hId, AlgHom.id_comp]
  have hTwo : φ.comp ψ = AlgHom.id R E := by rw [hMap, hUnique hMove, hId]
  exact ⟨Function.LeftInverse.injective (fun x => DFunLike.congr_fun hOne x),
    Function.RightInverse.surjective (fun x => DFunLike.congr_fun hTwo x)⟩

end Canonical

end WideE
