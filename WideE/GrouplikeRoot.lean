import WideE.HopfSmoothLocus
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Tensor products of affine domains and roots of group-like coordinates. -/

noncomputable section

open scoped TensorProduct
open TensorProduct

namespace WideE

universe u

section TensorDomain

variable {k A B : Type u} [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A]
  [Algebra k A] [Algebra.FiniteType k A] [CommRing B] [IsDomain B] [Algebra k B]

private theorem exists_rationalPoint_apply_ne_zero {a : A} (ha : a ≠ 0) :
    ∃ p : A →ₐ[k] k, p a ≠ 0 := by
  letI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  let x : PrimeSpectrum A := ⟨⊥, Ideal.bot_prime⟩
  have hx : x ∈ PrimeSpectrum.basicOpen a := by
    exact (PrimeSpectrum.mem_basicOpen a x).mpr (fun hb => ha (Ideal.mem_bot.mp hb))
  obtain ⟨y, hy, hyClosed⟩ := PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing
    (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) PrimeSpectrum.isOpen_basicOpen ⟨x, hx⟩
  letI : y.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hyClosed
  let p := StrictEUnit.maximalIdealPoint (k := k) y.asIdeal
  refine ⟨p, fun h => (PrimeSpectrum.mem_basicOpen a y).mp hy ?_⟩
  rw [← StrictEUnit.maximalIdealPoint_ker (k := k) y.asIdeal]
  exact h

/-- A finite-type domain over an algebraically closed field remains a domain
after tensoring with any domain over that field. -/
theorem tensor_isDomain_of_algClosed : IsDomain (A ⊗[k] B) := by
  classical
  let b := Basis.ofVectorSpace k B
  let e := TensorProduct.equivFinsuppOfBasisRight (M := A) b
  let ev (p : A →ₐ[k] k) : A ⊗[k] B →ₐ[k] B :=
    (Algebra.TensorProduct.lid k B).toAlgHom.comp (Algebra.TensorProduct.map p (AlgHom.id k B))
  have heval (p : A →ₐ[k] k) (z : A ⊗[k] B) (i : Basis.ofVectorSpaceIndex k B) :
      b.repr (ev p z) i = p (e z i) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, Finsupp.zero_apply]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
    | tmul a z =>
      simp only [ev, AlgHom.comp_apply, AlgEquiv.coe_algHom, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.lid_tmul, AlgHom.id_apply, map_smul, Finsupp.smul_apply, e,
        TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, smul_eq_mul, mul_comm]
  have hEntry (z : A ⊗[k] B) (hz : z ≠ 0) : ∃ i, e z i ≠ 0 := by
    by_contra! h
    apply hz
    apply e.injective
    ext i
    rw [map_zero, Finsupp.zero_apply, h i]
  obtain ⟨p, _⟩ := exists_rationalPoint_apply_ne_zero (k := k) (one_ne_zero : (1 : A) ≠ 0)
  letI : Nontrivial (A ⊗[k] B) := (ev p).toRingHom.domain_nontrivial
  letI : NoZeroDivisors (A ⊗[k] B) := ⟨by
    intro z w hzw
    by_contra! h
    obtain ⟨i, hi⟩ := hEntry z h.1
    obtain ⟨j, hj⟩ := hEntry w h.2
    obtain ⟨r, hr⟩ := exists_rationalPoint_apply_ne_zero (k := k) (mul_ne_zero hi hj)
    have hr' : r (e z i) * r (e w j) ≠ 0 := by simpa only [map_mul] using hr
    have hnonzero (v : A ⊗[k] B) (l : Basis.ofVectorSpaceIndex k B) (hl : r (e v l) ≠ 0) :
        ev r v ≠ 0 := by
      intro hzero
      apply hl
      rw [← heval, hzero, map_zero, Finsupp.zero_apply]
    have hz : ev r z ≠ 0 := hnonzero z i (fun h0 => hr' (by rw [h0, zero_mul]))
    have hw : ev r w ≠ 0 := hnonzero w j (fun h0 => hr' (by rw [h0, mul_zero]))
    apply mul_ne_zero hz hw
    rw [← map_mul, hzw, map_zero]⟩
  exact NoZeroDivisors.to_isDomain _

end TensorDomain

section Roots

variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [IsDomain H]
  [HopfAlgebra k H] [Algebra.FiniteType k H]

private theorem scalar_of_isIntegral {D : Type u} [CommRing D] [IsDomain D] [Algebra k D]
    {c : D} (hc : IsIntegral k c) : ∃ a : k, algebraMap k D a = c := by
  let B := Algebra.adjoin k ({c} : Set D)
  letI : Module.Finite k B := Algebra.finite_adjoin_simple_of_isIntegral hc
  letI : Algebra.IsIntegral k B := Algebra.IsIntegral.of_finite k B
  obtain ⟨a, ha⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := B)).surjective
    (⟨c, Algebra.subset_adjoin (Set.mem_singleton c)⟩ : B)
  exact ⟨a, congrArg (Subtype.val : B → D) ha⟩

/-- A unit whose positive power is group-like is itself group-like after its
counit has been normalized to one. -/
theorem grouplike_of_power_grouplike (u : Hˣ) (hε : Coalgebra.counit (R := k) (u : H) = 1)
    {d : ℕ} (hd : 0 < d)
    (hΔ : Coalgebra.comul (R := k) ((u : H) ^ d) = ((u : H) ^ d) ⊗ₜ[k] ((u : H) ^ d)) :
    Coalgebra.comul (R := k) (u : H) = (u : H) ⊗ₜ[k] (u : H) := by
  let T := H ⊗[k] H
  let Δ := Bialgebra.comulAlgHom k H
  let ε := Bialgebra.counitAlgHom k H
  let v : T := (↑u⁻¹ : H) ⊗ₜ[k] (↑u⁻¹ : H)
  let z : T := Δ (u : H) * v
  have hInv : ((u : H) ⊗ₜ[k] (u : H)) * v = 1 := by
    have hu : (u : H) * (↑u⁻¹ : H) = 1 := u.mul_inv
    change ((u : H) ⊗ₜ[k] (u : H)) * ((↑u⁻¹ : H) ⊗ₜ[k] (↑u⁻¹ : H)) = 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, hu, ← Algebra.TensorProduct.one_def]
  have hzpow : z ^ d = 1 := by
    change (Δ (u : H) * v) ^ d = 1
    rw [mul_pow, ← map_pow]
    change Coalgebra.comul (R := k) ((u : H) ^ d) * v ^ d = 1
    rw [hΔ, ← Algebra.TensorProduct.tmul_pow, ← mul_pow, hInv, one_pow]
  letI : IsDomain T := tensor_isDomain_of_algClosed (k := k) (A := H) (B := H)
  have hzi : IsIntegral k z := (show IsIntegral k (z ^ d) by
    rw [hzpow]; exact isIntegral_one).of_pow hd
  obtain ⟨a, ha⟩ := scalar_of_isIntegral hzi
  let ev₀ : T →ₐ[k] H := (Algebra.TensorProduct.lid k H).toAlgHom.comp
    (Algebra.TensorProduct.map ε (AlgHom.id k H))
  let ev := ε.comp ev₀
  have hεinv : ε (↑u⁻¹ : H) = 1 := by
    have h := congrArg ε u.mul_inv
    have hu : ε (u : H) = 1 := hε
    simpa only [map_mul, hu, one_mul, map_one] using h
  have hevV : ev v = 1 := by
    change ε (Algebra.TensorProduct.lid k H (Algebra.TensorProduct.map ε (AlgHom.id k H)
      ((↑u⁻¹ : H) ⊗ₜ[k] (↑u⁻¹ : H)))) = 1
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.lid_tmul,
      hεinv, one_smul, hεinv]
  have hevU : ev (Δ (u : H)) = 1 := by
    change ε (hopfTranslation ε (u : H)) = 1
    exact (hopfTranslation_counit ε (u : H)).trans hε
  have heval : ev z = 1 := by
    change ev (Δ (u : H) * v) = 1
    rw [map_mul, hevU, hevV, one_mul]
  have ha1 : a = 1 := by
    simpa [heval] using congrArg ev ha
  have hz1 : z = 1 := ha.symm.trans (by rw [ha1, map_one])
  have hInv' : v * ((u : H) ⊗ₜ[k] (u : H)) = 1 := (mul_comm _ _).trans hInv
  change Δ (u : H) = (u : H) ⊗ₜ[k] (u : H)
  calc
    Δ (u : H) = z * ((u : H) ⊗ₜ[k] (u : H)) := by
      change Δ (u : H) = (Δ (u : H) * v) * _
      rw [mul_assoc, hInv', mul_one]
    _ = (u : H) ⊗ₜ[k] (u : H) := by rw [hz1, one_mul]

end Roots

end WideE
