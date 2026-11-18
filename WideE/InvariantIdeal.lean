import WideE.HopfLieAlgebra
import Mathlib.RingTheory.Filtration

/-!
# Ideals preserved by all invariant derivations

An Euler derivation built from a cotangent basis acts on the `n`th augmentation
graded piece by `n`. An invariant ideal vanishing at the identity therefore
vanishes to every order there.
-/

noncomputable section

namespace WideE

section Euler

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

private theorem euler_sub_smul_mem_succ_pow (I : Ideal A) (E : Derivation k A A)
    (h₀ : ∀ a, E a ∈ I) (h₁ : ∀ a ∈ I, E a - a ∈ I ^ 2) (n : ℕ) :
    ∀ a ∈ I ^ n, E a - (n : k) • a ∈ I ^ (n + 1) := by
  induction n with
  | zero => simpa only [Nat.cast_zero, zero_smul, sub_zero, zero_add, pow_one] using fun a _ => h₀ a
  | succ n ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro a ha b hb
      have he : E (a * b) - ((n + 1 : ℕ) : k) • (a * b) =
          (E a - (n : k) • a) * b + a * (E b - b) := by
        rw [E.leibniz, Nat.cast_succ, add_smul, one_smul]
        simp only [Algebra.id.smul_eq_mul, Algebra.smul_def]
        ring
      rw [he]
      exact (I ^ (n + 2)).add_mem
        (by simpa only [pow_succ _ (n + 1)] using Ideal.mul_mem_mul (ih a ha) hb)
        (by simpa only [pow_add I n 2] using Ideal.mul_mem_mul ha (h₁ b hb))
    · intro a b ha hb
      rw [map_add, smul_add, add_sub_add_comm]
      exact (I ^ (n + 2)).add_mem ha hb

end Euler

section Hopf

variable {k H : Type*} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsDomain H]

local notation "I" => (hopfAugmentationIdeal k H)
local notation "ε" => (Bialgebra.counitAlgHom k H)
local notation "π" => (hopfCotangentProjection k H)

omit [CharZero k] [Algebra.FiniteType k H] [IsDomain H] in
private theorem projection_eq_toCotangent {a : H} (ha : a ∈ I) : π a = (I).toCotangent ⟨a, ha⟩ := by
  rw [hopfCotangentProjection_apply]
  congr 1
  apply Subtype.ext
  change a - algebraMap k H (ε a) = a
  rw [show ε a = 0 from ha, map_zero, sub_zero]

omit [IsDomain H] in
/-- An ideal stable under the invariant derivations and vanishing at
the identity lies in every power of the augmentation ideal. -/
theorem hopfInvariantIdeal_le_augmentation_pow (J : Ideal H) (hJ : J ≤ I)
    (hStable : ∀ D : hopfInvariantDerivations k H, ∀ a ∈ J, D.val a ∈ J) :
    ∀ n : ℕ, J ≤ I ^ n := by
  classical
  letI := hopfCotangent_finiteDimensional k H
  let b := Module.finBasis k (HopfCotangent k H)
  choose x hx using fun i => (I).toCotangent_surjective (b i)
  let D (i : Fin (Module.finrank k (HopfCotangent k H))) : hopfInvariantDerivations k H :=
    hopfLieVectorInvariantDerivations (b.coord i)
  let E : Derivation k H H := ∑ i, (x i : H) • (D i).val
  have hE (a : H) : E a = ∑ i, (x i : H) * (D i).val a := by
    let evalD : Derivation k H H →+ H :=
      { toFun := fun D => D a
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    change evalD (∑ i, (x i : H) • (D i).val) = _
    rw [map_sum]
    rfl
  have h₀ (a : H) : E a ∈ I := by
    rw [hE]
    exact (I).sum_mem fun i _ => (I).mul_mem_right _ (x i).prop
  have h₁ (a : H) (ha : a ∈ I) : E a - a ∈ I ^ 2 := by
    have hr : π (E a) = π a := by
      rw [hE, map_sum, ← b.sum_repr (π a)]
      apply Finset.sum_congr rfl
      intro i _
      rw [hopfCotangentProjection_mul, show ε (x i : H) = 0 from (x i).property,
        zero_smul, zero_add, projection_eq_toCotangent (x i).property, hx i]
      rw [show (D i).val = (hopfLieVectorInvariantDerivations (b.coord i)).val from rfl,
        hopfLieVectorInvariantDerivations_counit]
      rfl
    have he : E a - a ∈ I := (I).sub_mem (h₀ a) ha
    apply ((I).toCotangent_eq_zero ⟨E a - a, he⟩).mp
    rw [← projection_eq_toCotangent he, map_sub, hr, sub_self]
  have hPow (n : ℕ) : J ≤ I ^ n := by
    cases n with
    | zero => simp
    | succ n =>
      induction n with
      | zero => simpa using hJ
      | succ n ih =>
        intro a ha
        have hEa : E a ∈ I ^ (n + 2) := by
          rw [hE]
          apply (I ^ (n + 2)).sum_mem
          intro i _
          rw [pow_succ, mul_comm (x i : H)]
          exact Ideal.mul_mem_mul (ih (hStable (D i) a ha)) (x i).property
        have hDiff := euler_sub_smul_mem_succ_pow I E h₀ h₁ (n + 1) a (ih ha)
        have hMem := (I ^ (n + 2)).sub_mem hEa hDiff
        rw [sub_sub_cancel] at hMem
        have hn : ((n + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
        have h := (I ^ (n + 2)).mul_mem_left (algebraMap k H ((n + 1 : ℕ) : k)⁻¹) hMem
        simpa only [← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hn, one_smul] using h
  exact hPow

/-- An ideal of a Hopf domain vanishing at the identity and stable under
all invariant derivations is zero. -/
theorem hopfInvariantIdeal_eq_bot (J : Ideal H) (hJ : J ≤ I)
    (hStable : ∀ D : hopfInvariantDerivations k H, ∀ a ∈ J, D.val a ∈ J) : J = ⊥ := by
  letI := Algebra.FiniteType.isNoetherianRing k H
  have hTop : (I : Ideal H) ≠ ⊤ := by
    intro h
    have hOne : (1 : H) ∈ I := h ▸ Submodule.mem_top
    exact one_ne_zero ((map_one ε).symm.trans hOne)
  rw [eq_bot_iff, ← (I).iInf_pow_eq_bot_of_isDomain hTop]
  exact le_iInf (hopfInvariantIdeal_le_augmentation_pow J hJ hStable)

end Hopf

end WideE
