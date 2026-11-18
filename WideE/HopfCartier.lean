import WideE.InvariantIdeal
import WideE.HopfSmoothLocus
import AlgebraicPoint

/-! Cartier's reducedness argument for affine group schemes in characteristic zero. -/

noncomputable section

namespace WideE

section Derivations

variable {k A : Type*} [Field k] [CharZero k] [CommRing A] [Algebra k A]

/-- In characteristic zero, derivations of an algebra preserve nilpotent elements. -/
theorem isNilpotent_derivation_apply (D : Derivation k A A) {a : A} (ha : IsNilpotent a) :
    IsNilpotent (D a) := by
  let b := D a
  have hStep (n m : ℕ) (h : a ^ (n + 1) * b ^ (m + 1) = 0) :
      a ^ n * b ^ (m + 3) = 0 := by
    have hd : (D (a ^ (n + 1) * b ^ (m + 1))) * b = 0 := by
      rw [h, map_zero, zero_mul]
    have hExp : (D (a ^ (n + 1) * b ^ (m + 1))) * b =
        ((m + 1 : ℕ) : A) * D b * (a ^ (n + 1) * b ^ (m + 1)) +
          ((n + 1 : ℕ) : A) * (a ^ n * b ^ (m + 3)) := by
      rw [D.leibniz, D.leibniz_pow, D.leibniz_pow]
      simp only [Nat.add_sub_cancel, Algebra.id.smul_eq_mul, nsmul_eq_mul, ← show b = D a from rfl]
      simp only [pow_add, pow_one, pow_succ, pow_zero, one_mul]
      ring
    rw [hExp, h, mul_zero, zero_add] at hd
    have hu : IsUnit (((n + 1 : ℕ) : A)) := by
      have hne : ((n + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hne).map (algebraMap k A)
    exact hu.mul_right_eq_zero.mp hd
  have hDescend (n m : ℕ) (h : a ^ n * b ^ (m + 1) = 0) : IsNilpotent b := by
    induction n generalizing m with
    | zero => exact ⟨m + 1, by simpa only [pow_zero, one_mul] using h⟩
    | succ n ih =>
      exact ih (m + 2) (by simpa only [Nat.add_assoc] using hStep n m h)
  obtain ⟨n, hn⟩ := ha
  exact hDescend n 0 (by rw [hn, zero_mul])

end Derivations

section Group

universe u

/-- A finite-type affine group scheme over an algebraically closed field
of characteristic zero is reduced. -/
theorem hopfIsReduced_of_charZero (k H : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] : IsReduced H := by
  let I := hopfAugmentationIdeal k H
  let ε := Bialgebra.counitAlgHom k H
  letI := Algebra.FiniteType.isNoetherianRing k H
  have hI : nilradical H ≤ I := fun _ ha =>
    isNilpotent_iff_eq_zero.mp ((mem_nilradical.mp ha).map ε)
  have hStable (D : hopfInvariantDerivations k H) (a : H) (ha : a ∈ nilradical H) :
      D.val a ∈ nilradical H :=
    mem_nilradical.mpr (isNilpotent_derivation_apply D.val (mem_nilradical.mp ha))
  have hPow := hopfInvariantIdeal_le_augmentation_pow (nilradical H) hI hStable
  constructor
  intro a ha
  by_contra hne
  let J : Ideal H := LinearMap.ker (LinearMap.toSpanSingleton H H a)
  have hJ : J ≠ ⊤ := by
    intro h
    have h1 : (1 : H) ∈ J := h ▸ Submodule.mem_top
    change (1 : H) • a = 0 at h1
    exact hne (by simpa only [one_smul] using h1)
  obtain ⟨m, hm, hJM⟩ := Ideal.exists_le_maximal J hJ
  letI : m.IsMaximal := hm
  let p : H →ₐ[k] k := StrictEUnit.maximalIdealPoint m
  let t := hopfTranslation p
  have hNil : t a ∈ nilradical H := mem_nilradical.mpr (ha.map t)
  have hMem : t a ∈ (⨅ n : ℕ, I ^ n • ⊤ : Submodule H H) := by
    rw [Submodule.mem_iInf]
    intro n
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact hPow n hNil
  obtain ⟨r, hr⟩ := (I.mem_iInf_smul_pow_eq_bot_iff (t a)).mp hMem
  let u := t.symm r
  have hu : (u : H) ∈ m := by
    rw [← StrictEUnit.maximalIdealPoint_ker (k := k) m]
    change p u = 0
    rw [← hopfTranslation_counit p u]
    exact show ε (t (t.symm r)) = 0 by rw [AlgEquiv.apply_symm_apply]; exact r.property
  have hMul : u * a = a := by
    apply t.injective
    rw [map_mul, show t u = r from t.apply_symm_apply r]
    exact hr
  have hOne : (1 : H) ∈ m := by
    have hDiff : 1 - u ∈ J := by
      change (1 - u) * a = 0
      rw [sub_mul, one_mul, hMul, sub_self]
    simpa only [sub_add_cancel] using m.add_mem (hJM hDiff) hu
  exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr hOne)

/-- A finite-type affine group scheme over an algebraically closed field
of characteristic zero is smooth. -/
theorem hopfSmooth_of_charZero (k H : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] : Algebra.Smooth k H := by
  letI : IsReduced H := hopfIsReduced_of_charZero k H
  exact hopfSmooth_of_isReduced

end Group

end WideE
