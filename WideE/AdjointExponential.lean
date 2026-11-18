import WideE.KostantNormalForm

/-! Exponentiating an associative commutator is conjugation by the exponential. -/

noncomputable section

namespace WideE

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A] [Algebra ℚ A]

omit [Algebra ℚ A] in
private theorem leftAdjointDerivation_eq_mulLeft_add_mulRight (a : A) :
    (leftAdjointDerivation k a).toLinearMap = LinearMap.mulLeft k a + LinearMap.mulRight k (-a) := by
  apply LinearMap.ext
  intro x
  change leftAdjointDerivation k a x = a * x + x * (-a)
  rw [leftAdjointDerivation_apply, LieRing.of_associative_ring_bracket, mul_neg, sub_eq_add_neg]

omit [Algebra ℚ A] in
private theorem isNilpotent_mulRight (a : A) (ha : IsNilpotent a) :
    IsNilpotent (LinearMap.mulRight k a) := by
  obtain ⟨n, hn⟩ := ha
  exact ⟨n, by rw [LinearMap.pow_mulRight, hn, LinearMap.mulRight_zero_eq_zero]⟩

omit [Algebra ℚ A] in
/-- A nilpotent element has a nilpotent adjoint action in the commutator Lie algebra. -/
theorem isNilpotent_leftAdjointDerivation_of_isNilpotent (a : A) (ha : IsNilpotent a) :
    IsNilpotent (leftAdjointDerivation k a).toLinearMap := by
  rw [leftAdjointDerivation_eq_mulLeft_add_mulRight]
  exact (LinearMap.commute_mulLeft_right (R := k) a (-a)).isNilpotent_add
    (ha.map (Algebra.lmul k A)) (isNilpotent_mulRight _ ha.neg)

private theorem exp_mulRight_apply (a : A) (ha : IsNilpotent a) (x : A) :
    IsNilpotent.exp (LinearMap.mulRight k a) x = x * IsNilpotent.exp a := by
  obtain ⟨n, hn⟩ := ha
  have hR : LinearMap.mulRight k a ^ n = 0 := by
    rw [LinearMap.pow_mulRight, hn, LinearMap.mulRight_zero_eq_zero]
  rw [IsNilpotent.exp_eq_sum hR, IsNilpotent.exp_eq_sum hn, LinearMap.sum_apply, Finset.mul_sum]
  simp only [LinearMap.pow_mulRight, LinearMap.smul_apply, LinearMap.mulRight_apply, mul_smul_comm]

/-- The finite Lie exponential acts by actual conjugation by the finite associative exponential. -/
theorem leftAdjointExp_eq_exponential_conjugation (a : A) (ha : IsNilpotent a) (x : A) :
    LieDerivation.exp (leftAdjointDerivation k a) (isNilpotent_leftAdjointDerivation_of_isNilpotent a ha) x =
      IsNilpotent.exp a * x * IsNilpotent.exp (-a) := by
  have hL := ha.map (Algebra.lmul k A)
  have hR : IsNilpotent (LinearMap.mulRight k (-a)) := isNilpotent_mulRight _ ha.neg
  rw [LieDerivation.exp_map_apply, leftAdjointDerivation_eq_mulLeft_add_mulRight,
    IsNilpotent.exp_add_of_commute (LinearMap.commute_mulLeft_right (R := k) a (-a)) hL hR,
    Module.End.mul_apply, exp_mulRight_apply _ ha.neg]
  change IsNilpotent.exp (Algebra.lmul k A a) (x * IsNilpotent.exp (-a)) = _
  rw [← IsNilpotent.map_exp ha (Algebra.lmul k A)]
  exact mul_assoc _ _ _ |>.symm

end WideE
