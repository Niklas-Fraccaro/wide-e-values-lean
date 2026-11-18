import WideE.HopfQuotient

/-! The kernels of additive and multiplicative characters as Hopf quotients. -/

noncomputable section

open scoped TensorProduct

namespace WideE

variable {k H : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H]

/-- The kernel of an additive character is defined by its primitive coordinate. -/
theorem primitiveIdeal_isHopf (x : H)
    (hD : Coalgebra.comul (R := k) x = x ⊗ₜ[k] 1 + 1 ⊗ₜ[k] x)
    (he : Coalgebra.counit (R := k) x = 0) : IsHopfIdeal k (Ideal.span {x}) := by
  let π := Ideal.Quotient.mkₐ k (Ideal.span ({x} : Set H))
  have hx : π x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton x))
  refine IsHopfIdeal.span_of_generators k {x} ?_ ?_ ?_
  · intro a ha
    have hA : a = x := Set.mem_singleton_iff.mp ha
    subst a
    change Algebra.TensorProduct.map π π (Coalgebra.comul (R := k) x) = 0
    rw [hD, map_add, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      hx, TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]
  · intro a ha
    have hA : a = x := Set.mem_singleton_iff.mp ha
    subst a
    exact he
  · intro a ha
    have hA : a = x := Set.mem_singleton_iff.mp ha
    subst a
    have h := HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) x
    simp only [hD, map_add, LinearMap.rTensor_tmul, LinearMap.mul'_apply,
      HopfAlgebra.antipode_one, mul_one, one_mul, he, map_zero] at h
    simpa only [map_add, hx, add_zero, map_zero] using congrArg π h

/-- The kernel of a multiplicative character is defined by its grouplike coordinate minus one. -/
theorem grouplikeIdeal_isHopf (x : H)
    (hD : Coalgebra.comul (R := k) x = x ⊗ₜ[k] x)
    (he : Coalgebra.counit (R := k) x = 1) : IsHopfIdeal k (Ideal.span {x - 1}) := by
  let π := Ideal.Quotient.mkₐ k (Ideal.span ({x - 1} : Set H))
  have hx : π x = 1 := by
    have h : π (x - 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton (x - 1)))
    rwa [map_sub, map_one, sub_eq_zero] at h
  refine IsHopfIdeal.span_of_generators k {x - 1} ?_ ?_ ?_
  · rintro a rfl
    change Algebra.TensorProduct.map π π (Bialgebra.comulAlgHom k H (x - 1)) = 0
    rw [map_sub, map_one, map_sub, map_one]
    change Algebra.TensorProduct.map π π (Coalgebra.comul (R := k) x) - 1 = 0
    rw [hD, Algebra.TensorProduct.map_tmul, hx, ← Algebra.TensorProduct.one_def, sub_self]
  · rintro a rfl
    change Bialgebra.counitAlgHom k H (x - 1) = 0
    rw [map_sub, map_one, show Bialgebra.counitAlgHom k H x = 1 from he, sub_self]
  · rintro a rfl
    have h := HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) x
    rw [hD, LinearMap.rTensor_tmul, LinearMap.mul'_apply, he, map_one] at h
    have hS : π (HopfAlgebra.antipode (R := k) x) = 1 := by
      simpa only [map_mul, hx, mul_one, map_one] using congrArg π h
    change π (HopfAlgebra.antipode (R := k) (x - 1)) = 0
    rw [map_sub, HopfAlgebra.antipode_one, map_sub, map_one, hS, sub_self]

end WideE
