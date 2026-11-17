import WideE.AdditiveDescent
import WideE.PVTorsor

/-! Additive descent for the primitive coordinate of a constant group torsor. -/

open scoped TensorProduct

noncomputable section

namespace WideE

open StrictEUnit

attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule

variable {k B S H : Type*} [Field k] [CommRing B] [CommRing S] [CommRing H]
  [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S]
  [HopfAlgebra k H]

variable (T : AffineHopfTorsor k B S H)

private theorem coaction_eq_inverse_chart :
    T.coaction = inverseMultiplicationCoaction T.chart := by
  apply AlgHom.ext
  intro s
  rw [inverseMultiplicationCoaction_apply, AffineHopfTorsor.chart_symm_apply,
    ← Algebra.TensorProduct.one_def, one_mul]

private theorem tripleChart_coaction_comul (s : S) :
    pvTripleChart T.chart
      (Algebra.TensorProduct.map (AlgHom.id S S) (Bialgebra.comulAlgHom k H) (T.coaction s)) =
      (1 : S) ⊗ₜ[B] ((1 : S) ⊗ₜ[B] s) := by
  rw [← T.coassociative s, coaction_eq_inverse_chart T]
  rw [pvTripleChart_action_left, inverseMultiplicationCoaction_apply, AlgEquiv.apply_symm_apply]

private theorem tripleChart_comul (x : S ⊗[k] H) :
    pvTripleChart T.chart (Algebra.TensorProduct.map (AlgHom.id S S) (Bialgebra.comulAlgHom k H) x) =
      pvMiddleInsertion (k := k) (T.chart x) := by
  obtain ⟨y, rfl⟩ := T.chart.symm.surjective x
  rw [AlgEquiv.apply_symm_apply]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s t =>
    rw [AffineHopfTorsor.chart_symm_apply]
    change pvTripleChart T.chart (Algebra.TensorProduct.map (AlgHom.id S S)
      (Bialgebra.comulAlgHom k H) (algebraMap S (S ⊗[k] H) s * T.coaction t)) = _
    rw [map_mul, AlgHom.commutes, map_mul, AlgEquiv.commutes, tripleChart_coaction_comul,
      pvMiddleInsertion_tmul]
    change (s ⊗ₜ[B] ((1 : S) ⊗ₜ[B] (1 : S))) * ((1 : S) ⊗ₜ[B] ((1 : S) ⊗ₜ[B] t)) = _
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

private theorem tripleChart_append_one (y : S ⊗[B] S) :
    Algebra.TensorProduct.map (AlgHom.id B S) (T.chart.toAlgHom.restrictScalars B)
      (mixedAlgebraAssoc (k := k) (B := B) (y ⊗ₜ[k] (1 : H))) =
      Algebra.TensorProduct.assoc B S S S (y ⊗ₜ[B] (1 : S)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | tmul s t =>
    rw [mixedAlgebraAssoc_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      AlgHom.restrictScalars_apply, Algebra.TensorProduct.assoc_tmul]
    exact congrArg (fun x => s ⊗ₜ[B] x) (T.chart.commutes t)

private theorem associated_additiveCocycle (a : S ⊗[B] S) :
    Algebra.TensorProduct.assoc B S S S (additiveDescentCocycle B S a) =
      (1 : S) ⊗ₜ[B] a - pvMiddleInsertion (k := k) a +
        Algebra.TensorProduct.assoc B S S S (a ⊗ₜ[B] (1 : S)) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, TensorProduct.tmul_add, TensorProduct.add_tmul, hx, hy]
    abel
  | tmul s t =>
    simp only [additiveDescentCocycle_tmul, map_add, map_sub, Algebra.TensorProduct.assoc_tmul,
      pvMiddleInsertion_tmul]

/-- A primitive coordinate of the constant group is realized as the
additive translate of an element of the torsor algebra. -/
theorem exists_primitive_torsor_coordinate (h : H)
    (hPrimitive : Bialgebra.comulAlgHom k H h = (1 : H) ⊗ₜ[k] h + h ⊗ₜ[k] (1 : H)) :
    ∃ s : S, T.coaction s = s ⊗ₜ[k] (1 : H) + (1 : S) ⊗ₜ[k] h := by
  let a := T.chart ((1 : S) ⊗ₜ[k] h)
  have hFirst : pvTripleChart T.chart ((1 : S) ⊗ₜ[k] ((1 : H) ⊗ₜ[k] h)) = (1 : S) ⊗ₜ[B] a := by
    rw [pvTripleChart_tmul, show T.chart ((1 : S) ⊗ₜ[k] (1 : H)) =
      (1 : S) ⊗ₜ[B] (1 : S) from T.chart.commutes 1, mixedAlgebraAssoc_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.restrictScalars_apply]
    rfl
  have hLast : pvTripleChart T.chart ((1 : S) ⊗ₜ[k] (h ⊗ₜ[k] (1 : H))) =
      Algebra.TensorProduct.assoc B S S S (a ⊗ₜ[B] (1 : S)) := by
    rw [pvTripleChart_tmul]
    exact tripleChart_append_one T a
  have hMiddle := tripleChart_comul T ((1 : S) ⊗ₜ[k] h)
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hPrimitive,
    TensorProduct.tmul_add, map_add, hFirst, hLast] at hMiddle
  have ha : additiveDescentCocycle B S a = 0 := by
    apply (Algebra.TensorProduct.assoc B S S S).injective
    rw [map_zero, associated_additiveCocycle (k := k), ← hMiddle]
    abel
  letI := T.faithfullyFlat
  obtain ⟨s, hs⟩ := exists_additiveDescentPrimitive B S a ha
  have he := congrArg T.chart.symm hs
  change T.chart.symm ((1 : S) ⊗ₜ[B] s - s ⊗ₜ[B] (1 : S)) =
    T.chart.symm (T.chart ((1 : S) ⊗ₜ[k] h)) at he
  rw [map_sub, AffineHopfTorsor.chart_symm_apply, ← Algebra.TensorProduct.one_def, one_mul,
    show T.chart.symm (s ⊗ₜ[B] (1 : S)) = s ⊗ₜ[k] (1 : H) from T.chart.symm.commutes s,
    AlgEquiv.symm_apply_apply] at he
  exact ⟨s, (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)⟩

end WideE
