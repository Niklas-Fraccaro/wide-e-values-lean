import WideE.PVComponents

/-! The Hopf algebra on the connected component containing the identity. -/

noncomputable section

open scoped TensorProduct

namespace WideE

attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule

set_option maxHeartbeats 800000

namespace ComponentHopfPresentation

universe u

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  (P : ComponentHopfPresentation k H)

local notation "C" => P.IdentityComponent
local notation "π" => P.identityQuotient
local notation "M" => Algebra.TensorProduct.map (S := k)
local notation "Δ" => (Bialgebra.comulAlgHom k H)
local notation "ε" => (Bialgebra.counitAlgHom k H)
local notation "e₀" => P.idempotent P.identityIndex
local notation "J" => (Ideal.span ({1 - e₀} : Set H))

theorem identityComponent_finiteType [Algebra.FiniteType k H] : Algebra.FiniteType k C :=
  Algebra.FiniteType.of_surjective inferInstance π P.identityQuotient_surjective

private theorem identityIdempotent : IsIdempotentElem e₀ :=
  letI := P.index_finite
  P.complete.idem P.identityIndex

private theorem inversion_counit (x : H) : ε (P.inversion x) = ε x := by
  let c := Algebra.TensorProduct.rid k k H
  have h (z : H ⊗[k] H) :
      ε (LinearMap.mul' k H ((HopfAlgebra.antipode (R := k)).rTensor H z)) =
        ε (P.inversion (c (M (AlgHom.id k H) ε z))) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      rw [← P.inversion_eq, LinearMap.rTensor_tmul, LinearMap.mul'_apply,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      simp only [c, Algebra.TensorProduct.rid_tmul, Algebra.smul_def,
        AlgHom.toLinearMap_apply, map_mul, AlgHom.commutes]
      exact mul_comm _ _
  have hx := congrArg ε (HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) x)
  have h' : M (AlgHom.id k H) ε (Δ x) = c.symm x :=
    Coalgebra.lTensor_counit_comul (R := k) x
  change ε (LinearMap.mul' k H ((HopfAlgebra.antipode (R := k)).rTensor H (Δ x))) =
    ε (algebraMap k H (ε x)) at hx
  rw [h, h', AlgEquiv.apply_symm_apply, AlgHom.commutes] at hx
  exact hx

private theorem counit_comul (x : H) :
    Algebra.TensorProduct.lift ε ε (fun _ _ => Commute.all _ _) (Δ x) = ε x := by
  let c := Algebra.TensorProduct.rid k k H
  have h (z : H ⊗[k] H) : Algebra.TensorProduct.lift ε ε (fun _ _ => Commute.all _ _) z =
      ε (c (M (AlgHom.id k H) ε z)) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      simp only [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      simp only [c, Algebra.TensorProduct.rid_tmul, Algebra.smul_def, map_mul, AlgHom.commutes]
      exact mul_comm _ _
  rw [h, show M (AlgHom.id k H) ε (Δ x) = c.symm x from Coalgebra.lTensor_counit_comul x,
    AlgEquiv.apply_symm_apply]

private theorem inversion_identityIdempotent :
    π (P.inversion e₀) = 1 := by
  letI := P.identityComponent_connected
  rcases idempotent_eq_zero_or_one_of_preconnected (P.identityIdempotent.map ((π).comp P.inversion)) with hz | ho
  · have h := congrArg P.identityCounit hz
    change P.identityCounit (π (P.inversion e₀)) = P.identityCounit 0 at h
    rw [map_zero, show P.identityCounit (π (P.inversion e₀)) = ε (P.inversion e₀) from
      AlgHom.congr_fun P.identityCounit_comp_quotient _, P.inversion_counit, P.identityIndex_counit] at h
    exact (one_ne_zero h).elim
  · exact ho

private theorem comul_identityIdempotent [IsAlgClosed k] [Algebra.FiniteType k H] :
    M π π (Δ e₀) = 1 := by
  letI := P.identityComponent_finiteType
  letI := P.identityComponent_connected
  letI : Nontrivial C := P.identityCounit.toRingHom.domain_nontrivial
  let c := Algebra.TensorProduct.lift P.identityCounit P.identityCounit (fun _ _ => Commute.all _ _)
  have hc : c.comp (M π π) = Algebra.TensorProduct.lift ε ε (fun _ _ => Commute.all _ _) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
    exact congrArg₂ (· * ·) (AlgHom.congr_fun P.identityCounit_comp_quotient a)
      (AlgHom.congr_fun P.identityCounit_comp_quotient b)
  have he : c (M π π (Δ e₀)) = 1 := by
    change (c.comp (M π π)) (Δ e₀) = 1
    rw [hc, counit_comul, P.identityIndex_counit]
  rcases idempotent_tensor_eq_zero_or_one
    (fun _ h => idempotent_eq_zero_or_one_of_preconnected h)
    (fun _ h => idempotent_eq_zero_or_one_of_preconnected h)
    (P.identityIdempotent.map ((M π π).comp Δ)) with h | h
  · change M π π (Δ e₀) = 0 at h
    rw [h, map_zero] at he
    exact (zero_ne_one he).elim
  · exact h

/-- The ambient antipode preserves the ideal defining the identity component. -/
def identityInversion : C →ₐ[k] C :=
  Ideal.Quotient.liftₐ J ((π).comp P.inversion) (by
    change J ≤ RingHom.ker ((π).comp P.inversion)
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change π (P.inversion (1 - e₀)) = 0
    rw [map_sub, map_one, map_sub, map_one, P.inversion_identityIdempotent, sub_self])

theorem identityInversion_quotient (x : H) :
    P.identityInversion (π x) = π (P.inversion x) := rfl

variable [IsAlgClosed k] [Algebra.FiniteType k H]

/-- Products in the connected identity component are still in the component,
which lets the original comultiplication factor through its quotient. -/
def identityComul : C →ₐ[k] C ⊗[k] C :=
  Ideal.Quotient.liftₐ J ((M π π).comp Δ) (by
    change J ≤ RingHom.ker ((M π π).comp Δ)
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change M π π (Δ (1 - e₀)) = 0
    rw [map_sub, map_one, map_sub, map_one, P.comul_identityIdempotent, sub_self])

theorem identityComul_quotient (x : H) :
    P.identityComul (π x) = M π π (Δ x) := rfl

private theorem identityComul_coassoc (x : C) :
    Algebra.TensorProduct.assoc k C C C (M P.identityComul (AlgHom.id k C) (P.identityComul x)) =
      M (AlgHom.id k C) P.identityComul (P.identityComul x) := by
  obtain ⟨a, rfl⟩ := P.identityQuotient_surjective x
  rw [P.identityComul_quotient]
  have hΔ : P.identityComul.comp π = (M π π).comp Δ := AlgHom.ext P.identityComul_quotient
  have hL : (M P.identityComul (AlgHom.id k C)).comp (M π π) =
      (M (M π π) π).comp (M Δ (AlgHom.id k H)) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp,
      AlgHom.id_comp, AlgHom.comp_id, hΔ]
  have hR : (M (AlgHom.id k C) P.identityComul).comp (M π π) =
      (M π (M π π)).comp (M (AlgHom.id k H) Δ) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp,
      AlgHom.id_comp, AlgHom.comp_id, hΔ]
  have hAssoc : (Algebra.TensorProduct.assoc k C C C).toAlgHom.comp (M (M π π) π) =
      (M π (M π π)).comp (Algebra.TensorProduct.assoc k H H H).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro z h
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
  change ((Algebra.TensorProduct.assoc k C C C).toAlgHom.comp
    ((M P.identityComul (AlgHom.id k C)).comp (M π π))) (Δ a) =
      ((M (AlgHom.id k C) P.identityComul).comp (M π π)) (Δ a)
  rw [hL, hR, ← AlgHom.comp_assoc, hAssoc, AlgHom.comp_assoc]
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom]
  exact congrArg (M π (M π π)) (Coalgebra.coassoc_apply (R := k) a)

private theorem identityComul_leftCounit (x : C) :
    M P.identityCounit (AlgHom.id k C) (P.identityComul x) = (Algebra.TensorProduct.lid k C).symm x := by
  obtain ⟨a, rfl⟩ := P.identityQuotient_surjective x
  rw [P.identityComul_quotient]
  change ((M P.identityCounit (AlgHom.id k C)).comp (M π π)) (Δ a) = _
  rw [← Algebra.TensorProduct.map_comp, P.identityCounit_comp_quotient, AlgHom.id_comp]
  rw [show M ε π = (M (AlgHom.id k k) π).comp (M ε (AlgHom.id k H)) by
    apply Algebra.TensorProduct.ext'
    intro _ _
    rfl]
  rw [AlgHom.comp_apply, show M ε (AlgHom.id k H) (Δ a) =
    (Algebra.TensorProduct.lid k H).symm a from Coalgebra.rTensor_counit_comul a]
  rfl

private theorem identityComul_rightCounit (x : C) :
    M (AlgHom.id k C) P.identityCounit (P.identityComul x) = (Algebra.TensorProduct.rid k k C).symm x := by
  obtain ⟨a, rfl⟩ := P.identityQuotient_surjective x
  rw [P.identityComul_quotient]
  change ((M (AlgHom.id k C) P.identityCounit).comp (M π π)) (Δ a) = _
  rw [← Algebra.TensorProduct.map_comp, P.identityCounit_comp_quotient, AlgHom.id_comp]
  rw [show M π ε = (M π (AlgHom.id k k)).comp (M (AlgHom.id k H) ε) by
    apply Algebra.TensorProduct.ext'
    intro _ _
    rfl]
  rw [AlgHom.comp_apply, show M (AlgHom.id k H) ε (Δ a) =
    (Algebra.TensorProduct.rid k k H).symm a from Coalgebra.lTensor_counit_comul a]
  rfl

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem identityInversion_mul (z : H ⊗[k] H) :
    LinearMap.mul' k C (P.identityInversion.toLinearMap.rTensor C (M π π z)) =
      π (LinearMap.mul' k H ((HopfAlgebra.antipode (R := k)).rTensor H z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
      LinearMap.mul'_apply, LinearMap.mul'_apply, ← P.inversion_eq, map_mul]
    rfl

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem identityMul_inversion (z : H ⊗[k] H) :
    LinearMap.mul' k C (P.identityInversion.toLinearMap.lTensor C (M π π z)) =
      π (LinearMap.mul' k H ((HopfAlgebra.antipode (R := k)).lTensor H z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
      LinearMap.mul'_apply, LinearMap.mul'_apply, ← P.inversion_eq, map_mul]
    rfl

/-- The coordinate algebra of the identity component with its quotient Hopf
structure. -/
def identityHopf : HopfAlgebra k C where
  toBialgebra := Bialgebra.ofAlgHom P.identityComul P.identityCounit
    (AlgHom.ext P.identityComul_coassoc) (AlgHom.ext P.identityComul_leftCounit)
    (AlgHom.ext P.identityComul_rightCounit)
  antipode := P.identityInversion.toLinearMap
  mul_antipode_rTensor_comul := by
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := P.identityQuotient_surjective x
    change LinearMap.mul' k C (P.identityInversion.toLinearMap.rTensor C (P.identityComul (π a))) =
      algebraMap k C (P.identityCounit (π a))
    rw [P.identityComul_quotient, P.identityInversion_mul]
    exact congrArg π (HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) a)
  mul_antipode_lTensor_comul := by
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := P.identityQuotient_surjective x
    change LinearMap.mul' k C (P.identityInversion.toLinearMap.lTensor C (P.identityComul (π a))) =
      algebraMap k C (P.identityCounit (π a))
    rw [P.identityComul_quotient, P.identityMul_inversion]
    exact congrArg π (HopfAlgebra.mul_antipode_lTensor_comul_apply (R := k) a)

end ComponentHopfPresentation

end WideE
