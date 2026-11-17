import WideE.ComponentTorsorQuotient
import WideE.IdentityComponentHopf
import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-! The residual action of the identity component on the original torsor. -/

noncomputable section

open scoped TensorProduct

namespace WideE

open StrictEUnit

attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule

set_option maxHeartbeats 1250000
set_option synthInstance.maxHeartbeats 90000

universe u

section Residual

variable {k B S H : Type u} [Field k] [IsAlgClosed k] [CommRing B] [CommRing S] [CommRing H]
  [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S] [HopfAlgebra k H]
  (T : AffineHopfTorsor k B S H) (G : ComponentHopfPresentation k H)

local notation "Q" => componentTorsorQuotient T G
local notation "C" => G.IdentityComponent
local notation "π" => G.identityQuotient
local notation "M" => Algebra.TensorProduct.map

local instance quotientScalarTower : IsScalarTower k (↥Q) S :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

private def identityCoactionOverBase : S →ₐ[B] S ⊗[k] C :=
  (M (AlgHom.id B S) π).comp T.coaction

private theorem identityCoaction_fixes (q : Q) :
    identityCoactionOverBase T G (q : S) = (q : S) ⊗ₜ[k] (1 : C) := by
  letI := T.group_finiteType
  obtain ⟨z, hz⟩ := (mem_componentTorsorQuotient_iff T G (q : S)).mp q.property
  have h (x : S ⊗[k] (G.Index → k)) :
      M (AlgHom.id B S) π (M (AlgHom.id B S) G.inclusion x) =
        coactionCounit (M (AlgHom.id B S) G.inclusion x) ⊗ₜ[k] (1 : C) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, TensorProduct.add_tmul]
    | tmul s f =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, G.identityQuotient_inclusion]
      have he : Bialgebra.counitAlgHom k H (G.inclusion f) = f G.identityIndex := by
        rw [← AlgHom.congr_fun G.identityCounit_comp_quotient (G.inclusion f)]
        change G.identityCounit (π (G.inclusion f)) = _
        rw [G.identityQuotient_inclusion, AlgHom.commutes]
        rfl
      change s ⊗ₜ[k] algebraMap k C (f G.identityIndex) =
        (s * algebraMap k S (Bialgebra.counitAlgHom k H (G.inclusion f))) ⊗ₜ[k] (1 : C)
      rw [he, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        mul_smul_comm, mul_one, TensorProduct.smul_tmul]
  have hq := h z
  rw [hz, T.counital] at hq
  exact hq

/-- Restrict the original coaction to the identity component and view it
over the coordinate algebra of the component quotient. -/
def identityComponentCoaction : S →ₐ[Q] S ⊗[k] C where
  toRingHom := (identityCoactionOverBase T G).toRingHom
  commutes' q := identityCoaction_fixes T G q

private theorem identityCoaction_restrict :
    (identityComponentCoaction T G).restrictScalars k =
      (M (AlgHom.id k S) π).comp (T.coaction.restrictScalars k) := by
  apply AlgHom.ext
  intro s
  rfl

theorem identityComponentCoaction_coassociative (s : S) :
    letI := T.group_finiteType
    Algebra.TensorProduct.assoc k S C C
      (M ((identityComponentCoaction T G).restrictScalars k) (AlgHom.id k C)
        (identityComponentCoaction T G s)) =
      M (AlgHom.id S S) (G.identityComul) (identityComponentCoaction T G s) := by
  letI := T.group_finiteType
  let ρ := T.coaction.restrictScalars k
  let ρC := (identityComponentCoaction T G).restrictScalars k
  have hρ : ρC = (M (AlgHom.id k S) π).comp ρ := identityCoaction_restrict T G
  have hΔ : G.identityComul.comp π = (M π π).comp (Bialgebra.comulAlgHom k H) :=
    AlgHom.ext G.identityComul_quotient
  have hAssoc : (Algebra.TensorProduct.assoc k S C C).toAlgHom.comp (M (M (AlgHom.id k S) π) π) =
      (M (AlgHom.id k S) (M π π)).comp (Algebra.TensorProduct.assoc k S H H).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro z g
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
    | tmul a b => rfl
  have hL : (M ρC (AlgHom.id k C)).comp (M (AlgHom.id k S) π) =
      (M (M (AlgHom.id k S) π) π).comp (M ρ (AlgHom.id k H)) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id,
      AlgHom.id_comp, AlgHom.comp_id, hρ]
  have hR : (M (AlgHom.id k S) G.identityComul).comp (M (AlgHom.id k S) π) =
      (M (AlgHom.id k S) (M π π)).comp (M (AlgHom.id k S) (Bialgebra.comulAlgHom k H)) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp, hΔ]
  change Algebra.TensorProduct.assoc k S C C (M ρC (AlgHom.id k C) (ρC s)) =
    M (AlgHom.id k S) G.identityComul (ρC s)
  rw [show ρC s = M (AlgHom.id k S) π (ρ s) from AlgHom.congr_fun hρ s]
  change ((Algebra.TensorProduct.assoc k S C C).toAlgHom.comp
    ((M ρC (AlgHom.id k C)).comp (M (AlgHom.id k S) π))) (ρ s) =
      ((M (AlgHom.id k S) G.identityComul).comp (M (AlgHom.id k S) π)) (ρ s)
  rw [hL, hR, ← AlgHom.comp_assoc, hAssoc, AlgHom.comp_assoc]
  exact congrArg (M (AlgHom.id k S) (M π π)) (T.coassociative s)

theorem identityComponentCoaction_counital (s : S) :
    letI := T.group_finiteType
    letI := G.identityHopf
    coactionCounit (identityComponentCoaction T G s) = s := by
  letI := T.group_finiteType
  letI := G.identityHopf
  have h : (coactionCounit (k := k) (S := S) (H := C)).comp (M (AlgHom.id k S) π) =
      coactionCounit (k := k) (S := S) (H := H) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    change a * algebraMap k S (G.identityCounit (π b)) =
      a * algebraMap k S (Bialgebra.counitAlgHom k H b)
    rw [show G.identityCounit (π b) = Bialgebra.counitAlgHom k H b from
      AlgHom.congr_fun G.identityCounit_comp_quotient _]
  change ((coactionCounit (k := k) (S := S) (H := C)).comp (M (AlgHom.id k S) π))
    (T.coaction s) = s
  rw [h]
  exact T.counital s

/-- Pass from tensoring over the original base to tensoring over its
component quotient subalgebra. -/
def relativeTensorQuotient : S ⊗[B] S →ₐ[S] S ⊗[Q] S :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
    ((Algebra.TensorProduct.includeRight : S →ₐ[Q] S ⊗[Q] S).restrictScalars B)
    (fun _ _ => Commute.all _ _)

private theorem relativeTensorQuotient_tmul (s t : S) :
    relativeTensorQuotient T G (s ⊗ₜ[B] t) = s ⊗ₜ[Q] t := by
  rw [relativeTensorQuotient, Algebra.TensorProduct.lift_tmul, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private theorem relativeTensorQuotient_surjective : Function.Surjective (relativeTensorQuotient T G) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' + b', map_add _ _ _⟩
  | tmul s t => exact ⟨s ⊗ₜ[B] t, relativeTensorQuotient_tmul T G s t⟩

private def identityCanonical : S ⊗[Q] S →ₐ[S] S ⊗[k] C :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft (identityComponentCoaction T G)
    (fun _ _ => Commute.all _ _)

private theorem identityCanonical_comp :
    (identityCanonical T G).comp (relativeTensorQuotient T G) =
      (M (AlgHom.id S S) π).comp T.chart.symm.toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro s t
  rw [AlgHom.comp_apply, relativeTensorQuotient_tmul, identityCanonical,
    Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.includeLeft_apply,
    AlgHom.comp_apply, AlgEquiv.coe_algHom, T.chart_symm_apply, map_mul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
  rfl

omit [IsAlgClosed k] in
private theorem coactionCounit_chart (z : S ⊗[B] S) :
    coactionCounit (T.chart.symm z) = Algebra.TensorProduct.lmul'' B z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul s t =>
    rw [T.chart_symm_apply, map_mul, T.counital]
    change (s * algebraMap k S (Bialgebra.counitAlgHom k H 1)) * t = s * t
    rw [map_one, map_one, mul_one]

private theorem relativeTensorQuotient_on_component (z : S ⊗[B] Q) :
    relativeTensorQuotient T G (M (AlgHom.id S S) (Q).val z) =
      (Algebra.TensorProduct.lmul'' B (M (AlgHom.id S S) (Q).val z)) ⊗ₜ[Q] (1 : S) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, TensorProduct.add_tmul]
  | tmul s q =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, relativeTensorQuotient_tmul]
    change s ⊗ₜ[Q] (q : S) = (s * (q : S)) ⊗ₜ[Q] (1 : S)
    have hq : (q : S) = q • (1 : S) := ((Algebra.smul_def q (1 : S)).trans (mul_one _)).symm
    rw [show s * (q : S) = q • s from (mul_comm s _).trans (Algebra.smul_def q s).symm]
    rw [hq]
    exact (TensorProduct.smul_tmul q s (1 : S)).symm

private theorem relativeTensorQuotient_identityIdempotent :
    relativeTensorQuotient T G (T.chart ((1 : S) ⊗ₜ[k] G.idempotent G.identityIndex)) = 1 := by
  classical
  letI := T.group_finiteType
  let z := (componentTorsorQuotientChart T G).symm
    ((1 : S) ⊗ₜ[k] Pi.single G.identityIndex (1 : k))
  have hz :
      M (AlgHom.id S S) (Q).val z = T.chart ((1 : S) ⊗ₜ[k] G.idempotent G.identityIndex) := by
    apply T.chart.symm.injective
    rw [← componentTorsorQuotientChart_inclusion T G, AlgEquiv.symm_apply_apply]
    change M (AlgHom.id S S) G.inclusion ((componentTorsorQuotientChart T G)
      ((componentTorsorQuotientChart T G).symm (1 ⊗ₜ[k] Pi.single G.identityIndex (1 : k)))) = _
    rw [AlgEquiv.apply_symm_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    congr 1
    letI := G.index_finite
    exact componentScalarInclusion_indicator (k := k) G.idempotent G.complete G.identityIndex
  rw [← hz, relativeTensorQuotient_on_component T G, hz, ← coactionCounit_chart T,
    AlgEquiv.symm_apply_apply]
  change ((1 : S) * algebraMap k S (Bialgebra.counitAlgHom k H (G.idempotent G.identityIndex))) ⊗ₜ[Q]
    (1 : S) = 1
  rw [G.identityIndex_counit, map_one, mul_one]
  rfl

/-- The kernel of restriction to the identity component is precisely the
relation imposed by tensoring the torsor over the quotient algebra. -/
theorem identityComponentCoaction_canonical_bijective :
    Function.Bijective (relativeCandidateCanonical (identityComponentCoaction T G)) := by
  change Function.Bijective (identityCanonical T G)
  constructor
  · apply (RingHom.injective_iff_ker_eq_bot (identityCanonical T G).toRingHom).mpr
    apply le_antisymm _ bot_le
    intro y hy
    obtain ⟨x, rfl⟩ := relativeTensorQuotient_surjective T G y
    have hx : M (AlgHom.id S S) π (T.chart.symm x) = 0 := by
      change identityCanonical T G (relativeTensorQuotient T G x) = 0 at hy
      exact (AlgHom.congr_fun (identityCanonical_comp T G) x).symm.trans hy
    let I : Ideal H := Ideal.span {1 - G.idempotent G.identityIndex}
    let i : H →ₐ[k] S ⊗[k] H := Algebra.TensorProduct.includeRight
    have hker : RingHom.ker (M (AlgHom.id S S) π) = I.map i := by
      change RingHom.ker (M (AlgHom.id k S) π) = I.map i
      rw [Algebra.TensorProduct.lTensor_ker π G.identityQuotient_surjective]
      change (RingHom.ker (Ideal.Quotient.mk I)).map i = I.map i
      rw [Ideal.mk_ker]
    let f := (relativeTensorQuotient T G).comp T.chart.toAlgHom
    have hI : I.map i ≤ RingHom.ker f := by
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
      change f (i (1 - G.idempotent G.identityIndex)) = 0
      rw [map_sub i, map_one i, map_sub f, map_one f]
      change (1 : S ⊗[Q] S) -
        relativeTensorQuotient T G (T.chart (1 ⊗ₜ[k] G.idempotent G.identityIndex)) = 0
      rw [relativeTensorQuotient_identityIdempotent, sub_self]
    have h := hI (hker ▸ (show T.chart.symm x ∈ RingHom.ker (M (AlgHom.id S S) π) from hx))
    change f (T.chart.symm x) = 0 at h
    rw [AlgHom.comp_apply, AlgEquiv.coe_algHom, AlgEquiv.apply_symm_apply] at h
    exact h
  · have hπ : Function.Surjective (M (AlgHom.id S S) π) :=
      LinearMap.lTensor_surjective S G.identityQuotient_surjective
    have h := hπ.comp T.chart.symm.surjective
    change Function.Surjective ((M (AlgHom.id S S) π).comp T.chart.symm.toAlgHom) at h
    rw [← identityCanonical_comp] at h
    exact Function.Surjective.of_comp h

end Residual

end WideE
