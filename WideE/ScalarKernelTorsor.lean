import WideE.AdditiveTorsor
import WideE.ComponentFaithfulFlatness
import WideE.KummerCoordinates
import WideE.MultiplicativeTorsor
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-! The canonical map for a kernel action with a principal group relation. -/

noncomputable section

open scoped TensorProduct

namespace WideE

open StrictEUnit TensorProduct

attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule

set_option maxHeartbeats 650000
set_option synthInstance.maxHeartbeats 80000

section Restriction

variable {k B Q S H J : Type*}
  [CommRing k] [CommRing B] [CommRing Q] [CommRing S] [CommRing H] [CommRing J]
  [Algebra k B] [Algebra k Q] [Algebra k S]
  [Algebra B S] [Algebra B Q] [Algebra Q S]
  [IsScalarTower k B S] [IsScalarTower k Q S] [IsScalarTower B Q S]
  [HopfAlgebra k H] [Bialgebra k J]

local notation "M" => Algebra.TensorProduct.map

/-- Restrict the action along the specified quotient of the coordinate Hopf algebra. -/
def AffineHopfTorsor.kernelAction (T : AffineHopfTorsor k B S H) (π : H →ₐc[k] J) :
    S →ₐ[B] S ⊗[k] J :=
  (M (AlgHom.id B S) (π : H →ₐ[k] J)).comp T.coaction

/-- The restricted action satisfies coassociativity through the bialgebra projection. -/
theorem AffineHopfTorsor.kernelAction_coassociative (T : AffineHopfTorsor k B S H)
    (π : H →ₐc[k] J) (s : S) :
    Algebra.TensorProduct.assoc k S J J
      (M ((T.kernelAction π).restrictScalars k) (AlgHom.id k J) (T.kernelAction π s)) =
      M (AlgHom.id S S) (Bialgebra.comulAlgHom k J) (T.kernelAction π s) := by
  let p : H →ₐ[k] J := π
  let ρ := T.coaction.restrictScalars k
  let ρJ := (T.kernelAction π).restrictScalars k
  have hρ : ρJ = (M (AlgHom.id k S) p).comp ρ := AlgHom.ext fun _ => rfl
  have hΔ : (Bialgebra.comulAlgHom k J).comp p = (M p p).comp (Bialgebra.comulAlgHom k H) :=
    (BialgHomClass.map_comp_comulAlgHom π).symm
  have hAssoc : (Algebra.TensorProduct.assoc k S J J).toAlgHom.comp (M (M (AlgHom.id k S) p) p) =
      (M (AlgHom.id k S) (M p p)).comp (Algebra.TensorProduct.assoc k S H H).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro z a
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | tmul x h => rfl
  have hL : (M ρJ (AlgHom.id k J)).comp (M (AlgHom.id k S) p) =
      (M (M (AlgHom.id k S) p) p).comp (M ρ (AlgHom.id k H)) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id,
      AlgHom.id_comp, AlgHom.comp_id, hρ]
  have hR : (M (AlgHom.id k S) (Bialgebra.comulAlgHom k J)).comp (M (AlgHom.id k S) p) =
      (M (AlgHom.id k S) (M p p)).comp (M (AlgHom.id k S) (Bialgebra.comulAlgHom k H)) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp, hΔ]
  change Algebra.TensorProduct.assoc k S J J (M ρJ (AlgHom.id k J) (ρJ s)) =
    M (AlgHom.id k S) (Bialgebra.comulAlgHom k J) (ρJ s)
  rw [show ρJ s = M (AlgHom.id k S) p (ρ s) from AlgHom.congr_fun hρ s]
  change ((Algebra.TensorProduct.assoc k S J J).toAlgHom.comp
    ((M ρJ (AlgHom.id k J)).comp (M (AlgHom.id k S) p))) (ρ s) =
      ((M (AlgHom.id k S) (Bialgebra.comulAlgHom k J)).comp (M (AlgHom.id k S) p)) (ρ s)
  rw [hL, hR, ← AlgHom.comp_assoc, hAssoc, AlgHom.comp_assoc]
  exact congrArg (M (AlgHom.id k S) (M p p)) (T.coassociative s)

/-- The restricted action satisfies the counit identity. -/
theorem AffineHopfTorsor.kernelAction_counital (T : AffineHopfTorsor k B S H)
    (π : H →ₐc[k] J) (s : S) : coactionCounit (T.kernelAction π s) = s := by
  let p : H →ₐ[k] J := π
  have h : (coactionCounit (k := k) (S := S) (H := J)).comp (M (AlgHom.id k S) p) =
      coactionCounit (k := k) (S := S) (H := H) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    change a * algebraMap k S (Bialgebra.counitAlgHom k J (p b)) =
      a * algebraMap k S (Bialgebra.counitAlgHom k H b)
    rw [show Bialgebra.counitAlgHom k J (p b) = Bialgebra.counitAlgHom k H b from
      AlgHom.congr_fun (BialgHomClass.counitAlgHom_comp π) b]
  change ((coactionCounit (k := k) (S := S) (H := J)).comp (M (AlgHom.id k S) p)) (T.coaction s) = s
  rw [h]
  exact T.counital s

/-- The restricted action viewed over a base ring fixed by the kernel. -/
def AffineHopfTorsor.restrictCoactionOver (T : AffineHopfTorsor k B S H)
    (π : H →ₐc[k] J) (hfix : ∀ a : Q,
      T.kernelAction π (algebraMap Q S a) = algebraMap Q S a ⊗ₜ[k] (1 : J)) : S →ₐ[Q] S ⊗[k] J where
  toRingHom := (T.kernelAction π).toRingHom
  commutes' a := hfix a

/-- Change the tensor base from the original base to the fixed subalgebra. -/
def kernelRelativeTensor : S ⊗[B] S →ₐ[S] S ⊗[Q] S :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
    ((Algebra.TensorProduct.includeRight : S →ₐ[Q] S ⊗[Q] S).restrictScalars B)
    (fun _ _ => Commute.all _ _)

@[simp] theorem kernelRelativeTensor_tmul (s t : S) :
    kernelRelativeTensor (Q := Q) (s ⊗ₜ[B] t) = s ⊗ₜ[Q] t := by
  rw [kernelRelativeTensor, Algebra.TensorProduct.lift_tmul, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private theorem kernelRelativeTensor_surjective :
    Function.Surjective (kernelRelativeTensor (B := B) (Q := Q) (S := S)) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' + b', map_add _ _ _⟩
  | tmul s t => exact ⟨s ⊗ₜ[B] t, kernelRelativeTensor_tmul s t⟩

private def kernelCanonical (T : AffineHopfTorsor k B S H) (π : H →ₐc[k] J)
    (hfix : ∀ a : Q,
      T.kernelAction π (algebraMap Q S a) = algebraMap Q S a ⊗ₜ[k] (1 : J)) : S ⊗[Q] S →ₐ[S] S ⊗[k] J :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft (T.restrictCoactionOver π hfix)
    (fun _ _ => Commute.all _ _)

private theorem kernelCanonical_comp (T : AffineHopfTorsor k B S H) (π : H →ₐc[k] J)
    (hfix : ∀ a : Q,
      T.kernelAction π (algebraMap Q S a) = algebraMap Q S a ⊗ₜ[k] (1 : J)) :
    (kernelCanonical T π hfix).comp kernelRelativeTensor =
      (M (AlgHom.id S S) (π : H →ₐ[k] J)).comp T.chart.symm.toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro s t
  rw [AlgHom.comp_apply, kernelRelativeTensor_tmul, kernelCanonical,
    Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.includeLeft_apply, AlgHom.comp_apply,
    AlgEquiv.coe_algHom, T.chart_symm_apply, map_mul, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, map_one]
  rfl

/-- If translation sends the kernel relations to zero in the relative tensor,
the restricted coaction has a bijective canonical map. -/
theorem AffineHopfTorsor.kernel_canonical_bijective_of_kills
    (T : AffineHopfTorsor k B S H) (π : H →ₐc[k] J) (hπ : Function.Surjective π)
    (hfix : ∀ a : Q, T.kernelAction π (algebraMap Q S a) = algebraMap Q S a ⊗ₜ[k] (1 : J))
    (hkill : (RingHom.ker (π : H →ₐ[k] J)).map
        (Algebra.TensorProduct.includeRight : H →ₐ[k] S ⊗[k] H) ≤
      RingHom.ker ((kernelRelativeTensor (Q := Q)).comp T.chart.toAlgHom)) :
    Function.Bijective (relativeCandidateCanonical (T.restrictCoactionOver π hfix)) := by
  let r := kernelRelativeTensor (B := B) (Q := Q) (S := S)
  let c := kernelCanonical T π hfix
  have hrel := kernelCanonical_comp T π hfix
  have hkerMap : RingHom.ker (M (AlgHom.id S S) (π : H →ₐ[k] J)) =
      (RingHom.ker (π : H →ₐ[k] J)).map
        (Algebra.TensorProduct.includeRight : H →ₐ[k] S ⊗[k] H) := by
    change RingHom.ker (M (AlgHom.id k S) (π : H →ₐ[k] J)) = _
    exact Algebra.TensorProduct.lTensor_ker _ hπ
  change Function.Bijective c
  constructor
  · apply (RingHom.injective_iff_ker_eq_bot c.toRingHom).mpr
    refine le_antisymm (fun z hz => ?_) bot_le
    obtain ⟨y, rfl⟩ := kernelRelativeTensor_surjective (B := B) z
    have hy : T.chart.symm y ∈ RingHom.ker (M (AlgHom.id S S) (π : H →ₐ[k] J)) := by
      change M (AlgHom.id S S) (π : H →ₐ[k] J) (T.chart.symm y) = 0
      exact (AlgHom.congr_fun hrel y).symm.trans hz
    have h := hkill (hkerMap ▸ hy)
    change r (T.chart (T.chart.symm y)) = 0 at h
    rwa [AlgEquiv.apply_symm_apply] at h
  · have h : Function.Surjective ((M (AlgHom.id S S) (π : H →ₐ[k] J)).comp T.chart.symm.toAlgHom) :=
      (LinearMap.lTensor_surjective S hπ).comp T.chart.symm.surjective
    rw [← hrel] at h
    exact Function.Surjective.of_comp h

/-- A single balanced coordinate kills the principal kernel relation. The
canonical map for the restricted coaction then becomes bijective. -/
theorem AffineHopfTorsor.principalKernel_canonical_bijective (T : AffineHopfTorsor k B S H)
    (π : H →ₐc[k] J) (hπ : Function.Surjective π) (x : H)
    (hker : RingHom.ker (π : H →ₐ[k] J) = Ideal.span {x})
    (hfix : ∀ a : Q,
      T.kernelAction π (algebraMap Q S a) = algebraMap Q S a ⊗ₜ[k] (1 : J))
    (a : Q) (v : Sˣ)
    (hcoord : T.chart.symm ((1 : S) ⊗ₜ[B] algebraMap Q S a - algebraMap Q S a ⊗ₜ[B] (1 : S)) =
      (v : S) ⊗ₜ[k] x) :
    Function.Bijective (relativeCandidateCanonical (T.restrictCoactionOver π hfix)) := by
  let r := kernelRelativeTensor (B := B) (Q := Q) (S := S)
  let f := r.comp T.chart.toAlgHom
  let i : H →ₐ[k] S ⊗[k] H := Algebra.TensorProduct.includeRight
  have hbal : (1 : S) ⊗ₜ[Q] algebraMap Q S a = algebraMap Q S a ⊗ₜ[Q] (1 : S) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using (TensorProduct.smul_tmul a (1 : S) (1 : S)).symm
  have hzero : f ((v : S) ⊗ₜ[k] x) = 0 := by
    change r (T.chart ((v : S) ⊗ₜ[k] x)) = 0
    rw [← hcoord, AlgEquiv.apply_symm_apply, map_sub, kernelRelativeTensor_tmul,
      kernelRelativeTensor_tmul, hbal, sub_self]
  have hu : IsUnit (f ((v : S) ⊗ₜ[k] (1 : H))) :=
    (v.isUnit.map (Algebra.TensorProduct.includeLeft : S →ₐ[k] S ⊗[k] H)).map f
  have hx : f (i x) = 0 := by
    apply hu.mul_left_cancel
    change f ((v : S) ⊗ₜ[k] (1 : H)) * f ((1 : S) ⊗ₜ[k] x) = _
    rw [mul_zero, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    exact hzero
  apply T.kernel_canonical_bijective_of_kills π hπ hfix
  change (RingHom.ker (π : H →ₐ[k] J)).map i ≤ RingHom.ker f
  rw [hker, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
  exact hx

end Restriction

section ScalarBase

variable {k B S H J A : Type*}
  [CommRing k] [CommRing B] [CommRing S] [CommRing H] [CommRing J] [CommRing A]
  [Algebra k B] [Algebra k S] [Algebra k A] [Algebra B S] [IsScalarTower k B S]
  [HopfAlgebra k H] [Bialgebra k J]

/-- Extend a scalar coordinate on the group quotient to the torsor base. -/
def kernelScalarBaseMap (γ : A →ₐ[k] S) : B ⊗[k] A →ₐ[B] S :=
  Algebra.TensorProduct.lift (Algebra.ofId B S) γ (fun _ _ => Commute.all _ _)

@[simp] theorem kernelScalarBaseMap_tmul (γ : A →ₐ[k] S) (b : B) (a : A) :
    kernelScalarBaseMap γ (b ⊗ₜ[k] a) = algebraMap B S b * γ a := rfl

/-- The actual kernel canonical map over the scalar quotient with its chosen coordinate. -/
def AffineHopfTorsor.HasScalarKernelChart (T : AffineHopfTorsor k B S H)
    (π : H →ₐc[k] J) (γ : A →ₐ[k] S) : Prop :=
  let Q := B ⊗[k] A
  let f := kernelScalarBaseMap (B := B) γ
  letI : Algebra Q S := f.toRingHom.toAlgebra
  letI : IsScalarTower B Q S := IsScalarTower.of_algHom f
  letI : IsScalarTower k Q S := IsScalarTower.of_algHom (f.restrictScalars k)
  ∃ hfix : ∀ a : Q, T.kernelAction π (algebraMap Q S a) = algebraMap Q S a ⊗ₜ[k] (1 : J),
    Function.Bijective (relativeCandidateCanonical (T.restrictCoactionOver π hfix))

private theorem scalarKernelChart_of_coordinate (T : AffineHopfTorsor k B S H)
    (π : H →ₐc[k] J) (hπ : Function.Surjective π) (γ : A →ₐ[k] S)
    (hγ : ∀ a, T.kernelAction π (γ a) = γ a ⊗ₜ[k] (1 : J))
    (x : H) (hker : RingHom.ker (π : H →ₐ[k] J) = Ideal.span {x}) (a : A) (v : Sˣ)
    (ha : T.chart.symm ((1 : S) ⊗ₜ[B] γ a - γ a ⊗ₜ[B] (1 : S)) = (v : S) ⊗ₜ[k] x) :
    T.HasScalarKernelChart π γ := by
  let Q := B ⊗[k] A
  let f := kernelScalarBaseMap (B := B) γ
  letI : Algebra Q S := f.toRingHom.toAlgebra
  letI : IsScalarTower B Q S := IsScalarTower.of_algHom f
  letI : IsScalarTower k Q S := IsScalarTower.of_algHom (f.restrictScalars k)
  have hfix (z : Q) : T.kernelAction π (f z) = f z ⊗ₜ[k] (1 : J) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add b c hb hc => simp only [map_add, hb, hc, TensorProduct.add_tmul]
    | tmul b c =>
      rw [show f (b ⊗ₜ[k] c) = algebraMap B S b * γ c from kernelScalarBaseMap_tmul γ b c,
        map_mul, hγ, AlgHom.commutes]
      change (algebraMap B S b ⊗ₜ[k] (1 : J)) * (γ c ⊗ₜ[k] (1 : J)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have hcoord : algebraMap Q S ((1 : B) ⊗ₜ[k] a) = γ a := by
    change f ((1 : B) ⊗ₜ[k] a) = γ a
    rw [kernelScalarBaseMap_tmul, map_one, one_mul]
  refine ⟨hfix, T.principalKernel_canonical_bijective π hπ x hker hfix ((1 : B) ⊗ₜ[k] a) v ?_⟩
  simpa only [hcoord] using ha

end ScalarBase

section AssembleKernel

variable {k B S H J A : Type*}
  [CommRing k] [CommRing B] [CommRing S] [CommRing H] [CommRing J] [CommRing A]
  [Algebra k B] [Algebra k S] [Algebra k A] [Algebra B S] [IsScalarTower k B S]
  [HopfAlgebra k H] [HopfAlgebra k J]

/-- The checked canonical chart and faithful flatness give the actual kernel torsor. -/
def AffineHopfTorsor.scalarKernelTorsorOfFlat (T : AffineHopfTorsor k B S H)
    (π : H →ₐc[k] J) (hπ : Function.Surjective π) (γ : A →ₐ[k] S)
    (hchart : T.HasScalarKernelChart π γ)
    (hflat : letI : Algebra (B ⊗[k] A) S := (kernelScalarBaseMap (B := B) γ).toRingHom.toAlgebra
      Module.FaithfullyFlat (B ⊗[k] A) S) :
    let Q := B ⊗[k] A
    let f := kernelScalarBaseMap (B := B) γ
    letI : Algebra Q S := f.toRingHom.toAlgebra
    letI : IsScalarTower k Q S := IsScalarTower.of_algHom (f.restrictScalars k)
    AffineHopfTorsor k Q S J := by
  let Q := B ⊗[k] A
  let f := kernelScalarBaseMap (B := B) γ
  letI : Algebra Q S := f.toRingHom.toAlgebra
  letI : IsScalarTower B Q S := IsScalarTower.of_algHom f
  letI : IsScalarTower k Q S := IsScalarTower.of_algHom (f.restrictScalars k)
  change ∃ hfix : ∀ a : Q, T.kernelAction π (algebraMap Q S a) = algebraMap Q S a ⊗ₜ[k] (1 : J),
    Function.Bijective (relativeCandidateCanonical (T.restrictCoactionOver π hfix)) at hchart
  refine ⟨T.restrictCoactionOver π hchart.choose, ?_, ?_, hchart.choose_spec, hflat, ?_⟩
  · exact T.kernelAction_coassociative π
  · exact T.kernelAction_counital π
  · exact Algebra.FiniteType.of_surjective T.group_finiteType (π : H →ₐ[k] J) hπ

end AssembleKernel

section FaithfulFlatness

attribute [local instance] TensorProduct.leftModule

private theorem faithfullyFlat_of_ringSquare {R R' V V' : Type*}
    [CommRing R] [CommRing R'] [CommRing V] [CommRing V'] [Algebra R V] [Algebra R' V']
    (e : R ≃+* R') (f : V ≃+* V')
    (h : ∀ x : R, f (algebraMap R V x) = algebraMap R' V' (e x))
    [Module.FaithfullyFlat R' V'] : Module.FaithfullyFlat R V := by
  letI : Algebra R R' := e.toRingHom.toAlgebra
  letI : Algebra R V' := ((algebraMap R' V').comp e.toRingHom).toAlgebra
  letI : IsScalarTower R R' V' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let eb : R ≃ₗ[R] R' :=
    { e.toAddEquiv with
      map_smul' := fun x y => by
        change e (x * y) = e x * e y
        exact map_mul e x y }
  letI : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_linearEquiv R R eb.symm
  letI : Module.FaithfullyFlat R V' := Module.FaithfullyFlat.trans R R' V'
  let fv : V ≃ₗ[R] V' :=
    { f.toAddEquiv with
      map_smul' := fun x y => by
        change f (x • y) = x • f y
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        exact congrArg (· * f y) (h x) }
  exact Module.FaithfullyFlat.of_linearEquiv R V' fv

private def scalarSwapCancel (R P S V : Type*) [CommRing R] [CommRing P] [CommRing S] [CommRing V]
    [Algebra R P] [Algebra R S] [Algebra R V] [Algebra P V] [IsScalarTower R P V] :
    ((P ⊗[R] S) ⊗[P] V) ≃ₐ[R] S ⊗[R] V :=
  ((Algebra.TensorProduct.comm P (P ⊗[R] S) V).restrictScalars R).trans
    (((Algebra.TensorProduct.cancelBaseChange R P P V S).restrictScalars R).trans
      (Algebra.TensorProduct.comm R V S))

private theorem scalarSwapCancel_algebraMap (R P S V : Type*)
    [CommRing R] [CommRing P] [CommRing S] [CommRing V]
    [Algebra R P] [Algebra R S] [Algebra R V] [Algebra P V] [IsScalarTower R P V] (z : P ⊗[R] S) :
    scalarSwapCancel R P S V (algebraMap (P ⊗[R] S) ((P ⊗[R] S) ⊗[P] V) z) =
      Algebra.TensorProduct.map (AlgHom.id R S) (IsScalarTower.toAlgHom R P V)
        (Algebra.TensorProduct.comm R P S z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul p s =>
    change scalarSwapCancel R P S V ((p ⊗ₜ[R] s) ⊗ₜ[P] (1 : V)) = _
    simp only [scalarSwapCancel, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
      Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.cancelBaseChange_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.smul_def, mul_one]
    rfl

variable {k B S H A : Type*}
  [CommRing k] [CommRing B] [CommRing S] [CommRing H] [CommRing A]
  [Algebra k B] [Algebra k S] [Algebra k A] [Algebra B S] [IsScalarTower k B S] [HopfAlgebra k H]

local notation "M" => Algebra.TensorProduct.map

private theorem scalarKernel_baseChange_chart (T : AffineHopfTorsor k B S H) (j : A →ₐ[k] H)
    (γ : A →ₐ[k] S) (τ : S ⊗[k] A ≃ₐ[S] S ⊗[k] A)
    (hcoord : ∀ a : A, T.coaction (γ a) = M (AlgHom.id S S) j (τ ((1 : S) ⊗ₜ[k] a)))
    (z : S ⊗[B] (B ⊗[k] A)) :
    T.chart.symm (M (AlgHom.id S S) (kernelScalarBaseMap γ) z) =
      M (AlgHom.id S S) j (τ (Algebra.TensorProduct.cancelBaseChange k B S S A z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s q =>
    induction q using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
    | tmul b a =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, kernelScalarBaseMap_tmul, T.chart_symm_apply,
        map_mul, T.coaction.commutes, hcoord, Algebra.TensorProduct.cancelBaseChange_tmul]
      have h' : τ ((b • s) ⊗ₜ[k] (1 : A)) = (b • s) ⊗ₜ[k] (1 : A) := τ.commutes (b • s)
      have h : τ ((b • s) ⊗ₜ[k] a) = ((b • s) ⊗ₜ[k] (1 : A)) * τ ((1 : S) ⊗ₜ[k] a) := by
        rw [← h', ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [h, map_mul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
      change (s ⊗ₜ[k] (1 : H)) * ((algebraMap B S b ⊗ₜ[k] (1 : H)) *
        M (AlgHom.id S S) j (τ ((1 : S) ⊗ₜ[k] a))) = _
      rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def,
        mul_comm s (algebraMap B S b)]

set_option maxHeartbeats 2100000 in
/-- Faithful flatness of the group projection descends along the torsor chart
when the quotient coordinate identifies the pullback with a translate. -/
theorem kernelScalarBaseMap_faithfullyFlat_of_translation (T : AffineHopfTorsor k B S H)
    (j : A →ₐ[k] H) (hj : letI : Algebra A H := j.toRingHom.toAlgebra; Module.FaithfullyFlat A H)
    (γ : A →ₐ[k] S) (τ : S ⊗[k] A ≃ₐ[S] S ⊗[k] A)
    (hcoord : ∀ a : A, T.coaction (γ a) = M (AlgHom.id S S) j (τ ((1 : S) ⊗ₜ[k] a))) :
    letI : Algebra (B ⊗[k] A) S := (kernelScalarBaseMap (B := B) γ).toRingHom.toAlgebra
    Module.FaithfullyFlat (B ⊗[k] A) S := by
  let Q := B ⊗[k] A
  let v := kernelScalarBaseMap (B := B) γ
  letI : Algebra Q S := v.toRingHom.toAlgebra
  letI : IsScalarTower B Q S := IsScalarTower.of_algHom v
  letI : Algebra A H := j.toRingHom.toAlgebra
  letI : IsScalarTower k A H := IsScalarTower.of_algHom j
  letI : Module.FaithfullyFlat A H := hj
  letI : Module.FaithfullyFlat B S := T.faithfullyFlat
  let R := Q ⊗[B] S
  let R' := A ⊗[k] S
  let V := R ⊗[Q] S
  let V' := R' ⊗[A] H
  let eQ := (Algebra.TensorProduct.cancelBaseChange k B S S A).trans τ
  let e : R ≃+* R' := ((Algebra.TensorProduct.comm B Q S).toRingEquiv.trans eQ.toRingEquiv).trans
    (Algebra.TensorProduct.comm k S A).toRingEquiv
  let f : V ≃+* V' := (((scalarSwapCancel B Q S S).toRingEquiv.trans T.chart.symm.toRingEquiv).trans
    (scalarSwapCancel k A S H).symm.toRingEquiv)
  have he (z : R) : Algebra.TensorProduct.comm k A S (e z) =
      eQ (Algebra.TensorProduct.comm B Q S z) := by
    change Algebra.TensorProduct.comm k A S
      (Algebra.TensorProduct.comm k S A (eQ (Algebra.TensorProduct.comm B Q S z))) = _
    exact (Algebra.TensorProduct.comm k A S).apply_symm_apply _
  have h (z : R) : f (algebraMap R V z) = algebraMap R' V' (e z) := by
    apply (scalarSwapCancel k A S H).injective
    change scalarSwapCancel k A S H ((scalarSwapCancel k A S H).symm
      (T.chart.symm (scalarSwapCancel B Q S S (algebraMap R V z)))) = _
    rw [AlgEquiv.apply_symm_apply, scalarSwapCancel_algebraMap, scalarSwapCancel_algebraMap, he]
    exact scalarKernel_baseChange_chart T j γ τ hcoord (Algebra.TensorProduct.comm B Q S z)
  letI : Module.FaithfullyFlat R' V' :=
    inferInstanceAs (Module.FaithfullyFlat (A ⊗[k] S) ((A ⊗[k] S) ⊗[A] H))
  letI : Module.FaithfullyFlat R V :=
    faithfullyFlat_of_ringSquare (R := R) (R' := R') (V := V) (V' := V') e f h
  letI : Module.FaithfullyFlat Q R := inferInstanceAs (Module.FaithfullyFlat Q (Q ⊗[B] S))
  exact faithfullyFlat_of_faithfullyFlat_tensor Q R S

end FaithfulFlatness

section Elementary

variable {k B S H J : Type*}
  [Field k] [CommRing B] [CommRing S] [CommRing H] [CommRing J]
  [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S]
  [HopfAlgebra k H] [Bialgebra k J]

local notation "M" => Algebra.TensorProduct.map

private theorem projection_kills_generator (π : H →ₐc[k] J) {x : H}
    (hker : RingHom.ker (π : H →ₐ[k] J) = Ideal.span {x}) : (π : H →ₐ[k] J) x = 0 := by
  apply RingHom.mem_ker.mp
  rw [hker]
  exact Ideal.subset_span (Set.mem_singleton x)

/-- The additive quotient coordinate gives the canonical map over `B ⊗[k] Polynomial k`. -/
theorem AffineHopfTorsor.additiveKernel_chart (T : AffineHopfTorsor k B S H)
    (π : H →ₐc[k] J) (hπ : Function.Surjective π) (x : H)
    (hker : RingHom.ker (π : H →ₐ[k] J) = Ideal.span {x}) (s : S)
    (hs : T.coaction s = s ⊗ₜ[k] (1 : H) + (1 : S) ⊗ₜ[k] x) :
    T.HasScalarKernelChart π (Polynomial.aeval s : Polynomial k →ₐ[k] S) := by
  let γ : Polynomial k →ₐ[k] S := Polynomial.aeval s
  let i : S →ₐ[k] S ⊗[k] J := Algebra.TensorProduct.includeLeft
  have hHom : ((T.kernelAction π).restrictScalars k).comp γ = i.comp γ := by
    apply Polynomial.algHom_ext
    change T.kernelAction π (γ Polynomial.X) = γ Polynomial.X ⊗ₜ[k] (1 : J)
    rw [show γ Polynomial.X = s from Polynomial.aeval_X s]
    change M (AlgHom.id B S) (π : H →ₐ[k] J) (T.coaction s) = _
    rw [hs, map_add, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, AlgHom.id_apply, map_one, projection_kills_generator π hker, tmul_zero, add_zero]
  refine scalarKernelChart_of_coordinate T π hπ γ (fun a => DFunLike.congr_fun hHom a)
    x hker Polynomial.X 1 ?_
  rw [show γ Polynomial.X = s from Polynomial.aeval_X s, map_sub, T.chart_symm_apply,
    show T.chart.symm (s ⊗ₜ[B] (1 : S)) = s ⊗ₜ[k] (1 : H) from T.chart.symm.commutes s,
    ← Algebra.TensorProduct.one_def, one_mul, hs, add_sub_cancel_left, Units.val_one]

/-- Evaluation of the multiplicative scalar coordinate at a unit of the torsor algebra. -/
def laurentKernelCoordinate (u : Sˣ) : LaurentPolynomial k →ₐ[k] S where
  toRingHom := LaurentPolynomial.eval₂ (algebraMap k S) u
  commutes' a := LaurentPolynomial.eval₂_C _ _ a

@[simp] theorem laurentKernelCoordinate_T (u : Sˣ) :
    laurentKernelCoordinate (k := k) u (LaurentPolynomial.T 1) = u := by
  change LaurentPolynomial.eval₂ (algebraMap k S) u (LaurentPolynomial.T 1) = u
  rw [LaurentPolynomial.eval₂_T, zpow_one]

/-- The multiplicative quotient coordinate gives the canonical map over
`B ⊗[k] LaurentPolynomial k`. -/
theorem AffineHopfTorsor.multiplicativeKernel_chart (T : AffineHopfTorsor k B S H)
    (π : H →ₐc[k] J) (hπ : Function.Surjective π) (χ : Hˣ)
    (hker : RingHom.ker (π : H →ₐ[k] J) = Ideal.span {(χ : H) - 1}) (u : Sˣ)
    (hu : T.coaction (u : S) = (u : S) ⊗ₜ[k] (χ : H)) :
    T.HasScalarKernelChart π (laurentKernelCoordinate u) := by
  let γ := laurentKernelCoordinate (k := k) u
  let i : S →ₐ[k] S ⊗[k] J := Algebra.TensorProduct.includeLeft
  have hχ : (π : H →ₐ[k] J) (χ : H) = 1 := by
    have h := projection_kills_generator π hker
    rwa [map_sub, map_one, sub_eq_zero] at h
  have hHom : ((T.kernelAction π).restrictScalars k).comp γ = i.comp γ := by
    apply laurentAlgHom_ext
    change T.kernelAction π (γ (LaurentPolynomial.T 1)) = γ (LaurentPolynomial.T 1) ⊗ₜ[k] (1 : J)
    rw [show γ (LaurentPolynomial.T 1) = (u : S) from laurentKernelCoordinate_T u]
    change M (AlgHom.id B S) (π : H →ₐ[k] J) (T.coaction (u : S)) = _
    rw [hu, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hχ]
  refine scalarKernelChart_of_coordinate T π hπ γ (fun a => DFunLike.congr_fun hHom a)
    _ hker (LaurentPolynomial.T 1) u ?_
  rw [show γ (LaurentPolynomial.T 1) = (u : S) from laurentKernelCoordinate_T u,
    map_sub, T.chart_symm_apply,
    show T.chart.symm ((u : S) ⊗ₜ[B] (1 : S)) = (u : S) ⊗ₜ[k] (1 : H) from T.chart.symm.commutes u,
    ← Algebra.TensorProduct.one_def, one_mul, hu, tmul_sub]

/-- A primitive group coordinate supplies the additive quotient chart. -/
theorem AffineHopfTorsor.exists_additiveKernel_chart (T : AffineHopfTorsor k B S H)
    (π : H →ₐc[k] J) (hπ : Function.Surjective π) (x : H)
    (hker : RingHom.ker (π : H →ₐ[k] J) = Ideal.span {x})
    (hx : Bialgebra.comulAlgHom k H x = (1 : H) ⊗ₜ[k] x + x ⊗ₜ[k] (1 : H)) :
    ∃ s : S, T.coaction s = s ⊗ₜ[k] (1 : H) + (1 : S) ⊗ₜ[k] x ∧
      T.HasScalarKernelChart π (Polynomial.aeval s : Polynomial k →ₐ[k] S) := by
  obtain ⟨s, hs⟩ := exists_primitive_torsor_coordinate T x hx
  exact ⟨s, hs, T.additiveKernel_chart π hπ x hker s hs⟩

/-- Over a PID a grouplike unit supplies the multiplicative quotient chart. -/
theorem AffineHopfTorsor.exists_multiplicativeKernel_chart [IsDomain B] [IsPrincipalIdealRing B]
    (T : AffineHopfTorsor k B S H) (π : H →ₐc[k] J) (hπ : Function.Surjective π) (χ : Hˣ)
    (hker : RingHom.ker (π : H →ₐ[k] J) = Ideal.span {(χ : H) - 1})
    (hχ : Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H)) :
    ∃ u : Sˣ, T.coaction (u : S) = (u : S) ⊗ₜ[k] (χ : H) ∧
      T.HasScalarKernelChart π (laurentKernelCoordinate u) := by
  obtain ⟨u, hu⟩ := T.exists_grouplike_unit χ hχ
  exact ⟨u, hu, T.multiplicativeKernel_chart π hπ χ hker u hu⟩

end Elementary

section CoordinateTranslations

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S]

private def additiveScalarTranslation (s : S) :
    S ⊗[k] Polynomial k ≃ₐ[S] S ⊗[k] Polynomial k :=
  (polyEquivTensor' k S).symm.trans ((Polynomial.algEquivAevalXAddC s).trans (polyEquivTensor' k S))

private theorem additiveScalarTranslation_coordinate (s : S) :
    additiveScalarTranslation (k := k) s ((1 : S) ⊗ₜ[k] (Polynomial.X : Polynomial k)) =
      s ⊗ₜ[k] (1 : Polynomial k) + (1 : S) ⊗ₜ[k] (Polynomial.X : Polynomial k) := by
  let e := polyEquivTensor' k S
  let t := Polynomial.algEquivAevalXAddC s
  have hX : e Polynomial.X = (1 : S) ⊗ₜ[k] (Polynomial.X : Polynomial k) := by simp [e]
  have ht : t Polynomial.X = Polynomial.X + Polynomial.C s := by simp [t, Polynomial.algEquivAevalXAddC]
  have hC : e (Polynomial.C s) = s ⊗ₜ[k] (1 : Polynomial k) := e.commutes s
  calc
    _ = e (Polynomial.X + Polynomial.C s) := by
      rw [← hX]
      change e (t (e.symm (e Polynomial.X))) = _
      rw [AlgEquiv.symm_apply_apply, ht]
    _ = _ := by rw [map_add, hX, hC, add_comm]

local notation "L" => LaurentPolynomial k
local notation "D" => S ⊗[k] L

private def laurentScalarTranslationHom (u : Sˣ) : D →ₐ[S] D :=
  let t : Lˣ := (LaurentPolynomial.isUnit_T (R := k) 1).unit
  let l : S →ₐ[S] D := Algebra.ofId S D
  let r : L →ₐ[k] D := Algebra.TensorProduct.includeRight
  Algebra.TensorProduct.lift l
    (laurentKernelCoordinate (Units.map l.toMonoidHom u * Units.map r.toMonoidHom t))
    (fun _ _ => Commute.all _ _)

private theorem laurentScalarTranslationHom_tmul_T (u : Sˣ) (s : S) :
    laurentScalarTranslationHom (k := k) u (s ⊗ₜ[k] (LaurentPolynomial.T 1 : L)) =
      (s * (u : S)) ⊗ₜ[k] (LaurentPolynomial.T 1 : L) := by
  rw [laurentScalarTranslationHom, Algebra.TensorProduct.lift_tmul, laurentKernelCoordinate_T]
  let t : Lˣ := (LaurentPolynomial.isUnit_T (R := k) 1).unit
  change (s ⊗ₜ[k] (1 : L)) * (((u : S) ⊗ₜ[k] (1 : L)) * ((1 : S) ⊗ₜ[k] (t : L))) = _
  rw [show (t : L) = LaurentPolynomial.T 1 from (LaurentPolynomial.isUnit_T (R := k) 1).unit_spec]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private theorem laurentScalarTranslationHom_comp (u v : Sˣ) (h : v * u = 1) :
    (laurentScalarTranslationHom (k := k) u).comp (laurentScalarTranslationHom v) = AlgHom.id S D := by
  apply Algebra.TensorProduct.ext
  · exact AlgHom.ext (fun s => (AlgHom.commutes _ s).trans (AlgHom.commutes _ s).symm)
  · apply laurentAlgHom_ext
    change laurentScalarTranslationHom (k := k) u
      (laurentScalarTranslationHom v ((1 : S) ⊗ₜ[k] (LaurentPolynomial.T 1 : L))) =
        (1 : S) ⊗ₜ[k] (LaurentPolynomial.T 1 : L)
    rw [laurentScalarTranslationHom_tmul_T, one_mul, laurentScalarTranslationHom_tmul_T,
      show (v : S) * (u : S) = 1 from congrArg Units.val h]

private def laurentScalarTranslation (u : Sˣ) : D ≃ₐ[S] D :=
  AlgEquiv.ofAlgHom (laurentScalarTranslationHom u) (laurentScalarTranslationHom u⁻¹)
    (laurentScalarTranslationHom_comp u u⁻¹ (inv_mul_cancel u))
    (laurentScalarTranslationHom_comp u⁻¹ u (mul_inv_cancel u))

private theorem laurentScalarTranslation_coordinate (u : Sˣ) :
    laurentScalarTranslation (k := k) u ((1 : S) ⊗ₜ[k] (LaurentPolynomial.T 1 : L)) =
      (u : S) ⊗ₜ[k] (LaurentPolynomial.T 1 : L) := by
  change laurentScalarTranslationHom (k := k) u ((1 : S) ⊗ₜ[k] (LaurentPolynomial.T 1 : L)) = _
  rw [laurentScalarTranslationHom_tmul_T, one_mul]

end CoordinateTranslations

section ElementaryFaithfulFlatness

variable {k B S H : Type*} [Field k] [CommRing B] [CommRing S] [CommRing H]
  [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S] [HopfAlgebra k H]

local notation "M" => Algebra.TensorProduct.map

/-- The torsor algebra is faithfully flat over the translated additive quotient. -/
theorem AffineHopfTorsor.additiveKernel_faithfullyFlat (T : AffineHopfTorsor k B S H)
    (j : Polynomial k →ₐ[k] H)
    (hj : letI : Algebra (Polynomial k) H := j.toRingHom.toAlgebra; Module.FaithfullyFlat (Polynomial k) H)
    (s : S) (hs : T.coaction s = s ⊗ₜ[k] (1 : H) + (1 : S) ⊗ₜ[k] j Polynomial.X) :
    letI : Algebra (B ⊗[k] Polynomial k) S :=
      (kernelScalarBaseMap (B := B) (Polynomial.aeval s : Polynomial k →ₐ[k] S)).toRingHom.toAlgebra
    Module.FaithfullyFlat (B ⊗[k] Polynomial k) S := by
  let γ : Polynomial k →ₐ[k] S := Polynomial.aeval s
  let τ := additiveScalarTranslation (k := k) s
  let i : Polynomial k →ₐ[k] S ⊗[k] Polynomial k := Algebra.TensorProduct.includeRight
  let jS := M (AlgHom.id S S) j
  have h : (T.coaction.restrictScalars k).comp γ = ((jS.comp τ.toAlgHom).restrictScalars k).comp i := by
    apply Polynomial.algHom_ext
    change T.coaction (γ Polynomial.X) = jS (τ ((1 : S) ⊗ₜ[k] Polynomial.X))
    rw [show γ Polynomial.X = s from Polynomial.aeval_X s, hs, additiveScalarTranslation_coordinate]
    simp only [jS, map_add, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
  exact kernelScalarBaseMap_faithfullyFlat_of_translation T j hj γ τ (fun a => DFunLike.congr_fun h a)

/-- The torsor algebra is faithfully flat over the translated multiplicative quotient. -/
theorem AffineHopfTorsor.multiplicativeKernel_faithfullyFlat (T : AffineHopfTorsor k B S H)
    (j : LaurentPolynomial k →ₐ[k] H)
    (hj : letI : Algebra (LaurentPolynomial k) H := j.toRingHom.toAlgebra;
      Module.FaithfullyFlat (LaurentPolynomial k) H)
    (u : Sˣ) (hu : T.coaction (u : S) = (u : S) ⊗ₜ[k] j (LaurentPolynomial.T 1)) :
    letI : Algebra (B ⊗[k] LaurentPolynomial k) S :=
      (kernelScalarBaseMap (B := B) (laurentKernelCoordinate u)).toRingHom.toAlgebra
    Module.FaithfullyFlat (B ⊗[k] LaurentPolynomial k) S := by
  let γ := laurentKernelCoordinate (k := k) u
  let τ := laurentScalarTranslation (k := k) u
  let i : LaurentPolynomial k →ₐ[k] S ⊗[k] LaurentPolynomial k := Algebra.TensorProduct.includeRight
  let jS := M (AlgHom.id S S) j
  have h : (T.coaction.restrictScalars k).comp γ = ((jS.comp τ.toAlgHom).restrictScalars k).comp i := by
    apply laurentAlgHom_ext
    change T.coaction (γ (LaurentPolynomial.T 1)) = jS (τ ((1 : S) ⊗ₜ[k] LaurentPolynomial.T 1))
    rw [show γ (LaurentPolynomial.T 1) = (u : S) from laurentKernelCoordinate_T u, hu,
      laurentScalarTranslation_coordinate]
    simp only [jS, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  exact kernelScalarBaseMap_faithfullyFlat_of_translation T j hj γ τ (fun a => DFunLike.congr_fun h a)

end ElementaryFaithfulFlatness

section ElementaryKernelTorsors

variable {k B S H J : Type*}
  [Field k] [CommRing B] [CommRing S] [CommRing H] [CommRing J]
  [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S]
  [HopfAlgebra k H] [HopfAlgebra k J]

local instance : HopfAlgebra k (Polynomial k) := additivePolynomialHopf k

/-- An additive group quotient gives a kernel torsor over the polynomial
coordinate of the quotient of the original torsor. -/
theorem AffineHopfTorsor.exists_additiveKernelTorsor (T : AffineHopfTorsor k B S H)
    (j : Polynomial k →ₐc[k] H)
    (hj : letI : Algebra (Polynomial k) H := (j : Polynomial k →ₐ[k] H).toRingHom.toAlgebra
      Module.FaithfullyFlat (Polynomial k) H)
    (π : H →ₐc[k] J) (hπ : Function.Surjective π)
    (hker : RingHom.ker (π : H →ₐ[k] J) = Ideal.span {j Polynomial.X}) :
    ∃ s : S, T.coaction s = s ⊗ₜ[k] (1 : H) + (1 : S) ⊗ₜ[k] j Polynomial.X ∧
      (let Q := B ⊗[k] Polynomial k
       let f := kernelScalarBaseMap (B := B) (Polynomial.aeval s : Polynomial k →ₐ[k] S)
       letI : Algebra Q S := f.toRingHom.toAlgebra
       letI : IsScalarTower k Q S := IsScalarTower.of_algHom (f.restrictScalars k)
       ∃ U : AffineHopfTorsor k Q S J, ∀ z, U.coaction z = T.kernelAction π z) := by
  have hx : Bialgebra.comulAlgHom k H (j Polynomial.X) =
      (1 : H) ⊗ₜ[k] j Polynomial.X + j Polynomial.X ⊗ₜ[k] (1 : H) := by
    let g : Polynomial k →ₐ[k] H := j
    have h := DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom j) Polynomial.X
    change Algebra.TensorProduct.map g g (Bialgebra.comulAlgHom k (Polynomial k) Polynomial.X) =
      Bialgebra.comulAlgHom k H (j Polynomial.X) at h
    rw [additivePolynomialHopf_comul_X, map_add, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul, map_one g] at h
    exact h.symm
  obtain ⟨s, hs, hchart⟩ := T.exists_additiveKernel_chart π hπ (j Polynomial.X) hker hx
  have hflat := T.additiveKernel_faithfullyFlat (j : Polynomial k →ₐ[k] H) hj s hs
  exact ⟨s, hs, ⟨T.scalarKernelTorsorOfFlat π hπ (Polynomial.aeval s) hchart hflat, fun _ => rfl⟩⟩

/-- A multiplicative group quotient gives a kernel torsor over the Laurent
coordinate of the quotient of the original torsor over a PID. -/
theorem AffineHopfTorsor.exists_multiplicativeKernelTorsor [IsDomain B] [IsPrincipalIdealRing B]
    (T : AffineHopfTorsor k B S H) (j : LaurentPolynomial k →ₐc[k] H)
    (hj : letI : Algebra (LaurentPolynomial k) H := (j : LaurentPolynomial k →ₐ[k] H).toRingHom.toAlgebra
      Module.FaithfullyFlat (LaurentPolynomial k) H)
    (π : H →ₐc[k] J) (hπ : Function.Surjective π)
    (hker : RingHom.ker (π : H →ₐ[k] J) = Ideal.span {j (LaurentPolynomial.T 1) - 1}) :
    ∃ u : Sˣ, T.coaction (u : S) = (u : S) ⊗ₜ[k] j (LaurentPolynomial.T 1) ∧
      (let Q := B ⊗[k] LaurentPolynomial k
       let f := kernelScalarBaseMap (B := B) (laurentKernelCoordinate (k := k) u)
       letI : Algebra Q S := f.toRingHom.toAlgebra
       letI : IsScalarTower k Q S := IsScalarTower.of_algHom (f.restrictScalars k)
       ∃ U : AffineHopfTorsor k Q S J, ∀ z, U.coaction z = T.kernelAction π z) := by
  let g : LaurentPolynomial k →ₐ[k] H := j
  let t := (LaurentPolynomial.isUnit_T (R := k) 1).unit
  let χ := Units.map g.toMonoidHom t
  have hχ : (χ : H) = j (LaurentPolynomial.T 1) :=
    congrArg g (LaurentPolynomial.isUnit_T (R := k) 1).unit_spec
  have hΔ : Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H) := by
    rw [hχ]
    have h := DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom j) (LaurentPolynomial.T 1)
    change Algebra.TensorProduct.map g g (Coalgebra.comul (R := k) (LaurentPolynomial.T 1)) =
      Coalgebra.comul (R := k) (j (LaurentPolynomial.T 1)) at h
    rw [LaurentPolynomial.comul_T, Algebra.TensorProduct.map_tmul] at h
    exact h.symm
  have hker' : RingHom.ker (π : H →ₐ[k] J) = Ideal.span {(χ : H) - 1} := by simpa only [hχ] using hker
  obtain ⟨u, hu, hchart⟩ := T.exists_multiplicativeKernel_chart π hπ χ hker' hΔ
  have hu' : T.coaction (u : S) = (u : S) ⊗ₜ[k] j (LaurentPolynomial.T 1) := by
    simpa only [hχ] using hu
  have hflat := T.multiplicativeKernel_faithfullyFlat g hj u hu'
  exact ⟨u, hu', ⟨T.scalarKernelTorsorOfFlat π hπ (laurentKernelCoordinate u) hchart hflat, fun _ => rfl⟩⟩

end ElementaryKernelTorsors

end WideE
