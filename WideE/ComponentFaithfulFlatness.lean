import WideE.ComponentEtaleDescent
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Projection

/-! The original torsor algebra is faithfully flat over its component quotient. -/

noncomputable section

open scoped TensorProduct

namespace WideE

set_option maxHeartbeats 1050000
set_option synthInstance.maxHeartbeats 90000

private theorem flat_of_semisimple (R M : Type*) [CommRing R] [IsSemisimpleRing R]
    [AddCommGroup M] [Module R M] : Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro X Y _ _ _ _ f hf
  obtain ⟨q, hq⟩ := exists_isCompl (LinearMap.range f)
  let r := f.linearProjOfIsCompl q hf hq
  have h : Function.LeftInverse (r.lTensor M) (f.lTensor M) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul m x =>
      rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
      exact congrArg (m ⊗ₜ[R] ·) (LinearMap.linearProjOfIsCompl_apply_left q f hf hq x)
  exact h.injective

private theorem faithfullyFlat_of_split {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (r : S →ₐ[R] R) : Module.FaithfullyFlat R S := by
  rw [Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top]
  refine ⟨inferInstance, fun I h => ?_⟩
  rw [Ideal.smul_top_eq_map] at h
  have hm : I.map (algebraMap R S) = ⊤ :=
    (Submodule.restrictScalars_eq_top_iff _ _ _).mp h
  have h' := congrArg (Ideal.map r.toRingHom) hm
  rw [Ideal.map_map, Ideal.map_top,
    show r.toRingHom.comp (algebraMap R S) = RingHom.id R from
      RingHom.ext (fun x => r.commutes x), Ideal.map_id] at h'
  exact h'

private theorem faithfullyFlat_of_algebraSquare {R R' S S' : Type*}
    [CommRing R] [CommRing R'] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R' S']
    (e : R ≃+* R') (f : S ≃+* S')
    (h : ∀ x : R, f (algebraMap R S x) = algebraMap R' S' (e x))
    [Module.FaithfullyFlat R' S'] : Module.FaithfullyFlat R S := by
  letI : Algebra R R' := e.toRingHom.toAlgebra
  letI : Algebra R S' := ((algebraMap R' S').comp e.toRingHom).toAlgebra
  letI : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e' : R ≃ₗ[R] R' :=
    { e.toAddEquiv with
      map_smul' := fun x y => by
        change e (x * y) = e x * e y
        exact map_mul e x y }
  letI : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_linearEquiv R R e'.symm
  letI : Module.FaithfullyFlat R S' := Module.FaithfullyFlat.trans R R' S'
  let f' : S ≃ₗ[R] S' :=
    { f.toAddEquiv with
      map_smul' := fun r s => by
        change f (r • s) = r • f s
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        exact congrArg (· * f s) (h r) }
  exact Module.FaithfullyFlat.of_linearEquiv R S' f'

/-- Faithful flatness of an algebra can be checked after a faithfully flat
extension of its base. -/
theorem faithfullyFlat_of_faithfullyFlat_tensor (R A S : Type*)
    [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
    [Module.FaithfullyFlat R A] [Module.FaithfullyFlat A (A ⊗[R] S)] :
    Module.FaithfullyFlat R S := by
  rw [Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top]
  refine ⟨Module.Flat.of_flat_tensorProduct R S A, fun I h => ?_⟩
  rw [Ideal.smul_top_eq_map] at h
  have hm : I.map (algebraMap R S) = ⊤ :=
    (Submodule.restrictScalars_eq_top_iff _ _ _).mp h
  let i : S →ₐ[R] A ⊗[R] S := Algebra.TensorProduct.includeRight
  have hi : i.toRingHom.comp (algebraMap R S) = algebraMap R (A ⊗[R] S) :=
    RingHom.ext i.commutes
  have h₁ : I.map (algebraMap R (A ⊗[R] S)) = ⊤ := by
    rw [← hi, ← Ideal.map_map, hm, Ideal.map_top]
  have h₂ : (I.map (algebraMap R A)).map (algebraMap A (A ⊗[R] S)) = ⊤ := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R A (A ⊗[R] S), h₁]
  have h₃ := Ideal.comap_map_eq_self_of_faithfullyFlat
    (A := A) (B := A ⊗[R] S) (I.map (algebraMap R A))
  rw [h₂, Ideal.comap_top] at h₃
  have h₄ := Ideal.comap_map_eq_self_of_faithfullyFlat (A := R) (B := A) I
  rw [← h₃, Ideal.comap_top] at h₄
  exact h₄.symm

section Compare

variable (R P S V : Type*) [CommRing R] [CommRing P] [CommRing S] [CommRing V]
  [Algebra R P] [Algebra R S] [Algebra R V] [Algebra P V] [IsScalarTower R P V]

private def swapCancel : ((P ⊗[R] S) ⊗[P] V) ≃ₐ[R] S ⊗[R] V :=
  ((Algebra.TensorProduct.comm P (P ⊗[R] S) V).restrictScalars R).trans
    (((Algebra.TensorProduct.cancelBaseChange R P P V S).restrictScalars R).trans
      (Algebra.TensorProduct.comm R V S))

private theorem swapCancel_algebraMap (z : P ⊗[R] S) :
    swapCancel R P S V (algebraMap (P ⊗[R] S) ((P ⊗[R] S) ⊗[P] V) z) =
      Algebra.TensorProduct.map (AlgHom.id R S) (IsScalarTower.toAlgHom R P V)
        (Algebra.TensorProduct.comm R P S z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul p s =>
    change swapCancel R P S V ((p ⊗ₜ[R] s) ⊗ₜ[P] (1 : V)) = _
    simp only [swapCancel, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
      Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.cancelBaseChange_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.smul_def, mul_one]
    rfl

end Compare

universe u

section Components

variable {k B S H : Type u} [Field k] [IsAlgClosed k] [CommRing B] [CommRing S] [CommRing H]
  [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S] [HopfAlgebra k H]
  (T : AffineHopfTorsor k B S H) (G : ComponentHopfPresentation k H)

local notation "Q" => componentTorsorQuotient T G
local notation "J" => (G.Index → k)

set_option maxHeartbeats 6000000 in
/-- The map to the quotient is faithfully flat, as the quotient chart
identifies its pullback with the split inclusion of the component scalars. -/
theorem componentTorsorQuotient_faithfullyFlat : Module.FaithfullyFlat (↥Q) S := by
  letI := G.index_finite
  letI := T.group_finiteType
  letI := T.faithfullyFlat
  letI : Algebra J H := G.inclusion.toRingHom.toAlgebra
  letI : IsScalarTower k J H := IsScalarTower.of_algHom G.inclusion
  let r := componentPointRetraction (k := k) G.idempotent G.connected
  let rJ : H →ₐ[J] J :=
    { toRingHom := r.toRingHom
      commutes' f := componentPointRetraction_inclusion G.idempotent G.complete G.connected f }
  letI : Module.Flat J H := flat_of_semisimple J H
  letI : Module.FaithfullyFlat J H := faithfullyFlat_of_split rJ
  let R := (↥Q) ⊗[B] S
  let R' := J ⊗[k] S
  let A := R ⊗[Q] S
  let A' := R' ⊗[J] H
  let e : R ≃+* R' := ((Algebra.TensorProduct.comm B (↥Q) S).toRingEquiv.trans
    (componentTorsorQuotientChart T G).toRingEquiv).trans (Algebra.TensorProduct.comm k S J).toRingEquiv
  let f : A ≃+* A' := (((swapCancel B (↥Q) S S).toRingEquiv.trans
    T.chart.symm.toRingEquiv).trans (swapCancel k J S H).symm.toRingEquiv)
  have he (z : R) : Algebra.TensorProduct.comm k J S (e z) =
      componentTorsorQuotientChart T G (Algebra.TensorProduct.comm B (↥Q) S z) := by
    change Algebra.TensorProduct.comm k J S
      (Algebra.TensorProduct.comm k S J
        (componentTorsorQuotientChart T G (Algebra.TensorProduct.comm B (↥Q) S z))) = _
    exact (Algebra.TensorProduct.comm k J S).apply_symm_apply _
  have h (z : R) : f (algebraMap R A z) = algebraMap R' A' (e z) := by
    apply (swapCancel k J S H).injective
    change (swapCancel k J S H) ((swapCancel k J S H).symm
      (T.chart.symm (swapCancel B (↥Q) S S (algebraMap R A z)))) = _
    rw [AlgEquiv.apply_symm_apply, swapCancel_algebraMap, swapCancel_algebraMap, he]
    exact (componentTorsorQuotientChart_inclusion T G _).symm
  letI : Module.FaithfullyFlat R' A' :=
    inferInstanceAs (Module.FaithfullyFlat (J ⊗[k] S) ((J ⊗[k] S) ⊗[J] H))
  letI : Module.FaithfullyFlat R A :=
    faithfullyFlat_of_algebraSquare (R := R) (R' := R') (S := A) (S' := A') e f h
  letI : Module.FaithfullyFlat (↥Q) R :=
    inferInstanceAs (Module.FaithfullyFlat (↥Q) ((↥Q) ⊗[B] S))
  exact faithfullyFlat_of_faithfullyFlat_tensor (↥Q) R S

end Components

end WideE
