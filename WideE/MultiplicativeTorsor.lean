import WideE.PVTorsor
import MixedCoactionLaws
import CanonicalTorsorUnitLift
import BialgebraBaseChangeLaws
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-! Triviality of affine torsors under the constant multiplicative group over a PID. -/

noncomputable section

open scoped TensorProduct
open TensorProduct

namespace WideE

open StrictEUnit

attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule

set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 50000

section Pairing

variable {B S : Type*} [CommRing B] [IsDomain B] [IsPrincipalIdealRing B]
  [CommRing S] [Algebra B S] [Module.Flat B S]

omit [IsPrincipalIdealRing B] in
private theorem flat_scalar_mul_injective {b : B} (hb : b ≠ 0) :
    Function.Injective (fun x : S => algebraMap B S b * x) := by
  let f : B →ₗ[B] B := LinearMap.mulRight B b
  have hf : Function.Injective f := fun _ _ h => mul_right_cancel₀ hb h
  have ht := Module.Flat.lTensor_preserves_injective_linearMap (M := S) f hf
  intro x y hxy
  have h : (f.lTensor S) (x ⊗ₜ[B] (1 : B)) = (f.lTensor S) (y ⊗ₜ[B] (1 : B)) := by
    apply (TensorProduct.rid B S).injective
    simpa only [LinearMap.lTensor_tmul, f, LinearMap.mulRight_apply, one_mul,
      TensorProduct.rid_tmul, Algebra.smul_def] using hxy
  simpa only [TensorProduct.rid_tmul, one_smul] using congrArg (TensorProduct.rid B S) (ht h)

/-- Multiplication with a fixed opposite weight embeds the first weight module
in a principal ideal. Surjectivity of the pairing gives its generator an inverse. -/
private theorem pid_unit_of_pairing (M N : Submodule B S) (μ : M ⊗[B] N →ₗ[B] B)
    (hμ : Function.Surjective μ)
    (hprod : ∀ (x : M) (y : N), algebraMap B S (μ (x ⊗ₜ[B] y)) = (x : S) * (y : S)) :
    ∃ u : Sˣ, (u : S) ∈ M := by
  obtain ⟨m, n, hmn⟩ := exists_nonzero_pure_pairing M N μ hμ
  let f : M →ₗ[B] B := μ.comp ((TensorProduct.mk B M N).flip n)
  have hf : Function.Injective f := by
    intro x y hxy
    have h := congrArg (algebraMap B S) hxy
    change algebraMap B S (μ (x ⊗ₜ[B] n)) = algebraMap B S (μ (y ⊗ₜ[B] n)) at h
    rw [hprod, hprod] at h
    apply Subtype.ext
    apply (flat_scalar_mul_injective (S := S) hmn)
    rw [hprod]
    calc
      (m : S) * (n : S) * (x : S) = (m : S) * ((x : S) * (n : S)) := by ac_rfl
      _ = (m : S) * ((y : S) * (n : S)) := congrArg ((m : S) * ·) h
      _ = (m : S) * (n : S) * (y : S) := by ac_rfl
  let I : Ideal B := LinearMap.range f
  obtain ⟨b, hb⟩ := (Submodule.isPrincipal_iff I).mp (inferInstance : I.IsPrincipal)
  have hbI : b ∈ I := by
    rw [hb]
    exact Submodule.mem_span_singleton_self b
  obtain ⟨v, hv⟩ := hbI
  have hgen (x : M) : ∃ a : B, x = a • v := by
    have hx : f x ∈ I := LinearMap.mem_range_self f x
    rw [hb] at hx
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
    refine ⟨a, hf ?_⟩
    rw [map_smul, hv]
    exact ha.symm
  obtain ⟨w, hw⟩ := pairing_attains_at_generator μ v hgen hμ 1
  have hmul : (v : S) * (w : S) = 1 := by
    rw [← hprod, hw, map_one]
  exact ⟨⟨v, w, hmul, (mul_comm _ _).trans hmul⟩, v.property⟩

end Pairing

section Canonical

variable {B S J : Type*} [CommRing B] [IsDomain B] [IsPrincipalIdealRing B]
  [CommRing S] [CommRing J] [Algebra B S] [Bialgebra B J] [Module.FaithfullyFlat B S]

/-- On a canonical torsor over a PID, any grouplike unit is realized by a
unit of that weight in the torsor algebra. -/
private theorem canonical_grouplike_unit (ρ : S →ₐ[B] S ⊗[B] J)
    (hcan : Function.Bijective (torsorCanonical ρ))
    (hcoassoc : ∀ s : S, Algebra.TensorProduct.assoc B S J J
      (Algebra.TensorProduct.map ρ (AlgHom.id B J) (ρ s)) =
      weightBaseChangeAlgHom S (Bialgebra.comulAlgHom B J) (ρ s))
    (χ : Jˣ) (hχ : Coalgebra.comul (R := B) (χ : J) = (χ : J) ⊗ₜ[B] (χ : J)) :
    ∃ u : Sˣ, ρ (u : S) = (u : S) ⊗ₜ[B] (χ : J) := by
  let ι : S →ₐ[B] S ⊗[B] J := Algebra.TensorProduct.includeLeft
  let ψ := extendedUnit (k := B) S χ
  let e := torsorCanonicalEquiv ρ hcan
  let E := torsorTargetChart e
  have heρ := torsorCanonicalEquiv_coaction ρ hcan hcoassoc
  have heι := torsorTargetChart_includeLeft e
  have hinjS := chart_base_injective e (extended_regular_base_injective (H := J) S)
  have hfixedS := chart_invariants_are_scalars e E _ _ _ _ heρ heι
    (extended_regular_invariants_are_scalars (H := J) S)
  have hinj := scalar_inclusion_injective_descends S ρ ι hinjS
  have hfixed := invariant_image_descends S ρ ι hfixedS
  have hunit : ∃ u : (S ⊗[B] S)ˣ, (u : S ⊗[B] S) ∈
      weightSpace (weightBaseChangeAlgHom S ρ) (weightBaseChangeAlgHom S ι)
        ((1 : S) ⊗ₜ[B] (ψ : S ⊗[B] J)) := by
    apply chart_weighted_unit e E _ _ _ _ heρ heι _ (extendedUnit (k := B) S χ)
    change (extendedUnit (k := B) S χ : S ⊗[B] J) ∈ weightSpace _ _
      (torsorTargetChart e ((1 : S) ⊗ₜ[B] ((1 : S) ⊗ₜ[B] (χ : J))))
    rw [torsorTargetChart_multiplier]
    exact extended_regular_unit_weight S χ hχ
  let ρS := weightBaseChangeAlgHom S ρ
  let ιS := weightBaseChangeAlgHom S ι
  let ψS := extendedUnit (k := B) S ψ
  let ν := scalarWeightPairing ρS ιS ψS hinjS hfixedS
  obtain ⟨u, hu⟩ := hunit
  let x : weightSpace ρS ιS (ψS : S ⊗[B] (S ⊗[B] J)) := ⟨u, hu⟩
  let y : weightSpace ρS ιS (↑ψS⁻¹ : S ⊗[B] (S ⊗[B] J)) :=
    ⟨↑u⁻¹, inverse_unit_opposite_weight ρS ιS ψS u hu⟩
  have hone : ν (x ⊗ₜ[S] y) = 1 := by
    apply hinjS
    rw [scalarWeightPairing_tmul, map_one]
    exact Units.mul_inv u
  have hν : Function.Surjective ν := by
    intro s
    exact ⟨s • (x ⊗ₜ[S] y), by rw [map_smul, hone, smul_eq_mul, mul_one]⟩
  let μ := scalarWeightPairing ρ ι ψ hinj hfixed
  have hμ : Function.Surjective μ := pairing_surjective_of_faithfully_flat S μ
    (scalarWeightPairing_lTensor_surjective_of_extended_pairing S ρ ι ψ hinj hfixed ν
      (scalarWeightPairing_tmul ρS ιS ψS hinjS hfixedS) hν)
  obtain ⟨v, hv⟩ := pid_unit_of_pairing _ _ μ hμ (scalarWeightPairing_tmul ρ ι ψ hinj hfixed)
  refine ⟨v, ?_⟩
  change ρ (v : S) = ((v : S) ⊗ₜ[B] (1 : J)) * ((1 : S) ⊗ₜ[B] (χ : J)) at hv
  simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using hv

end Canonical

section ConstantGroup

variable {k B S H : Type*} [CommRing k] [CommRing B] [CommRing S] [CommRing H]
  [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S] [HopfAlgebra k H]
  [IsDomain B] [IsPrincipalIdealRing B]

/-- A character of the constant Hopf group is realized by a unit of the torsor algebra. -/
theorem AffineHopfTorsor.exists_grouplike_unit (T : AffineHopfTorsor k B S H)
    (χ : Hˣ) (hχ : Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H)) :
    ∃ u : Sˣ, T.coaction (u : S) = (u : S) ⊗ₜ[k] (χ : H) := by
  letI := T.faithfullyFlat
  letI := baseChangeBialgebra (k := k) (H := H) B
  obtain ⟨u, hu⟩ := canonical_grouplike_unit (scalarTargetCoaction T.coaction)
    (scalarTargetCoaction_canonical_bijective T.coaction T.canonical_bijective)
    (scalarTargetCoaction_coassoc T.coaction T.coassociative)
    (extendedUnit (k := k) B χ) (baseChange_grouplike_unit B χ hχ)
  let e := Algebra.TensorProduct.cancelBaseChange k B B S H
  have h := congrArg e hu
  change e (e.symm (T.coaction (u : S))) = e ((u : S) ⊗ₜ[B] ((1 : B) ⊗ₜ[k] (χ : H))) at h
  rw [AlgEquiv.apply_symm_apply, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul] at h
  exact ⟨u, h⟩

end ConstantGroup

section LaurentCoordinate

open LaurentPolynomial

private def coordinateUnit (k : Type*) [CommRing k] : (LaurentPolynomial k)ˣ :=
  (isUnit_T (R := k) 1).unit

@[simp] private theorem coordinateUnit_val (k : Type*) [CommRing k] :
    (coordinateUnit k : LaurentPolynomial k) = T 1 := (isUnit_T (R := k) 1).unit_spec

variable {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]

private def evalLaurentUnit (u : Sˣ) : LaurentPolynomial k →ₐ[k] S where
  toRingHom := LaurentPolynomial.eval₂ (algebraMap k S) u
  commutes' c := LaurentPolynomial.eval₂_C (algebraMap k S) u c

@[simp] private theorem evalLaurentUnit_T (u : Sˣ) : evalLaurentUnit (k := k) u (T 1) = u := by
  change LaurentPolynomial.eval₂ (algebraMap k S) u (T 1) = u
  rw [LaurentPolynomial.eval₂_T, zpow_one]

private theorem laurentAlgHom_ext_T (f g : LaurentPolynomial k →ₐ[k] S)
    (h : f (T 1) = g (T 1)) : f = g := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial k))
  apply Polynomial.ringHom_ext
  · intro c
    simpa only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      Polynomial.toLaurent_C] using (f.commutes c).trans (g.commutes c).symm
  · simpa only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      Polynomial.toLaurent_X] using h

local notation "D" => S ⊗[k] LaurentPolynomial k

private theorem tensorLaurent_ext (f g : D →ₐ[S] D)
    (h : f ((1 : S) ⊗ₜ[k] (T 1 : LaurentPolynomial k)) =
      g ((1 : S) ⊗ₜ[k] (T 1 : LaurentPolynomial k))) : f = g := by
  apply Algebra.TensorProduct.ext
  · exact AlgHom.ext (fun s => (f.commutes s).trans (g.commutes s).symm)
  · exact laurentAlgHom_ext_T _ _ h

private def scaleCoordinate (u : Sˣ) : D →ₐ[S] D :=
  Algebra.TensorProduct.lift (Algebra.ofId S D)
    (evalLaurentUnit (Units.map (Algebra.ofId S D).toMonoidHom u *
      extendedUnit (k := k) S (coordinateUnit k))) (fun _ _ => Commute.all _ _)

@[simp] private theorem scaleCoordinate_tmul_T (u : Sˣ) (s : S) :
    scaleCoordinate (k := k) u (s ⊗ₜ[k] (T 1 : LaurentPolynomial k)) =
      (s * (u : S)) ⊗ₜ[k] (T 1 : LaurentPolynomial k) := by
  rw [scaleCoordinate, Algebra.TensorProduct.lift_tmul, evalLaurentUnit_T]
  change (s ⊗ₜ[k] (1 : LaurentPolynomial k)) *
    (((u : S) ⊗ₜ[k] (1 : LaurentPolynomial k)) * ((1 : S) ⊗ₜ[k] (coordinateUnit k : LaurentPolynomial k))) = _
  rw [coordinateUnit_val]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private theorem scaleCoordinate_comp (u v : Sˣ) (h : v * u = 1) :
    (scaleCoordinate (k := k) u).comp (scaleCoordinate (k := k) v) = AlgHom.id S D := by
  apply tensorLaurent_ext
  rw [AlgHom.comp_apply, scaleCoordinate_tmul_T, scaleCoordinate_tmul_T, one_mul, AlgHom.id_apply]
  rw [show (v : S) * (u : S) = 1 from congrArg Units.val h]

private def scaleCoordinateEquiv (u : Sˣ) : D ≃ₐ[S] D :=
  AlgEquiv.ofAlgHom (scaleCoordinate u) (scaleCoordinate u⁻¹)
    (scaleCoordinate_comp u u⁻¹ (inv_mul_cancel _))
    (scaleCoordinate_comp u⁻¹ u (mul_inv_cancel _))

end LaurentCoordinate

section MultiplicativeGroup

variable {k B S : Type*} [CommRing k] [CommRing B] [CommRing S]
  [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S]
  [IsDomain B] [IsPrincipalIdealRing B]

local notation "H" => LaurentPolynomial k
local notation "F" => B ⊗[k] H
local notation "D" => S ⊗[k] H

/-- A multiplicative torsor over a PID is isomorphic to the scalar extension
of the Laurent coordinate algebra of the group. -/
theorem affineMultiplicativeTorsor_scalarExtension (T : AffineHopfTorsor k B S H) :
    Nonempty (F ≃ₐ[B] S) := by
  have hχ : Coalgebra.comul (R := k) (coordinateUnit k : H) =
      (coordinateUnit k : H) ⊗ₜ[k] (coordinateUnit k : H) := by
    rw [coordinateUnit_val, LaurentPolynomial.comul_T]
  obtain ⟨u, hu⟩ := T.exists_grouplike_unit (coordinateUnit k) hχ
  rw [coordinateUnit_val] at hu
  let f : F →ₐ[B] S := Algebra.TensorProduct.lift (Algebra.ofId B S) (evalLaurentUnit u)
    (fun _ _ => Commute.all _ _)
  let e := (Algebra.TensorProduct.cancelBaseChange k B S S H).symm
  let f' : S ⊗[B] F →ₐ[S] S ⊗[B] S := Algebra.TensorProduct.map (AlgHom.id S S) f
  let g : D →ₐ[S] D := T.chart.symm.toAlgHom.comp (f'.comp e.toAlgHom)
  have hg : g = scaleCoordinate u := by
    apply tensorLaurent_ext
    change T.chart.symm (f' (e ((1 : S) ⊗ₜ[k] (LaurentPolynomial.T 1 : H)))) = _
    rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    have hf : f ((1 : B) ⊗ₜ[k] (LaurentPolynomial.T 1 : H)) = (u : S) := by
      change (Algebra.ofId B S) (1 : B) * evalLaurentUnit u (LaurentPolynomial.T 1 : H) = (u : S)
      rw [evalLaurentUnit_T, map_one, one_mul]
    change T.chart.symm ((1 : S) ⊗ₜ[B] f ((1 : B) ⊗ₜ[k] (LaurentPolynomial.T 1 : H))) = _
    rw [hf, T.chart_symm_apply, ← Algebra.TensorProduct.one_def, one_mul, hu,
      scaleCoordinate_tmul_T, one_mul]
  have hgBijective : Function.Bijective g := by
    rw [hg]
    exact (scaleCoordinateEquiv (k := k) u).bijective
  have hBase : Function.Bijective (f.toLinearMap.lTensor S) := by
    change Function.Bijective f'
    constructor
    · intro x y hxy
      obtain ⟨x', rfl⟩ := e.surjective x
      obtain ⟨y', rfl⟩ := e.surjective y
      have h : g x' = g y' := congrArg T.chart.symm hxy
      exact congrArg e (hgBijective.1 h)
    · intro y
      obtain ⟨x, hx⟩ := hgBijective.2 (T.chart.symm y)
      exact ⟨e x, T.chart.symm.injective hx⟩
  letI := T.faithfullyFlat
  exact ⟨AlgEquiv.ofBijective f
    ⟨(Module.FaithfullyFlat.lTensor_injective_iff_injective B S f.toLinearMap).mp hBase.1,
      (Module.FaithfullyFlat.lTensor_surjective_iff_surjective B S f.toLinearMap).mp hBase.2⟩⟩

/-- The affine torsor under the constant multiplicative group has a section over a PID. -/
theorem affineMultiplicativeTorsor_has_section (T : AffineHopfTorsor k B S H) :
    Nonempty (S →ₐ[B] B) := by
  obtain ⟨e⟩ := affineMultiplicativeTorsor_scalarExtension T
  let p : F →ₐ[B] B := Algebra.TensorProduct.lift (AlgHom.id B B)
    ((Algebra.ofId k B).comp (Bialgebra.counitAlgHom k H)) (fun _ _ => Commute.all _ _)
  exact ⟨p.comp e.symm.toAlgHom⟩

end MultiplicativeGroup

end WideE
