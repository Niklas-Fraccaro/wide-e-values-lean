import WideE.HopfPointGroup
import WideE.HopfSmoothness
import WideE.OrbitMapFlatness
import WideE.ProjectiveLineStabilizer

/-! A line stabilizer is reduced via the flat scaled orbit morphism. -/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

universe u

attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

variable {k H ι : Type u} [Field k] [IsAlgClosed k] [CharZero k] [CommRing H] [IsDomain H]
  [HopfAlgebra k H] [Algebra.FiniteType k H] [Fintype ι] [DecidableEq ι]

/-- The coordinate ring of the line stabilizer is a retract of the double
fiber product of the scaled orbit map. In characteristic zero that tensor
product is reduced by flatness and separability. -/
theorem projectiveLineStabilizer_isReduced (U : (Matrix ι ι H)ˣ)
    (hD : ∀ a b, Coalgebra.comul (R := k) (U.val a b) = ∑ l, U.val a l ⊗ₜ[k] U.val l b)
    (he : ∀ a b, Coalgebra.counit (R := k) (U.val a b) = if a = b then 1 else 0)
    (v : ι → k) (i : ι) (hi : v i ≠ 0) : IsReduced (H ⧸ projectiveLineStabilizerIdeal U v i) := by
  let Q := H ⧸ projectiveLineStabilizerIdeal U v i
  let C := OrbitConeAlgebra U.val v
  let L := LaurentPolynomial H
  let π : H →ₐ[k] Q := Ideal.Quotient.mkₐ k _
  let f := orbitConeMap U.val v
  letI : Algebra C L := f.toRingHom.toAlgebra
  letI : IsScalarTower k C L := IsScalarTower.of_algHom f
  let I := L ⊗[C] L
  letI : SMulCommClass C C L := ⟨fun a b x => by simp only [Algebra.smul_def]; ac_rfl⟩
  letI : SMulCommClass C k L := ⟨fun a b x => by simp only [Algebra.smul_def]; ac_rfl⟩
  letI : Algebra k I := Algebra.TensorProduct.leftAlgebra
  letI : IsScalarTower k C I := IsScalarTower.of_algebraMap_eq (R := k) (S := C) (A := I) fun a => by
    change (algebraMap k L a) ⊗ₜ[C] (1 : L) =
      (algebraMap C L (algebraMap k C a)) ⊗ₜ[C] (1 : L)
    rw [IsScalarTower.algebraMap_apply k C L]
  let j₁ : L →ₐ[C] I := Algebra.TensorProduct.includeLeft
  let j₂ : L →ₐ[C] I := Algebra.TensorProduct.includeRight
  let a := (j₁.restrictScalars k).comp (IsScalarTower.toAlgHom k H L)
  let b := (j₂.restrictScalars k).comp (IsScalarTower.toAlgHom k H L)
  let t := (LaurentPolynomial.isUnit_T (R := H) 1).unit
  have ht : (t : L) = LaurentPolynomial.T 1 := IsUnit.unit_spec _
  let s := t.map j₁.toRingHom.toMonoidHom
  let r := t.map j₂.toRingHom.toMonoidHom
  letI : Group (H →ₐ[k] I) := hopfPointGroup
  let ρ := hopfPointMatrix (A := I) U hD he
  let x := algebraMap k I ∘ v
  have hOrbit : (s : I) • ((ρ a).val *ᵥ x) = (r : I) • ((ρ b).val *ᵥ x) := by
    funext j
    have hJ := (j₁.commutes (orbitConeCoordinate U.val v j)).trans
      (j₂.commutes (orbitConeCoordinate U.val v j)).symm
    change j₁ (f (orbitConeCoordinate U.val v j)) = j₂ (f (orbitConeCoordinate U.val v j)) at hJ
    rw [orbitConeMap_coordinate, map_mul, map_mul, ← ht] at hJ
    have ha := congrFun (orbitVector_map a U.val v) j
    have hb := congrFun (orbitVector_map b U.val v) j
    change a (orbitVector U.val v j) = ((ρ a).val *ᵥ x) j at ha
    change b (orbitVector U.val v j) = ((ρ b).val *ᵥ x) j at hb
    change (s : I) * ((ρ a).val *ᵥ x) j = (r : I) * ((ρ b).val *ᵥ x) j
    rw [← ha, ← hb, mul_comm (s : I), mul_comm (r : I)]
    exact hJ
  let d := a⁻¹ * b
  have hd : (ρ d).val *ᵥ x = ((r⁻¹ * s : Iˣ) : I) • x := by
    have h := congrArg ((ρ a⁻¹).val *ᵥ ·) hOrbit
    change (ρ a⁻¹).val *ᵥ ((s : I) • ((ρ a).val *ᵥ x)) =
      (ρ a⁻¹).val *ᵥ ((r : I) • ((ρ b).val *ᵥ x)) at h
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, Matrix.one_mulVec] at h
    change (s : I) • x = (r : I) • ((ρ d).val *ᵥ x) at h
    have hr : ((r⁻¹ : Iˣ) : I) * (r : I) = 1 := r.inv_val
    have hAction (a b : I) (w : ι → I) : a • (b • w) = (a * b) • w :=
      funext fun j => (mul_assoc a b (w j)).symm
    calc
      (ρ d).val *ᵥ x = (1 : I) • ((ρ d).val *ᵥ x) := (one_smul _ _).symm
      _ = ((r⁻¹ : Iˣ) : I) • ((r : I) • ((ρ d).val *ᵥ x)) :=
        (congrArg (fun a : I => a • ((ρ d).val *ᵥ x)) hr.symm).trans (hAction _ _ _).symm
      _ = ((r⁻¹ : Iˣ) : I) • ((s : I) • x) := congrArg (fun w : ι → I => ((r⁻¹ : Iˣ) : I) • w) h.symm
      _ = ((r⁻¹ * s : Iˣ) : I) • x := hAction _ _ _
  have hdKill : projectiveLineStabilizerIdeal U v i ≤ RingHom.ker d.toRingHom := by
    apply projectiveLineIdeal_le_ker (R := k) v i hi _ d ((r⁻¹ * s : Iˣ) : I)
    rw [orbitVector_map]
    exact hd
  let j : Q →ₐ[k] I := Ideal.Quotient.liftₐ _ d (fun _ hx => RingHom.mem_ker.mp (hdKill hx))
  obtain ⟨c, hc⟩ := projectiveLineStabilizer_scale U v i hi
  let e₁ := evalLaurentPoint (hopfPointOne : H →ₐ[k] Q) 1
  let e₂ := evalLaurentPoint π c⁻¹
  letI : Group (H →ₐ[k] Q) := hopfPointGroup
  have hOne (j : ι) : (hopfPointOne : H →ₐ[k] Q) (orbitVector U.val v j) = algebraMap k Q (v j) := by
    have h := orbitVector_map (hopfPointOne : H →ₐ[k] Q) U.val v
    change (hopfPointOne : H →ₐ[k] Q).toRingHom ∘ orbitVector U.val v =
      (hopfPointMatrix U hD he (1 : H →ₐ[k] Q)).val *ᵥ (algebraMap k Q ∘ v) at h
    rw [map_one, Units.val_one, Matrix.one_mulVec] at h
    exact congrFun h j
  have hPi (j : ι) : π (orbitVector U.val v j) = (c : Q) * algebraMap k Q (v j) := by
    rw [← orbitVector_map] at hc
    exact congrFun hc j
  have hAgree : e₁.comp f = e₂.comp f := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    change evalLaurentPoint (hopfPointOne : H →ₐ[k] Q) 1 (f (orbitConeCoordinate U.val v j)) =
      evalLaurentPoint π c⁻¹ (f (orbitConeCoordinate U.val v j))
    rw [orbitConeMap_coordinate, map_mul, map_mul, evalLaurentPoint_C, evalLaurentPoint_C,
      evalLaurentPoint_T_one, evalLaurentPoint_T_one, Units.val_one, mul_one, hOne, hPi]
    rw [mul_right_comm, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  letI : Algebra C Q := (e₁.comp f).toRingHom.toAlgebra
  letI : IsScalarTower k C Q := IsScalarTower.of_algHom (e₁.comp f)
  let e₁C : L →ₐ[C] Q := { toRingHom := e₁.toRingHom, commutes' := fun _ => rfl }
  let e₂C : L →ₐ[C] Q :=
    { toRingHom := e₂.toRingHom, commutes' := fun z => AlgHom.congr_fun hAgree.symm z }
  let rC := Algebra.TensorProduct.lift e₁C e₂C (fun _ _ => Commute.all _ _)
  let ret := rC.restrictScalars k
  have hA : ret.comp a = hopfPointOne := by
    apply AlgHom.ext
    intro y
    change e₁ (LaurentPolynomial.C y) * e₂ 1 = (hopfPointOne : H →ₐ[k] Q) y
    rw [map_one, mul_one]
    exact evalLaurentPoint_C _ _ _
  have hB : ret.comp b = π := by
    apply AlgHom.ext
    intro y
    change e₁ 1 * e₂ (LaurentPolynomial.C y) = π y
    rw [map_one, one_mul]
    exact evalLaurentPoint_C _ _ _
  have hRet : ret.comp d = π := by
    change ret.comp (hopfPointMul (a.comp (hopfAntipodeAlgHom k H)) b) = π
    rw [hopfPointMul_postcompose, ← AlgHom.comp_assoc, hA, hB]
    change ((1 : H →ₐ[k] Q)⁻¹) * π = π
    rw [inv_one, one_mul]
  have hInjective : Function.Injective j := by
    apply Function.LeftInverse.injective (g := ret)
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (projectiveLineStabilizerIdeal U v i) y
    exact AlgHom.congr_fun hRet z
  letI : IsDomain C := Function.Injective.isDomain f (orbitConeMap_injective U.val v)
  letI : CharZero C := Algebra.charZero_of_charZero k C
  letI : Algebra.FiniteType k L := laurentPolynomial_finiteType (H := H)
  letI : Algebra.FiniteType C L := Algebra.FiniteType.of_restrictScalars_finiteType k C L
  letI : Module.Flat C L := orbitConeMap_flat U hD v
  letI : IsReduced I := flatDomainTensor_isReduced (orbitConeMap_injective U.val v)
  exact isReduced_of_injective j.toRingHom hInjective

end WideE
