import WideE.PrincipalSimpleReflection
import WideE.AdjointCovariance

/-! A simple coreflection on the Cartan has a constant group representative. -/

noncomputable section

open LieAlgebra LieAlgebra.IsKilling LieModule
open scoped Matrix TensorProduct

namespace WideE

section Calculation

variable {k L : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ k L]

omit [CharZero k] [IsScalarTower ℚ k L] in
private theorem leftAdjointExp_of_three (u x : L)
    (h : IsNilpotent (leftAdjointDerivation k u).toLinearMap)
    (h₃ : ⁅u, ⁅u, ⁅u, x⁆⁆⁆ = 0) :
    LieDerivation.exp (leftAdjointDerivation k u) h x = x + ⁅u, x⁆ + ((2 : ℚ)⁻¹) • ⁅u, ⁅u, x⁆⁆ := by
  let D := (leftAdjointDerivation k u).toLinearMap
  have hD (y : L) : D y = ⁅u, y⁆ := leftAdjointDerivation_apply k _ _
  have hD₃ : (D ^ 3) x = 0 := by
    rw [pow_succ', pow_succ', pow_one, Module.End.mul_apply, Module.End.mul_apply, hD, hD, hD, h₃]
  have hHigher (n : ℕ) : (D ^ (3 + n)) x = 0 := by
    rw [add_comm, pow_add, Module.End.mul_apply, hD₃, map_zero]
  obtain ⟨n, hn⟩ := h
  have hZero : D ^ (3 + n) = 0 := pow_eq_zero_of_le (by omega) hn
  change IsNilpotent.exp D x = _
  rw [IsNilpotent.exp_eq_sum hZero, LinearMap.sum_apply, Finset.sum_range_add]
  simp only [LinearMap.smul_apply, hHigher, smul_zero, Finset.sum_const_zero, add_zero,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero, Nat.factorial_one,
    Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat, inv_one, one_smul, pow_zero, pow_one,
    Module.End.one_apply, zero_add, pow_succ' D 1, Module.End.mul_apply, hD]

omit [CharZero k] [IsScalarTower ℚ k L] in
private theorem leftAdjointExp_of_two (u x : L)
    (h : IsNilpotent (leftAdjointDerivation k u).toLinearMap)
    (h₂ : ⁅u, ⁅u, x⁆⁆ = 0) : LieDerivation.exp (leftAdjointDerivation k u) h x = x + ⁅u, x⁆ := by
  rw [leftAdjointExp_of_three u x h (by rw [h₂, lie_zero]), h₂, smul_zero, add_zero]

private theorem simpleCoreflection_exp_action {h e f : L} (t : IsSl2Triple h e f)
    (x : L) (a : k) (hxe : ⁅x, e⁆ = a • e) (hxf : ⁅x, f⁆ = -a • f)
    (hE : IsNilpotent (leftAdjointDerivation k e).toLinearMap)
    (hF : IsNilpotent (leftAdjointDerivation k (-f)).toLinearMap) :
    let E := LieDerivation.exp (leftAdjointDerivation k e) hE
    let F := LieDerivation.exp (leftAdjointDerivation k (-f)) hF
    E (F (E x)) = x - a • h := by
  dsimp only
  let E := (LieDerivation.exp (leftAdjointDerivation k e) hE).toLieHom
  let F := (LieDerivation.exp (leftAdjointDerivation k (-f)) hF).toLieHom
  change E (F (E x)) = _
  have hEx : ⁅e, x⁆ = -(a • e) := by rw [← lie_skew, hxe]
  have hEh : ⁅e, h⁆ = -((2 : k) • e) := by rw [← lie_skew, t.lie_h_e_smul k]
  have hFx : ⁅-f, x⁆ = -(a • f) := by rw [neg_lie, ← lie_skew f x, hxf, neg_smul, neg_neg]
  have hFe : ⁅-f, e⁆ = h := by rw [neg_lie, ← lie_skew f e, t.lie_e_f, neg_neg]
  have hFh : ⁅-f, h⁆ = -((2 : k) • f) := by
    rw [neg_lie, ← lie_skew f h, t.lie_lie_smul_f k, neg_neg]
  have h₁ : E x = x - a • e := by
    change LieDerivation.exp (leftAdjointDerivation k e) hE x = _
    rw [leftAdjointExp_of_two e x hE (by rw [hEx, lie_neg, lie_smul, lie_self, smul_zero, neg_zero]),
      hEx, sub_eq_add_neg]
  have h₂ : E e = e := by
    change LieDerivation.exp (leftAdjointDerivation k e) hE e = _
    rw [leftAdjointExp_of_two e e hE (by simp only [lie_self, lie_zero]), lie_self, add_zero]
  have h₃ : E h = h - (2 : k) • e := by
    change LieDerivation.exp (leftAdjointDerivation k e) hE h = _
    rw [leftAdjointExp_of_two e h hE (by rw [hEh, lie_neg, lie_smul, lie_self, smul_zero, neg_zero]),
      hEh, sub_eq_add_neg]
  have h₄ : F x = x - a • f := by
    change LieDerivation.exp (leftAdjointDerivation k (-f)) hF x = _
    rw [leftAdjointExp_of_two (-f) x hF (by rw [hFx, lie_neg, lie_smul, neg_lie, lie_self, neg_zero,
      smul_zero, neg_zero]), hFx, sub_eq_add_neg]
  have h₅ : F e = e + h - f := by
    change LieDerivation.exp (leftAdjointDerivation k (-f)) hF e = _
    have hHalf : ((2 : ℚ)⁻¹) • (-((2 : k) • f)) = -f := by
      rw [← IsScalarTower.algebraMap_smul k ((2 : ℚ)⁻¹), smul_neg, smul_smul, map_inv₀, map_ofNat,
        inv_mul_cancel₀ (by norm_num : (2 : k) ≠ 0), one_smul]
    rw [leftAdjointExp_of_three (-f) e hF (by rw [hFe, hFh, lie_neg, lie_smul, neg_lie, lie_self,
      neg_zero, smul_zero, neg_zero]), hFe, hFh, hHalf, sub_eq_add_neg]
  have hMid : F (E x) = x - a • e - a • h := by
    rw [h₁, LieHom.map_sub, LieHom.map_smul, h₄, h₅]
    simp only [smul_sub, smul_add]
    abel
  rw [hMid, LieHom.map_sub, LieHom.map_sub, LieHom.map_smul, LieHom.map_smul, h₁, h₂, h₃]
  simp only [smul_sub, smul_add, smul_smul, mul_comm a 2, two_mul, add_smul]
  abel

end Calculation

section Group

variable {k L A ι η : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ k L] [LieAlgebra.IsKilling k L] [FiniteDimensional k L]
  [CommRing A] [HopfAlgebra k A] [Fintype ι] [DecidableEq ι] [Fintype η] [DecidableEq η]
variable {H : LieSubalgebra k L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable k H L]

local notation "Φ" => LieAlgebra.IsKilling.rootSystem H
local notation "𝔤" => hopfInvariantDerivations k A
local notation "J" => hopfLieVectorInvariantDerivations (k := k) (H := A)

/-- An element independent of the Cartan parameter induces the simple coreflection on the Cartan. -/
theorem exists_hopfPoint_simpleCoreflection_on_cartan (c : Basis η k (HopfCotangent k A))
    (U : (Matrix ι ι A)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (j : L →ₗ⁅k⁆ 𝔤) (i : H.root) (e f : L)
    (hE : e ∈ rootSpace H (((Φ).root i : H →ₗ[k] k) : H → k))
    (hF : f ∈ rootSpace H (-(((Φ).root i : H →ₗ[k] k) : H → k)))
    (ht : IsSl2Triple ((Φ).coroot i : L) e f) :
    ∃ p : A →ₐ[k] k, ∀ z : H,
      hopfAdjoint p ((J).symm (j (z : L))) = (J).symm (j ((Φ).coreflection i z : H)) := by
  letI : LieAlgebra ℚ 𝔤 := inferInstanceAs (LieAlgebra ℚ (RestrictScalars ℚ k 𝔤))
  letI : Group (A →ₐ[k] k) := hopfPointGroup
  let h : L := (Φ).coroot i
  let ρ := (hopfLieMatrixHom U.val hD).comp j
  have heq : ⁅h, e⁆ = (2 : k) • e := ht.lie_h_e_smul k
  have hfq : ⁅h, -f⁆ = -(2 : k) • (-f) := by rw [lie_neg, ht.lie_lie_smul_f k, smul_neg, neg_smul]
  have heNil : IsNilpotent (hopfLieMatrix U.val (j e)) := by
    change IsNilpotent (ρ e)
    apply isNilpotent_of_lie_eq_smul_ne_zero (ρ h) (ρ e) (2 : k) (by norm_num)
    rw [← LieHom.map_lie, heq, LieHom.map_smul]
  have hfNil : IsNilpotent (hopfLieMatrix U.val (j (-f))) := by
    change IsNilpotent (ρ (-f))
    apply isNilpotent_of_lie_eq_smul_ne_zero (ρ h) (ρ (-f)) (-(2 : k)) (by norm_num)
    rw [← LieHom.map_lie, hfq, LieHom.map_smul]
  have heAd : IsNilpotent (leftAdjointDerivation k e).toLinearMap := by
    rw [show (leftAdjointDerivation k e).toLinearMap = LieModule.toEnd k L L e from
      LinearMap.ext (leftAdjointDerivation_apply k e)]
    exact sl2_lower_isNilpotent (M := L) ht.symm
  have hfAd : IsNilpotent (leftAdjointDerivation k (-f)).toLinearMap := by
    rw [show (leftAdjointDerivation k (-f)).toLinearMap = LieModule.toEnd k L L (-f) from
      LinearMap.ext (leftAdjointDerivation_apply k (-f))]
    rw [LieHom.map_neg]
    exact (sl2_lower_isNilpotent (M := L) ht).neg
  obtain ⟨heJ, u, hu⟩ := exists_hopfPoint_lieAdjointExp U hD he hGen (j e) heNil
  obtain ⟨hfJ, v, hv⟩ := exists_hopfPoint_lieAdjointExp U hD he hGen (j (-f)) hfNil
  refine ⟨(u * v) * u, fun z => ?_⟩
  have hxe : ⁅(z : L), e⁆ = (Φ).root i z • e := lie_eq_smul_of_mem_rootSpace hE z
  have hxf : ⁅(z : L), f⁆ = -(Φ).root i z • f := lie_eq_smul_of_mem_rootSpace hF z
  have hEq := simpleCoreflection_exp_action ht (z : L) ((Φ).root i z) hxe hxf heAd hfAd
  simp only at hEq
  apply (J).injective
  rw [hopfAdjoint_mul c, hopfAdjoint_mul c, hu, hv, hu, (J).apply_symm_apply,
    ← map_leftAdjointExp j e _ heAd heJ, ← map_leftAdjointExp j (-f) _ hfAd hfJ,
    ← map_leftAdjointExp j e _ heAd heJ, (J).apply_symm_apply]
  rw [hEq, RootPairing.coreflection_apply]
  rfl

end Group

end WideE
