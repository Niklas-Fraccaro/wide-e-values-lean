import WideE.PrincipalSl2
import WideE.HopfAdjointExponential
import WideE.AdjointWeightNilpotence
import WideE.Sl2WeightSplitting

/-! Simple Weyl reflections on the affine set `e+Cartan` are realized by negative root exponentials. -/

noncomputable section

open LieAlgebra LieAlgebra.IsKilling LieModule
open scoped Matrix TensorProduct

namespace WideE

section Exponential

variable {k L : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ k L]

/-- The adjoint exponential of a simple negative root element changes the Cartan term by
the corresponding reflection. -/
theorem leftAdjointExp_eq_simpleReflection (E z h f : L) (a : k)
    (hEf : ⁅E, f⁆ = h) (hzf : ⁅z, f⁆ = -a • f) (hhf : ⁅h, f⁆ = -(2 : k) • f)
    (hN : IsNilpotent (leftAdjointDerivation k (a • f)).toLinearMap) :
    LieDerivation.exp (leftAdjointDerivation k (a • f)) hN (E + z) = E + (z - a • h) := by
  let x := E + z
  let D := (leftAdjointDerivation k (a • f)).toLinearMap
  have hD (y : L) : D y = ⁅a • f, y⁆ := leftAdjointDerivation_apply k (a • f) y
  have hF₁ : ⁅f, E⁆ = -h := (lie_skew f E).symm.trans (congrArg Neg.neg hEf)
  have hF₂ : ⁅f, z⁆ = a • f := by rw [← lie_skew, hzf, neg_smul, neg_neg]
  have hF₃ : ⁅f, h⁆ = (2 : k) • f := by rw [← lie_skew, hhf, neg_smul, neg_neg]
  have hDf : D f = 0 := by rw [hD, smul_lie, lie_self, smul_zero]
  have hD₁ : D x = a • (-h + a • f) := by
    rw [hD, show x = E + z from rfl, smul_lie, lie_add, hF₁, hF₂]
  have hD₂ : (D ^ 2) x = (-(2 : k) * a ^ 2) • f := by
    rw [pow_succ', pow_one, Module.End.mul_apply, hD₁, map_smul, map_add, map_neg, map_smul,
      hDf, smul_zero, add_zero, hD, smul_lie, hF₃]
    simp only [smul_smul, ← neg_smul]
    congr 1
    ring
  have hD₃ : (D ^ 3) x = 0 := by
    rw [pow_succ', Module.End.mul_apply, hD₂, map_smul, hDf, smul_zero]
  have hHigher (i : ℕ) : (D ^ (3 + i)) x = 0 := by
    rw [add_comm, pow_add, Module.End.mul_apply, hD₃, map_zero]
  obtain ⟨n, hn⟩ : IsNilpotent D := hN
  have hZero : D ^ (3 + n) = 0 := pow_eq_zero_of_le (by omega) hn
  have hHalf : ((2 : ℚ)⁻¹) • ((-(2 : k) * a ^ 2) • f) = -(a ^ 2) • f := by
    rw [← IsScalarTower.algebraMap_smul k ((2 : ℚ)⁻¹), smul_smul, map_inv₀, map_ofNat]
    congr 1
    field_simp
    ring
  change IsNilpotent.exp D x = _
  rw [IsNilpotent.exp_eq_sum hZero, LinearMap.sum_apply, Finset.sum_range_add]
  simp only [LinearMap.smul_apply, hHigher, smul_zero, Finset.sum_const_zero, add_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero, Nat.factorial_one,
    Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat, inv_one, one_smul, pow_zero, pow_one,
    Module.End.one_apply, zero_add, hD₁, hD₂, hHalf]
  simp only [x, smul_add, smul_neg, smul_smul, neg_smul, pow_two, sub_eq_add_neg]
  abel

end Exponential

section Group

variable {k L A ι : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ k L] [LieAlgebra.IsKilling k L] [FiniteDimensional k L]
  [CommRing A] [HopfAlgebra k A] [Fintype ι] [DecidableEq ι]
variable {H : LieSubalgebra k L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable k H L]

local notation "Φ" => LieAlgebra.IsKilling.rootSystem H
local notation "𝔤" => hopfInvariantDerivations k A
local notation "J" => hopfLieVectorInvariantDerivations (k := k) (H := A)

/-- A simple reflection of a Cartan element in the principal affine set `e+Cartan`
is induced by a point with the expected negative root exponential matrix. -/
theorem exists_hopfPoint_principalSimpleReflection (U : (Matrix ι ι A)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (j : L →ₗ⁅k⁆ 𝔤) (b : (Φ).Base) [Fintype b.support]
    (e f : b.support → L)
    (heRoot : ∀ i : b.support, e i ∈ rootSpace H (((Φ).root i : H →ₗ[k] k) : H → k))
    (hfRoot : ∀ i : b.support, f i ∈ rootSpace H (-(((Φ).root i : H →ₗ[k] k) : H → k)))
    (ht : ∀ i : b.support, IsSl2Triple ((Φ).coroot i : L) (e i) (f i))
    (i : b.support) (z : H) :
    ∃ p : A →ₐ[k] k,
      (hopfPointMatrix U hD he p).val =
        IsNilpotent.exp (hopfLieMatrix U.val (j ((Φ).root i z • f i))) ∧
      hopfAdjoint p ((J).symm (j ((∑ r, e r) + (z : L)))) =
        (J).symm (j ((∑ r, e r) + ((Φ).coreflection i z : L))) := by
  classical
  letI : LieAlgebra ℚ 𝔤 := inferInstanceAs (LieAlgebra ℚ (RestrictScalars ℚ k 𝔤))
  let E : L := ∑ r, e r
  let a : k := (Φ).root i z
  let D : L := a • f i
  let h : L := (Φ).coroot i
  have hEf : ⁅E, f i⁆ = h := by
    rw [show E = ∑ r, e r from rfl, sum_lie, Finset.sum_eq_single i]
    · exact (ht i).lie_e_f
    · intro r _ hr
      exact lie_simple_pos_neg_eq_zero b r i hr (heRoot r) (hfRoot i)
    · simp
  have hzf : ⁅(z : L), f i⁆ = -a • f i :=
    lie_eq_smul_of_mem_rootSpace (hfRoot i) z
  have hhf : ⁅h, f i⁆ = -(2 : k) • f i := by
    rw [neg_smul, two_smul]
    simpa only [h, two_nsmul] using (ht i).lie_h_f_nsmul
  have hRef : ((Φ).coreflection i z : L) = (z : L) - a • h := by
    rw [RootPairing.coreflection_apply]
    rfl
  let h₀ : L := principalCartanElement b
  have hPr : ⁅h₀, f i⁆ = -(2 : k) • f i := by
    have hEval := lie_eq_smul_of_mem_rootSpace (hfRoot i) (principalCartanElement b)
    change ⁅h₀, f i⁆ = -((Φ).root i (principalCartanElement b)) • f i at hEval
    rwa [principalCartanElement_simpleRoot] at hEval
  have hWeight : ⁅h₀, D⁆ = -(2 : k) • D := by
    rw [show D = a • f i from rfl, lie_smul, hPr, smul_comm a]
  let ρ := (hopfLieMatrixHom U.val hD).comp j
  have hNil : IsNilpotent (hopfLieMatrix U.val (j D)) := by
    change IsNilpotent (ρ D)
    apply isNilpotent_of_lie_eq_smul_ne_zero (ρ h₀) (ρ D) (-(2 : k)) (by norm_num)
    rw [← LieHom.map_lie, hWeight, LieHom.map_smul]
  have hN : IsNilpotent (leftAdjointDerivation k D).toLinearMap := by
    let η := LieModule.toEnd k L L
    have hEq : (leftAdjointDerivation k D).toLinearMap = η D :=
      LinearMap.ext (leftAdjointDerivation_apply k D)
    rw [hEq, show D = a • f i from rfl, LieHom.map_smul]
    exact (sl2_lower_isNilpotent (M := L) (ht i)).smul a
  obtain ⟨hN', p, hpMatrix, hp⟩ := exists_hopfPoint_lieAdjointExp_with_matrix U hD he hGen (j D) hNil
  refine ⟨p, hpMatrix, ?_⟩
  apply (J).injective
  change (J) (hopfAdjoint p ((J).symm (j (E + (z : L))))) =
    (J) ((J).symm (j (E + ((Φ).coreflection i z : L))))
  rw [hRef, hp, (J).apply_symm_apply, (J).apply_symm_apply]
  rw [← map_leftAdjointExp j D (E + (z : L)) hN hN']
  exact congrArg j (leftAdjointExp_eq_simpleReflection E (z : L) h (f i) a hEf hzf hhf hN)

end Group

end WideE
