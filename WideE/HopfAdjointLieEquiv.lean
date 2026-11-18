import WideE.HopfLieMatrixAdjoint

/-! Adjoint action as an actual automorphism of the Lie algebra of invariant derivations. -/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

variable {k H ι η : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [Fintype ι] [DecidableEq ι] [Fintype η] [DecidableEq η]

local notation "L" => (HopfLieVector k H k)
local notation "G" => (H →ₐ[k] k)
local notation "𝔤" => (hopfInvariantDerivations k H)

omit [DecidableEq η] in
/-- The counit point acts trivially on the Lie algebra. -/
theorem hopfAdjoint_one_point (b : Basis η k (HopfCotangent k H)) (x : L) :
    hopfAdjoint (Bialgebra.counitAlgHom k H) x = x := by
  classical
  have he : (hopfAdjointMatrix b).map (Bialgebra.counitAlgHom k H) = 1 := by
    exact Matrix.ext fun i j => (hopfAdjointMatrix_counit b i j).trans Matrix.one_apply.symm
  have h := hopfAdjoint_apply_basis b (Bialgebra.counitAlgHom k H) x
  rw [he, Matrix.one_mulVec] at h
  exact b.ext fun i => congrFun h i

omit [DecidableEq η] in
private def hopfAdjointLinear (b : Basis η k (HopfCotangent k H)) (g : G) : L →ₗ[k] L :=
  (b.constr k).toLinearMap.comp (((hopfAdjointMatrix b).map g).mulVecLin.comp (b.constr k).symm.toLinearMap)

omit [DecidableEq η] in
private theorem hopfAdjointLinear_apply (b : Basis η k (HopfCotangent k H)) (g : G) (x : L) :
    hopfAdjointLinear b g x = hopfAdjoint g x := by
  apply b.ext
  intro i
  change b.constr k (((hopfAdjointMatrix b).map g) *ᵥ (fun j => x (b j))) (b i) = _
  rw [Basis.constr_basis]
  exact (congrFun (hopfAdjoint_apply_basis b g x) i).symm

private theorem commute_conjugate_bracket (P : (Matrix ι ι k)ˣ) (X Y : Matrix ι ι k) :
    ⁅P.val * X * P.inv, P.val * Y * P.inv⁆ = P.val * ⁅X, Y⁆ * P.inv := by
  have h (A B : Matrix ι ι k) : P.val * A * P.inv * (P.val * B * P.inv) = P.val * (A * B) * P.inv := by
    rw [← mul_assoc _ _ P.inv, mul_assoc _ P.inv (P.val * B), ← mul_assoc P.inv P.val,
      P.inv_val, one_mul, mul_assoc P.val A]
  rw [Ring.lie_def, h, h, Ring.lie_def, mul_sub, sub_mul]

/-- Adjunction by a group point preserves the Lie algebra bracket. -/
def hopfAdjointInvariantDerivationsLieEquiv (b : Basis η k (HopfCotangent k H)) (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (g : G) : 𝔤 ≃ₗ⁅k⁆ 𝔤 := by
  letI : Group G := hopfPointGroup
  let E := hopfLieVectorInvariantDerivations (k := k) (H := H)
  let f (g' : G) : 𝔤 →ₗ[k] 𝔤 := E.toLinearMap.comp ((hopfAdjointLinear b g').comp E.symm.toLinearMap)
  have hF (g' : G) (x : 𝔤) : f g' x = E (hopfAdjoint g' (E.symm x)) := by
    change E (hopfAdjointLinear b g' (E.symm x)) = _
    rw [hopfAdjointLinear_apply]
  let ρ := hopfLieMatrixHom U.val hΔ
  let P := hopfPointMatrix U hΔ hε g
  have hM (x : 𝔤) : ρ (f g x) = P.val * ρ x * P.inv := by
    change hopfLieMatrix U.val (f g x) = _
    rw [hF, hopfLieMatrix_invariantDerivations, hopfCotangentMatrix_adjoint,
      ← hopfLieMatrix_invariantDerivations, E.apply_symm_apply]
    rfl
  let φ : 𝔤 →ₗ⁅k⁆ 𝔤 :=
    { toLinearMap := f g
      map_lie' := by
        intro x y
        apply hopfLieMatrixHom_injective U.val hΔ hGen
        change ρ (f g ⁅x, y⁆) = ρ ⁅f g x, f g y⁆
        rw [hM, LieHom.map_lie, LieHom.map_lie, hM, hM, commute_conjugate_bracket] }
  have hInv (g₁ g₂ : G) (hg : g₁ * g₂ = 1) : Function.LeftInverse (f g₁) (f g₂) := by
    intro x
    rw [hF, hF, E.symm_apply_apply, ← hopfAdjoint_mul b, hg]
    change E (hopfAdjoint (Bialgebra.counitAlgHom k H) (E.symm x)) = x
    rw [hopfAdjoint_one_point b, E.apply_symm_apply]
  exact LieEquiv.ofBijective φ ⟨(hInv g⁻¹ g (inv_mul_cancel g)).injective,
    (hInv g g⁻¹ (mul_inv_cancel g)).surjective⟩

@[simp] theorem hopfAdjointInvariantDerivationsLieEquiv_apply (b : Basis η k (HopfCotangent k H))
    (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (g : G) (x : 𝔤) :
    hopfAdjointInvariantDerivationsLieEquiv b U hΔ hε hGen g x =
      hopfLieVectorInvariantDerivations (hopfAdjoint g (hopfLieVectorInvariantDerivations.symm x)) := by
  change hopfLieVectorInvariantDerivations
    (hopfAdjointLinear b g (hopfLieVectorInvariantDerivations.symm x)) = _
  rw [hopfAdjointLinear_apply]

end WideE
