import WideE.ReducedNormDescent
import WideE.Tsen

/-!
# Division algebras over a C₁ field with a Galois splitting

The descended determinant has degree equal to the matrix size. If this size
exceeds one, the C₁ property gives a nonzero element with singular image,
contradicting invertibility in the division algebra.
-/

noncomputable section

open scoped Matrix TensorProduct BigOperators
open MvPolynomial

namespace WideE

variable {K L D : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
variable [DivisionRing D] [Algebra K D] [FiniteDimensional K D] {m : ℕ}

/-- A finite-dimensional division algebra over a C₁ field with a split Galois
scalar extension has dimension one. -/
theorem finrank_eq_one_of_isC1_of_galois_splitting (hK : IsC1 K)
    (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin m) (Fin m) L) : Module.finrank K D = 1 := by
  classical
  let r := Module.finrank K D
  let b : Basis (Fin r) K D := Module.finBasis K D
  have hdim : r = m * m := by
    calc
      r = Module.finrank L (L ⊗[K] D) := by
        simpa only [Fintype.card_fin] using (Module.finrank_eq_card_basis
          (Algebra.TensorProduct.basis L b)).symm
      _ = Module.finrank L (Matrix (Fin m) (Fin m) L) := e.toLinearEquiv.finrank_eq
      _ = m * m := by rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one]
  have hm : 0 < m := by
    have hr : 0 < r := Module.finrank_pos
    by_contra h
    have hm₀ : m = 0 := Nat.eq_zero_of_not_pos h
    rw [hdim, hm₀, zero_mul] at hr
    exact (Nat.lt_irrefl 0) hr
  have hlt : ¬ m < r := by
    intro hmr
    letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    obtain ⟨q, hq, hmap⟩ := exists_reducedNorm_polynomial_of_galois_splitting e b
    rw [Fintype.card_fin] at hq
    obtain ⟨x, hx, hq₀⟩ := hK q hq hm hmr
    let a := b.equivFun.symm x
    have ha : a ≠ 0 := by
      intro ha₀
      apply hx
      apply b.equivFun.symm.injective
      simpa only [map_zero] using ha₀
    let ρ : D →ₐ[K] Matrix (Fin m) (Fin m) L :=
      (e.restrictScalars K).toAlgHom.comp Algebra.TensorProduct.includeRight
    have hComb : (∑ i, algebraMap K L (x i) • ρ (b i)) = ρ a := by
      dsimp only [a]
      rw [Basis.equivFun_symm_apply, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [IsScalarTower.algebraMap_smul L]
      exact (ρ.toLinearMap.map_smul (x i) (b i)).symm
    have hEval : eval (algebraMap K L ∘ x) (map (algebraMap K L) q) = 0 := by
      rw [eval_map, ← eval₂_comp, hq₀, map_zero]
    rw [hmap, eval_detMatrixLinearForm] at hEval
    change (∑ i, algebraMap K L (x i) • ρ (b i)).det = 0 at hEval
    rw [hComb] at hEval
    have hu : IsUnit (ρ a) := (isUnit_iff_ne_zero.mpr ha).map ρ
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero hEval
  have hm₁ : m = 1 := by
    by_contra h
    apply hlt
    rw [hdim]
    simpa only [one_mul] using (Nat.mul_lt_mul_of_pos_right (show 1 < m by omega) hm)
  change r = 1
  rw [hdim, hm₁, one_mul]

/-- A finite-dimensional division algebra with a Galois splitting over a C₁ field
is isomorphic to the base field. -/
theorem exists_algEquiv_base_of_isC1_of_galois_splitting (hK : IsC1 K)
    (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin m) (Fin m) L) : Nonempty (D ≃ₐ[K] K) := by
  have hdim := finrank_eq_one_of_isC1_of_galois_splitting hK e
  have hSurj : Function.Surjective (Algebra.ofId K D) := by
    intro a
    obtain ⟨x, hx⟩ := (finrank_eq_one_iff_of_nonzero' (1 : D) one_ne_zero).mp hdim a
    exact ⟨x, by simpa only [Algebra.smul_def, mul_one, Algebra.ofId_apply] using hx⟩
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId K D) ⟨(algebraMap K D).injective, hSurj⟩).symm⟩

end WideE
