import WideE.CoalgebraFiniteSpan
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.HopfAlgebra.Basic

/-! A finite-dimensional linear representation of a finite-type affine group
whose matrix coefficients generate its coordinate algebra. -/

noncomputable section

open scoped TensorProduct BigOperators Matrix

namespace WideE

section Evaluate

variable {k V M : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup M] [Module k M]

private def leftTensorEvaluate (f : V →ₗ[k] k) : V ⊗[k] M →ₗ[k] M :=
  (TensorProduct.lid k M).toLinearMap.comp (f.rTensor M)

@[simp] private theorem leftTensorEvaluate_tmul (f : V →ₗ[k] k) (v : V) (m : M) :
    leftTensorEvaluate f (v ⊗ₜ[k] m) = f v • m := by
  simp only [leftTensorEvaluate, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.rTensor_tmul, TensorProduct.lid_tmul]

private theorem leftTensorEvaluate_assoc_tmul (f : V →ₗ[k] k) (z : V ⊗[k] M) (m : M) :
    leftTensorEvaluate (M := M ⊗[k] M) f (TensorProduct.assoc k V M M (z ⊗ₜ[k] m)) =
      leftTensorEvaluate f z ⊗ₜ[k] m := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.zero_tmul, map_zero]
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | tmul v a => simp only [TensorProduct.assoc_tmul, leftTensorEvaluate_tmul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']

end Evaluate

variable (k H : Type*) [Field k] [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]

/-- The matrix coefficients of a regular subcomodule give a matrix realization
of the affine group. They generate the Hopf algebra as a coefficient algebra. -/
theorem exists_generatingHopfMatrix : ∃ (n : ℕ) (U : (Matrix (Fin n) (Fin n) H)ˣ),
    (∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j) ∧
    (∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0) ∧
    Algebra.adjoin k (Set.range fun ij : Fin n × Fin n => U.val ij.1 ij.2) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := H)
  obtain ⟨V, hFinite, hIn, hStable⟩ := exists_finite_rightCoaction_span_finset (k := k) s
  letI := hFinite
  let n := Module.finrank k V
  let b : Basis (Fin n) k V := Module.finBasis k V
  choose z hz using fun j : Fin n => hStable (b j : H) (b j).property
  let v (j : Fin n) : H := b j
  let M : Matrix (Fin n) (Fin n) H := fun i j => (TensorProduct.equivFinsuppOfBasisLeft b (z j)) i
  have hSum (j : Fin n) : Coalgebra.comul (R := k) (v j) = ∑ i, v i ⊗ₜ[k] M i j := by
    have h := (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply (z j)
    rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype] at h
    · rw [← hz j, ← h, map_sum]
      simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply, M, v]
    · intro i
      exact TensorProduct.tmul_zero _ _
  choose f hf using fun i : Fin n =>
    LinearMap.exists_extend ((Finsupp.lapply i).comp b.repr.toLinearMap)
  have hF (i j : Fin n) : f i (v j) = if j = i then 1 else 0 := by
    have h := LinearMap.congr_fun (hf i) (b j)
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      Finsupp.lapply_apply, Basis.repr_self, Finsupp.single_apply, v] using h
  have hEvaluate (i j : Fin n) : leftTensorEvaluate (f i) (Coalgebra.comul (R := k) (v j)) = M i j := by
    rw [hSum j, map_sum]
    simp only [leftTensorEvaluate_tmul, hF, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hComul (i j : Fin n) : Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j := by
    have h := congrArg (leftTensorEvaluate (M := H ⊗[k] H) (f i))
      (Coalgebra.coassoc_apply (R := k) (v j))
    rw [hSum j] at h
    simpa only [map_sum, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, leftTensorEvaluate_assoc_tmul,
      leftTensorEvaluate_tmul, hEvaluate, hF, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] using h.symm
  have hCounit (i j : Fin n) : Coalgebra.counit (R := k) (M i j) = if i = j then 1 else 0 := by
    have h := congrArg (leftTensorEvaluate (M := k) (f i)) (Coalgebra.lTensor_counit_comul (R := k) (v j))
    rw [hSum j] at h
    have h' : Coalgebra.counit (R := k) (M i j) = if j = i then 1 else 0 := by
      simpa only [map_sum, LinearMap.lTensor_tmul, leftTensorEvaluate_tmul, hF, ite_smul,
        one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h
    simpa only [eq_comm] using h'
  let U : (Matrix (Fin n) (Fin n) H)ˣ :=
    ⟨M, M.map (HopfAlgebra.antipode (R := k)), by
        ext i j
        have h := HopfAlgebra.mul_antipode_lTensor_comul_apply (R := k) (M i j)
        rw [hComul i j] at h
        simpa only [map_sum, LinearMap.lTensor_tmul, LinearMap.mul'_apply, Algebra.linearMap_apply,
          hCounit, apply_ite (algebraMap k H), map_one, map_zero, Matrix.mul_apply, Matrix.map_apply,
          Matrix.one_apply] using h,
      by
        ext i j
        have h := HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) (M i j)
        rw [hComul i j] at h
        simpa only [map_sum, LinearMap.rTensor_tmul, LinearMap.mul'_apply, Algebra.linearMap_apply,
          hCounit, apply_ite (algebraMap k H), map_one, map_zero, Matrix.mul_apply, Matrix.map_apply,
          Matrix.one_apply] using h⟩
  refine ⟨n, U, hComul, hCounit, ?_⟩
  let A := Algebra.adjoin k (Set.range fun ij : Fin n × Fin n => M ij.1 ij.2)
  have hEntry (i j : Fin n) : M i j ∈ A := Algebra.subset_adjoin ⟨(i, j), rfl⟩
  have hBasis (j : Fin n) : v j ∈ A := by
    have h := congrArg (TensorProduct.lid k H) (Coalgebra.rTensor_counit_comul (R := k) (v j))
    rw [hSum j] at h
    have hsum : (∑ i, Coalgebra.counit (R := k) (v i) • M i j) = v j := by
      simpa only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, one_smul] using h
    rw [← hsum]
    exact A.sum_mem fun i _ => A.smul_mem (hEntry i j) _
  have hmem (x : H) (hx : x ∈ V) : x ∈ A := by
    let y : V := ⟨x, hx⟩
    change V.subtype y ∈ A
    rw [← b.sum_repr y, map_sum]
    exact A.sum_mem fun i _ => by rw [map_smul]; exact A.smul_mem (hBasis i) _
  change A = ⊤
  apply top_unique
  rw [← hs]
  exact Algebra.adjoin_le fun x hx => hmem x (hIn x hx)

end WideE
