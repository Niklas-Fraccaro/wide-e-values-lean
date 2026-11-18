import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-! Finite-dimensional subspaces of the regular comodule containing specified elements. -/

noncomputable section

open scoped TensorProduct BigOperators

namespace WideE

variable {k H : Type*} [Field k] [AddCommGroup H] [Module k H] [Coalgebra k H]

section Coordinates

variable {ι M : Type*} [DecidableEq ι] [AddCommGroup M] [Module k M]

private def rightTensorCoordinate (b : Basis ι k H) (i : ι) : M ⊗[k] H →ₗ[k] M :=
  (Finsupp.lapply i).comp (TensorProduct.equivFinsuppOfBasisRight b).toLinearMap

omit [Coalgebra k H] in
@[simp] private theorem rightTensorCoordinate_tmul (b : Basis ι k H) (i : ι) (m : M) (h : H) :
    rightTensorCoordinate b i (m ⊗ₜ[k] h) = b.repr h i • m :=
  TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply b m h i

private theorem rightTensorCoordinate_comul_rTensor (b : Basis ι k H) (i : ι) (z : H ⊗[k] H) :
    rightTensorCoordinate b i ((Coalgebra.comul (R := k)).rTensor H z) =
      Coalgebra.comul (rightTensorCoordinate b i z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a h => simp only [LinearMap.rTensor_tmul, rightTensorCoordinate_tmul, map_smul]

omit [Coalgebra k H] in
private theorem rightTensorCoordinate_assoc_symm (b : Basis ι k H) (i : ι) (a : H)
    (z : H ⊗[k] H) :
    rightTensorCoordinate b i ((TensorProduct.assoc k H H H).symm (a ⊗ₜ[k] z)) =
      a ⊗ₜ[k] rightTensorCoordinate b i z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul x y => simp only [TensorProduct.assoc_symm_tmul, rightTensorCoordinate_tmul,
      TensorProduct.tmul_smul]

end Coordinates

/-- Every element of the regular right comodule lies in a finite-dimensional
subspace stable under the right coaction. -/
theorem exists_finite_rightCoaction_span (x : H) :
    ∃ V : Submodule k H, Module.Finite k V ∧ x ∈ V ∧
      ∀ y ∈ V, ∃ z : V ⊗[k] H, V.subtype.rTensor H z = Coalgebra.comul y := by
  classical
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := k) (M := H)
  let w := (TensorProduct.equivFinsuppOfBasisRight b) (Coalgebra.comul (R := k) x)
  have hs : Coalgebra.comul (R := k) x = ∑ j ∈ w.support, w j ⊗ₜ[k] b j := by
    have h := (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply (Coalgebra.comul (R := k) x)
    change (TensorProduct.equivFinsuppOfBasisRight b).symm w = Coalgebra.comul (R := k) x at h
    simpa only [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum] using h.symm
  let V := Submodule.span k (Set.range fun i : w.support => w i)
  have hV (i : ι) (hi : i ∈ w.support) : w i ∈ V :=
    Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  have hFinite : Module.Finite k V := Module.Finite.iff_fg.mpr (Submodule.fg_span (Set.finite_range _))
  have hx : x ∈ V := by
    have h := congrArg (TensorProduct.rid k H) (Coalgebra.lTensor_counit_comul (R := k) x)
    rw [hs] at h
    have hSum : ∑ j ∈ w.support, Coalgebra.counit (R := k) (b j) • w j = x := by
      simpa only [map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, one_smul] using h
    rw [← hSum]
    exact V.sum_mem fun j hj => V.smul_mem _ (hV j hj)
  refine ⟨V, hFinite, hx, ?_⟩
  let W := LinearMap.range (V.subtype.rTensor H)
  have hStable : V ≤ W.comap (Coalgebra.comul (R := k)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have h := congrArg (rightTensorCoordinate (M := H ⊗[k] H) b (i : ι))
      (Coalgebra.coassoc_symm_apply (R := k) x)
    rw [rightTensorCoordinate_comul_rTensor,
      show rightTensorCoordinate b (i : ι) (Coalgebra.comul (R := k) x) = w i from rfl, hs] at h
    have hComul : Coalgebra.comul (R := k) (w i) =
        ∑ j ∈ w.support, w j ⊗ₜ[k] rightTensorCoordinate b (i : ι) (Coalgebra.comul (R := k) (b j)) := by
      simpa only [map_sum, LinearMap.lTensor_tmul, rightTensorCoordinate_assoc_symm] using h.symm
    change Coalgebra.comul (R := k) (w i) ∈ W
    rw [hComul]
    apply W.sum_mem
    intro j hj
    exact ⟨(⟨w j, hV j hj⟩ : V) ⊗ₜ[k] rightTensorCoordinate b (i : ι) (Coalgebra.comul (R := k) (b j)), rfl⟩
  intro y hy
  exact hStable hy

/-- A finite subset of a coalgebra is contained in a finite-dimensional right subcomodule. -/
theorem exists_finite_rightCoaction_span_finset (s : Finset H) :
    ∃ V : Submodule k H, Module.Finite k V ∧ (∀ x ∈ s, x ∈ V) ∧
      ∀ y ∈ V, ∃ z : V ⊗[k] H, V.subtype.rTensor H z = Coalgebra.comul y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨⊥, Module.Finite.iff_fg.mpr Submodule.fg_bot, by simp, ?_⟩
    intro y hy
    have hy₀ : y = 0 := by simpa only [Submodule.mem_bot] using hy
    exact ⟨0, by simp only [hy₀, map_zero]⟩
  | insert a s _ ih =>
    obtain ⟨V, hV, hs, hStableV⟩ := ih
    obtain ⟨W, hW, ha, hStableW⟩ := exists_finite_rightCoaction_span (k := k) a
    letI := hV
    letI := hW
    refine ⟨V ⊔ W, inferInstance, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (le_sup_right : W ≤ V ⊔ W) ha
      · exact (le_sup_left : V ≤ V ⊔ W) (hs x hx)
    · intro y hy
      obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨x, hx⟩ := hStableV v hv
      obtain ⟨z, hz⟩ := hStableW w hw
      refine ⟨(Submodule.inclusion (le_sup_left : V ≤ V ⊔ W)).rTensor H x +
        (Submodule.inclusion (le_sup_right : W ≤ V ⊔ W)).rTensor H z, ?_⟩
      simp only [map_add, ← LinearMap.rTensor_comp_apply, Submodule.subtype_comp_inclusion, hx, hz]

end WideE
