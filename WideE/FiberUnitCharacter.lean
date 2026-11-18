import WideE.Comparison
import DomainUnitCharacters
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Inverse tensors with independent numerical coefficients determine one character. -/

open scoped TensorProduct BigOperators
open TensorProduct StrictEUnit

noncomputable section

namespace WideE

variable {k L H : Type*} [Field k] [Field L] [Algebra k L]
  [CommRing H] [Bialgebra k H]

omit [Bialgebra k H] in
/-- Evaluating the two coordinate vectors yields inverse numerical tensors
when their coordinate product is the unit vector. -/
theorem inverse_tensor_of_coordinateProduct [Algebra k H]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → L) (b : κ → L) (c : ι → ι → κ → k) (d : κ → k)
    (hProd : ∀ i j, a i * a j = ∑ l, c i j l • b l)
    (hOne : (∑ l, d l • b l) = 1) (X Y : ι → H)
    (hXY : coordinateProduct (fun i j l => algebraMap k H (c i j l)) X Y = algebraMap k H ∘ d) :
    (∑ i, a i ⊗ₜ[k] X i) * (∑ i, a i ⊗ₜ[k] Y i) = 1 := by
  calc
    _ = ∑ i, ∑ j, (a i * a j) ⊗ₜ[k] (X i * Y j) := by
      simp only [Finset.sum_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul]
      exact Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ l, b l ⊗ₜ[k] (X i * (Y j * algebraMap k H (c i j l))) := by
      simp only [hProd, sum_tmul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      rw [TensorProduct.smul_tmul, Algebra.smul_def]
      congr 1
      ring
    _ = ∑ l, b l ⊗ₜ[k] coordinateProduct (fun i j l => algebraMap k H (c i j l)) X Y l := by
      simp only [coordinateProduct_apply, tmul_sum]
      calc
        _ = ∑ i, ∑ l, ∑ j, b l ⊗ₜ[k] (X i * (Y j * algebraMap k H (c i j l))) :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
        _ = _ := Finset.sum_comm
    _ = ∑ l, (d l • b l) ⊗ₜ[k] (1 : H) := by
      rw [hXY]
      apply Finset.sum_congr rfl
      intro l _
      rw [Function.comp_apply, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    _ = 1 := by rw [← sum_tmul, hOne, Algebra.TensorProduct.one_def]

private def extendCounit : L ⊗[k] H →ₐ[k] L :=
  Algebra.TensorProduct.lift (AlgHom.id k L)
    ((Algebra.ofId k L).comp (Bialgebra.counitAlgHom k H)) (fun _ _ => Commute.all _ _)

@[simp] private theorem extendCounit_tmul (a : L) (b : H) :
    extendCounit (a ⊗ₜ[k] b) = a * algebraMap k L (Bialgebra.counitAlgHom k H b) := rfl

private theorem exists_normalized_pure [IsAlgClosed k] [IsDomain H]
    (u : (L ⊗[k] H)ˣ) : ∃ b : H, Bialgebra.counitAlgHom k H b = 1 ∧
      (u : L ⊗[k] H) = extendCounit (u : L ⊗[k] H) ⊗ₜ[k] b := by
  obtain ⟨a, b, hab⟩ := tensor_unit_is_pure u
  let ε := Bialgebra.counitAlgHom k H
  have hb : ε b ≠ 0 := by
    intro h
    have hu := (Units.map extendCounit.toMonoidHom u).ne_zero
    change extendCounit (u : L ⊗[k] H) ≠ 0 at hu
    rw [hab, extendCounit_tmul, show Bialgebra.counitAlgHom k H b = 0 from h, map_zero, mul_zero] at hu
    exact hu rfl
  refine ⟨(ε b)⁻¹ • b, ?_, ?_⟩
  · change ε ((ε b)⁻¹ • b) = 1
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hb]
  · rw [hab, extendCounit_tmul, mul_comm a, ← Algebra.smul_def,
      TensorProduct.smul_tmul, smul_smul, mul_inv_cancel₀ hb, one_smul]

private theorem tensor_sum_injective_of_linearIndependent {ι : Type*} [Fintype ι]
    (a : ι → L) (ha : LinearIndependent k a) :
    Function.Injective (fun b : ι → H => ∑ i, a i ⊗ₜ[k] b i) := by
  classical
  intro b c h
  funext i
  let ℓ : Submodule.span k (Set.range a) →ₗ[k] k := (Finsupp.lapply i).comp ha.repr
  obtain ⟨f, hf⟩ := ℓ.exists_extend
  have hEval (j : ι) : f (a j) = if j = i then 1 else 0 := by
    let q : Submodule.span k (Set.range a) := ⟨a j, Submodule.subset_span ⟨j, rfl⟩⟩
    have hq := LinearMap.congr_fun hf q
    change f (a j) = ha.repr q i at hq
    simpa only [ha.repr_eq_single j q rfl, Finsupp.single_apply] using hq
  have hh := congrArg (fun t : L ⊗[k] H => TensorProduct.lid k H (f.rTensor H t)) h
  simpa [hEval, ite_smul] using hh

private theorem coefficients_of_normalized_tensor {ι : Type*} [Fintype ι]
    (a : ι → L) (ha : LinearIndependent k a) (x : ι → k) (b : ι → H)
    (hε : ∀ i, Bialgebra.counitAlgHom k H (b i) = x i) (z : H)
    (hPure : (∑ i, a i ⊗ₜ[k] b i) = extendCounit (∑ i, a i ⊗ₜ[k] b i) ⊗ₜ[k] z) :
    ∀ i, b i = x i • z := by
  have h : (∑ i, a i ⊗ₜ[k] b i) = ∑ i, a i ⊗ₜ[k] (x i • z) := by
    rw [hPure]
    simp only [map_sum, extendCounit_tmul, hε, sum_tmul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]
  exact congrFun (tensor_sum_injective_of_linearIndependent a ha h)

/-- Inverse numerical tensors expressed in independent coordinates give a
character over the original field and opposite weights in those coordinates. -/
theorem inverse_tensor_coordinates_have_character [IsAlgClosed k] [IsDomain H]
    {ι : Type*} [Fintype ι] (a : ι → L) (ha : LinearIndependent k a)
    (x y : ι → k) (X Y : ι → H)
    (hX : ∀ i, Bialgebra.counitAlgHom k H (X i) = x i)
    (hY : ∀ i, Bialgebra.counitAlgHom k H (Y i) = y i)
    (hXY : (∑ i, a i ⊗ₜ[k] X i) * (∑ i, a i ⊗ₜ[k] Y i) = 1) :
    ∃ χ : Hˣ, Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H) ∧
      (∀ i, X i = x i • (χ : H)) ∧ (∀ i, Y i = y i • (↑χ⁻¹ : H)) := by
  let u := ∑ i, a i ⊗ₜ[k] X i
  let v := ∑ i, a i ⊗ₜ[k] Y i
  let w : (L ⊗[k] H)ˣ := ⟨u, v, hXY, (mul_comm v u).trans hXY⟩
  obtain ⟨χ, hχε, hχ⟩ := exists_normalized_pure w
  obtain ⟨ψ, _, hψ⟩ := exists_normalized_pure w⁻¹
  change u = extendCounit u ⊗ₜ[k] χ at hχ
  change v = extendCounit v ⊗ₜ[k] ψ at hψ
  have hε : extendCounit u * extendCounit v = 1 := by
    rw [← map_mul, show u * v = 1 from hXY, map_one]
  have hχψ : χ * ψ = 1 := by
    apply Algebra.TensorProduct.includeRight_injective (A := L) (algebraMap k L).injective
    change (1 : L) ⊗ₜ[k] (χ * ψ) = (1 : L) ⊗ₜ[k] (1 : H)
    change u * v = 1 at hXY
    rw [hχ, hψ, Algebra.TensorProduct.tmul_mul_tmul, hε] at hXY
    exact hXY
  let g : Hˣ := ⟨χ, ψ, hχψ, (mul_comm ψ χ).trans hχψ⟩
  have hg : counitUnit (k := k) g = 1 := Units.ext hχε
  have hn : normalizedRegularUnit (k := k) g = g := by
    rw [normalizedRegularUnit, hg, inv_one]
    change Units.map (algebraMap k H).toMonoidHom 1 * g = g
    rw [map_one, one_mul]
  have hΔ := normalized_unit_grouplike_of_domain (k := k) g
  rw [hn] at hΔ
  exact ⟨g, hΔ, coefficients_of_normalized_tensor a ha x X hX χ hχ,
    coefficients_of_normalized_tensor a ha y Y hY ψ hψ⟩

end WideE
