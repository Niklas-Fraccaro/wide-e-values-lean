import Mathlib.Algebra.Central.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Scalar extension of a central division algebra is simple

Choose a nonzero element in a two-sided ideal with minimum support in a basis of
the scalar field. Normalize one coefficient in the division algebra to one.
Every commutator with the division algebra has smaller support, so all
coefficients are central. This gives an invertible element of the ideal.
-/

noncomputable section

open scoped TensorProduct BigOperators

namespace WideE

section Coordinates

variable {K L D ι : Type*} [Field K] [Field L] [Algebra K L]
variable [DivisionRing D] [Algebra K D] [DecidableEq ι]

private theorem tensorCoeff_mul_right (b : Basis ι K L) (x : L ⊗[K] D) (d : D) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (x * (1 ⊗ₜ[K] d)) i =
      TensorProduct.equivFinsuppOfBasisLeft b x i * d := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a z =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      simp only [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, smul_mul_assoc]
  | add x y hx hy =>
      simp only [add_mul, map_add, Finsupp.add_apply, hx, hy]

private theorem tensorCoeff_mul_left (b : Basis ι K L) (x : L ⊗[K] D) (d : D) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b ((1 ⊗ₜ[K] d) * x) i =
      d * TensorProduct.equivFinsuppOfBasisLeft b x i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a z =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      simp only [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, mul_smul_comm]
  | add x y hx hy =>
      simp only [mul_add, map_add, Finsupp.add_apply, hx, hy]

end Coordinates

variable {K L D : Type*} [Field K] [Field L] [Algebra K L]
variable [DivisionRing D] [Algebra K D]

private theorem tensor_nontrivial : Nontrivial (L ⊗[K] D) := by
  classical
  refine ⟨⟨(1 : L) ⊗ₜ[K] (1 : D), 0, ?_⟩⟩
  let b := Module.Free.chooseBasis K L
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := D) b
  intro h
  apply (one_ne_zero : (1 : L) ≠ 0)
  apply b.repr.injective
  ext i
  have hi := congrArg (fun z : L ⊗[K] D => e z i) h
  change TensorProduct.equivFinsuppOfBasisLeft b ((1 : L) ⊗ₜ[K] (1 : D)) i = e 0 i at hi
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Algebra.smul_def, mul_one,
    map_zero, Finsupp.zero_apply] at hi
  rw [map_zero, Finsupp.zero_apply]
  exact (algebraMap K D).injective (hi.trans (map_zero _).symm)

private theorem scalarExtension_isSimple_of_center
    (hCentral : ∀ z : D, (∀ d : D, z * d = d * z) → ∃ c : K, algebraMap K D c = z) :
    IsSimpleRing (L ⊗[K] D) := by
  classical
  letI : Nontrivial (L ⊗[K] D) := tensor_nontrivial
  let b := Module.Free.chooseBasis K L
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := D) b
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  by_cases hI : I = ⊥
  · exact Or.inl hI
  · right
    obtain ⟨u, huI, hu₀⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI : ⊥ < I)
    have hExists : ∃ n : ℕ, ∃ x : L ⊗[K] D, x ∈ I ∧ x ≠ 0 ∧ (e x).support.card = n :=
      ⟨(e u).support.card, u, huI, hu₀, rfl⟩
    let n := Nat.find hExists
    obtain ⟨x, hxI, hx₀, hCard⟩ := Nat.find_spec hExists
    have hMin {z : L ⊗[K] D} (hzI : z ∈ I) (hz₀ : z ≠ 0) : n ≤ (e z).support.card :=
      Nat.find_min' hExists ⟨z, hzI, hz₀, rfl⟩
    have hNZ : ∃ i, e x i ≠ 0 := by
      by_contra h
      push_neg at h
      apply hx₀
      apply e.injective
      ext i
      simpa only [map_zero, Finsupp.zero_apply] using h i
    obtain ⟨i₀, hi₀⟩ := hNZ
    let y := x * (1 ⊗ₜ[K] (e x i₀)⁻¹)
    have hyI : y ∈ I := I.mul_mem_right _ _ hxI
    have hYcoeff (i) : e y i = e x i * (e x i₀)⁻¹ := tensorCoeff_mul_right b x _ i
    have hy₁ : e y i₀ = 1 := (hYcoeff i₀).trans (mul_inv_cancel₀ hi₀)
    have hy₀ : y ≠ 0 := by
      intro h
      rw [h, map_zero, Finsupp.zero_apply] at hy₁
      exact zero_ne_one hy₁
    have hCommute (d : D) : y * (1 ⊗ₜ[K] d) - (1 ⊗ₜ[K] d) * y = 0 := by
      let z := y * (1 ⊗ₜ[K] d) - (1 ⊗ₜ[K] d) * y
      have hzCoeff (i) : e z i = e y i * d - d * e y i := by
        dsimp only [z]
        rw [map_sub, Finsupp.sub_apply]
        exact congrArg₂ (· - ·) (tensorCoeff_mul_right b y d i) (tensorCoeff_mul_left b y d i)
      have hzSub : (e z).support ⊂ (e x).support := by
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · intro i hi
          rw [Finsupp.mem_support_iff] at hi ⊢
          intro h
          apply hi
          rw [hzCoeff, hYcoeff, h, zero_mul, zero_mul, mul_zero, sub_zero]
        · intro h
          have hi : i₀ ∈ (e x).support := Finsupp.mem_support_iff.mpr hi₀
          rw [← h, Finsupp.mem_support_iff, hzCoeff, hy₁, one_mul, mul_one, sub_self] at hi
          exact hi rfl
      have hzI : z ∈ I := I.sub_mem (I.mul_mem_right _ _ hyI) (I.mul_mem_left _ _ hyI)
      by_contra hz₀
      exact (Nat.not_le_of_lt ((Finset.card_lt_card hzSub).trans_eq hCard)) (hMin hzI hz₀)
    have hC (i) : ∃ c : K, algebraMap K D c = e y i := by
      apply hCentral
      intro d
      apply sub_eq_zero.mp
      have h : e (y * (1 ⊗ₜ[K] d) - (1 ⊗ₜ[K] d) * y) i = e 0 i :=
        congrArg (fun z : L ⊗[K] D => e z i) (hCommute d)
      rw [map_sub, Finsupp.sub_apply, map_zero, Finsupp.zero_apply] at h
      exact (congrArg₂ (· - ·) (tensorCoeff_mul_right b y d i)
        (tensorCoeff_mul_left b y d i)).symm.trans h
    choose c hc using hC
    let t : L := ∑ i ∈ (e y).support, c i • b i
    have hY : y = t ⊗ₜ[K] (1 : D) := by
      calc
        y = (e y).sum (fun i d => b i ⊗ₜ[K] d) := by
          rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
          exact (e.symm_apply_apply y).symm
        _ = t ⊗ₜ[K] (1 : D) := by
          dsimp only [Finsupp.sum, t]
          rw [TensorProduct.sum_tmul]
          apply Finset.sum_congr rfl
          intro i _
          rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one, hc]
    have ht : t ≠ 0 := by
      intro h
      exact hy₀ (hY.trans (by rw [h, TensorProduct.zero_tmul]))
    have hY' : y = algebraMap L (L ⊗[K] D) t := hY
    have h := I.mul_mem_left (algebraMap L (L ⊗[K] D) t⁻¹) y hyI
    rw [hY', ← map_mul, inv_mul_cancel₀ ht, map_one] at h
    exact I.one_mem_iff.mp h

/-- Any field extension of a central division algebra is a simple ring. -/
theorem scalarExtension_centralDivision_isSimple [Algebra.IsCentral K D] :
    IsSimpleRing (L ⊗[K] D) := by
  apply scalarExtension_isSimple_of_center
  intro z hz
  have h : z ∈ Subalgebra.center K D := Subalgebra.mem_center_iff.mpr fun d => (hz d).symm
  exact (inferInstance : Algebra.IsCentral K D).out h

end WideE
