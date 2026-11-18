import WideE.HopfCotangentBaseChange
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.LinearAlgebra.Dual.Basis

/-! Base change of an actual generating Hopf matrix and its tangent Lie algebra. -/

noncomputable section

open scoped TensorProduct Matrix
open StrictEUnit Module

namespace WideE

variable {k F H : Type*} [Field k] [Field F] [Algebra k F] [CommRing H] [HopfAlgebra k H]

local notation "H'" => (F ⊗[k] H)
local notation "r" => (Algebra.TensorProduct.includeRight : H →ₐ[k] H')

attribute [local instance] hopfScalarExtension

section Matrix

variable {ι : Type*} [Fintype ι]

/-- The extended matrix has the same corepresentation relations. -/
theorem hopfMatrixRelations_baseChange [DecidableEq ι] (U : Matrix ι ι H)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U i j) = ∑ l, U i l ⊗ₜ[k] U l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U i j) = if i = j then 1 else 0) :
    (∀ i j, Coalgebra.comul (R := F) ((U.map r) i j) = ∑ l, (U.map r) i l ⊗ₜ[F] (U.map r) l j) ∧
      (∀ i j, Coalgebra.counit (R := F) ((U.map r) i j) = if i = j then 1 else 0) := by
  constructor
  · intro i j
    change baseChangeComul F ((1 : F) ⊗ₜ[k] U i j) =
      ∑ l, ((1 : F) ⊗ₜ[k] U i l) ⊗ₜ[F] ((1 : F) ⊗ₜ[k] U l j)
    rw [baseChangeComul_tmul, hD, TensorProduct.tmul_sum, map_sum]
    simp only [algebraTensorBaseChangeEquiv_symm_tmul]
  · intro i j
    change Bialgebra.counitAlgHom F H' ((1 : F) ⊗ₜ[k] U i j) = _
    rw [hopfScalarExtension_counit_tmul, one_mul]
    change algebraMap k F (Coalgebra.counit (R := k) (U i j)) = _
    rw [he]
    simp only [apply_ite (algebraMap k F), map_one, map_zero]

omit [Fintype ι] in
/-- The same coefficients generate after scalar extension. -/
theorem hopfMatrix_generates_baseChange (U : Matrix ι ι H)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U ij.1 ij.2) = ⊤) :
    Algebra.adjoin F (Set.range fun ij : ι × ι => (U.map r) ij.1 ij.2) = ⊤ := by
  let S := Algebra.adjoin F (Set.range fun ij : ι × ι => (U.map r) ij.1 ij.2)
  have hSub : Algebra.adjoin k (Set.range fun ij : ι × ι => U ij.1 ij.2) ≤
      (S.restrictScalars k).comap r := by
    apply Algebra.adjoin_le
    rintro _ ⟨ij, rfl⟩
    exact Algebra.subset_adjoin ⟨ij, rfl⟩
  rw [hGen] at hSub
  suffices h : ∀ z : H', z ∈ S from top_unique fun z _ => h z
  intro z
  change z ∈ S
  induction z using TensorProduct.induction_on with
  | zero => exact zero_mem S
  | add x y hx hy => exact add_mem hx hy
  | tmul a x =>
    have hx : (1 : F) ⊗ₜ[k] x ∈ S := hSub (show x ∈ (⊤ : Subalgebra k H) from trivial)
    rw [← mul_one a, ← smul_eq_mul, ← TensorProduct.smul_tmul']
    exact S.smul_mem hx a

end Matrix

section Lie

variable [Algebra.FiniteType k H]

local notation "𝔤" => hopfInvariantDerivations k H
local notation "𝔤'" => hopfInvariantDerivations F H'
local notation "C" => HopfCotangent k H

private def invariantDerivationToScalarLieVector : F ⊗[k] 𝔤 ≃ₗ[F] HopfLieVector k H F := by
  letI := hopfCotangent_finiteDimensional k H
  let b := finBasis k C
  let e := hopfLieVectorInvariantDerivations (k := k) (H := H)
  exact (((b.dualBasis.map e).baseChange F).equivFun).trans (b.constr F)

private theorem invariantDerivationToScalarLieVector_tmul (a : F) (D : 𝔤) :
    invariantDerivationToScalarLieVector (a ⊗ₜ[k] D) =
      a • (Algebra.ofId k F).toLinearMap.comp (hopfLieVectorInvariantDerivations.symm D) := by
  letI := hopfCotangent_finiteDimensional k H
  let b := finBasis k C
  let e := hopfLieVectorInvariantDerivations (k := k) (H := H)
  apply b.ext
  intro i
  change b.constr F (((b.dualBasis.map e).baseChange F).equivFun (a ⊗ₜ[k] D)) (b i) = _
  rw [Basis.constr_basis, Basis.equivFun_apply, Basis.baseChange_repr_tmul,
    Basis.map_repr, LinearEquiv.trans_apply, Basis.dualBasis_repr]
  change (e.symm D (b i)) • a = a * algebraMap k F (e.symm D (b i))
  rw [Algebra.smul_def, mul_comm]

/-- Scalar extension of invariant derivations as a linear equivalence. -/
def hopfInvariantDerivationsBaseChangeLinear : F ⊗[k] 𝔤 ≃ₗ[F] 𝔤' :=
  invariantDerivationToScalarLieVector.trans
    (hopfLieVectorBaseChange.trans hopfLieVectorInvariantDerivations)

theorem hopfInvariantDerivationsBaseChangeLinear_tmul (a : F) (D : 𝔤) :
    hopfInvariantDerivationsBaseChangeLinear (a ⊗ₜ[k] D) =
      hopfLieVectorInvariantDerivations (hopfLieVectorBaseChange (F := F)
        (a • (Algebra.ofId k F).toLinearMap.comp (hopfLieVectorInvariantDerivations.symm D))) := by
  change hopfLieVectorInvariantDerivations
    (hopfLieVectorBaseChange (F := F) (invariantDerivationToScalarLieVector (a ⊗ₜ[k] D))) = _
  rw [invariantDerivationToScalarLieVector_tmul]

/-- The tangent matrix of a pure tensor extends each coefficient and multiplies by its scalar. -/
theorem hopfLieMatrix_baseChange_tmul {ι : Type*} (U : Matrix ι ι H) (a : F) (D : 𝔤) :
    hopfLieMatrix (U.map r) (hopfInvariantDerivationsBaseChangeLinear (a ⊗ₜ[k] D)) =
      a • (hopfLieMatrix U D).map (algebraMap k F) := by
  rw [hopfInvariantDerivationsBaseChangeLinear_tmul, hopfLieMatrix_invariantDerivations,
    hopfCotangentMatrix_baseChange]
  have hD := hopfLieMatrix_invariantDerivations U
    ((hopfLieVectorInvariantDerivations (k := k) (H := H)).symm D)
  rw [LinearEquiv.apply_symm_apply] at hD
  rw [hD]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1500000 in
set_option synthInstance.maxHeartbeats 120000 in
/-- The scalar extension of the tangent Lie algebra is the actual invariant
derivation algebra of the extended Hopf coordinates. -/
def hopfInvariantDerivationsBaseChange (U : Matrix ι ι H)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U i j) = ∑ l, U i l ⊗ₜ[k] U l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U ij.1 ij.2) = ⊤) :
    F ⊗[k] 𝔤 ≃ₗ⁅F⁆ 𝔤' := by
  let f : F ⊗[k] 𝔤 ≃ₗ[F] 𝔤' := hopfInvariantDerivationsBaseChangeLinear
  have hf₀ : f 0 = 0 := f.map_zero
  have hfAdd (x y : F ⊗[k] 𝔤) : f (x + y) = f x + f y := f.map_add x y
  refine { f with map_lie' := ?_ }
  intro x y
  change f ⁅x, y⁆ = ⁅f x, f y⁆
  induction x using TensorProduct.induction_on with
  | zero => simp only [zero_lie, hf₀]
  | add x₁ x₂ hx₁ hx₂ => simp only [add_lie, hfAdd, hx₁, hx₂]
  | tmul a x =>
    induction y using TensorProduct.induction_on with
    | zero =>
      have h : ⁅a ⊗ₜ[k] x, (0 : F ⊗[k] 𝔤)⁆ = 0 :=
        lie_zero (M := F ⊗[k] 𝔤) (a ⊗ₜ[k] x)
      simp only [h, hf₀, lie_zero]
    | add y₁ y₂ hy₁ hy₂ =>
      have h : ⁅a ⊗ₜ[k] x, y₁ + y₂⁆ = ⁅a ⊗ₜ[k] x, y₁⁆ + ⁅a ⊗ₜ[k] x, y₂⁆ :=
        lie_add (a ⊗ₜ[k] x) y₁ y₂
      simp only [h, hfAdd, hy₁, hy₂, lie_add]
    | tmul b y =>
      let U' := U.map r
      let ψ := hopfLieMatrixHom U' (hopfMatrixRelations_baseChange U hD he).1
      have hψ (c : F) (D : 𝔤) : ψ (f (c ⊗ₜ[k] D)) = c • (hopfLieMatrix U D).map (algebraMap k F) :=
        hopfLieMatrix_baseChange_tmul U c D
      apply hopfLieMatrixHom_injective U' (hopfMatrixRelations_baseChange U hD he).1
        (hopfMatrix_generates_baseChange U hGen)
      change ψ (f ⁅a ⊗ₜ[k] x, b ⊗ₜ[k] y⁆) = ψ ⁅f (a ⊗ₜ[k] x), f (b ⊗ₜ[k] y)⁆
      rw [LieAlgebra.ExtendScalars.bracket_tmul, LieHom.map_lie, hψ, hψ, hψ,
        smul_lie, lie_smul, smul_smul]
      congr 1
      change (algebraMap k F).mapMatrix (hopfLieMatrixHom U hD ⁅x, y⁆) =
        ⁅(algebraMap k F).mapMatrix (hopfLieMatrixHom U hD x),
          (algebraMap k F).mapMatrix (hopfLieMatrixHom U hD y)⁆
      rw [LieHom.map_lie, Ring.lie_def, Ring.lie_def, map_sub, map_mul, map_mul]

@[simp] theorem hopfInvariantDerivationsBaseChange_apply (U : Matrix ι ι H)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U i j) = ∑ l, U i l ⊗ₜ[k] U l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U ij.1 ij.2) = ⊤)
    (x : F ⊗[k] 𝔤) :
    hopfInvariantDerivationsBaseChange U hD he hGen x = hopfInvariantDerivationsBaseChangeLinear x := rfl

end Lie

end WideE
