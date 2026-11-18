import WideE.LieMatrixCentralizer
import WideE.InvariantIdeal
import Mathlib.Algebra.Lie.Abelian
import NilpotentMatrixExpDerivative

/-! Central Lie directions are fixed by the actual adjoint action of a connected affine group. -/

noncomputable section

open LieAlgebra
open StrictEUnit
open scoped Matrix TensorProduct

namespace WideE

section Universal

variable {k H ι : Type*} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsDomain H] [Fintype ι] [DecidableEq ι]

/-- A constant matrix commuting with every tangent matrix commutes with the universal group matrix. -/
theorem commute_hopfMatrix_of_commute_all_tangents (U : Matrix ι ι H)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U i j) = ∑ l, U i l ⊗ₜ[k] U l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U i j) = if i = j then 1 else 0)
    (Z : Matrix ι ι k)
    (hZ : ∀ D : hopfInvariantDerivations k H, Commute (hopfLieMatrix U D) Z) :
    Commute U ((algebraMap k H).mapMatrix Z) := by
  classical
  let φ := (algebraMap k H).mapMatrix (m := ι)
  let ε := (Bialgebra.counitAlgHom k H).toRingHom.mapMatrix (m := ι)
  let W := U * φ Z - φ Z * U
  have hεU : ε U = 1 := Matrix.ext fun i j => (he i j).trans Matrix.one_apply.symm
  have hεZ : ε (φ Z) = Z := Matrix.ext fun i j => (Bialgebra.counitAlgHom k H).commutes _
  have hεW : ε W = 0 := by
    simp only [W, map_sub, map_mul, hεU, hεZ, one_mul, mul_one, sub_self]
  have hW (D : hopfInvariantDerivations k H) :
      matrixDerivative D.val W = W * φ (hopfLieMatrix U D) := by
    let N := φ (hopfLieMatrix U D)
    have hN : matrixDerivative D.val U = U * N :=
      Matrix.ext fun i j => hopfInvariantDerivation_matrixCoefficient U hD D i j
    have hComm : Commute N (φ Z) := (hZ D).map φ
    have hSub (x y : Matrix ι ι H) :
        matrixDerivative D.val (x - y) = matrixDerivative D.val x - matrixDerivative D.val y :=
      Matrix.ext fun i j => map_sub D.val (x i j) (y i j)
    change matrixDerivative D.val (U * φ Z - φ Z * U) = (U * φ Z - φ Z * U) * N
    rw [hSub, matrixDerivative_mul, matrixDerivative_mul]
    simp only [φ, matrixDerivative_constant, zero_mul, mul_zero, zero_add, add_zero]
    rw [hN]
    simp only [sub_mul, mul_assoc]
    exact congrArg (fun X => U * X - φ Z * (U * N)) hComm.eq
  let I : Ideal H := Ideal.span (Set.range fun ij : ι × ι => W ij.1 ij.2)
  have hI : I ≤ hopfAugmentationIdeal k H := by
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    change Bialgebra.counitAlgHom k H (W i j) = 0
    exact congrArg (fun X : Matrix ι ι k => X i j) hεW
  have hStable (D : hopfInvariantDerivations k H) (a : H) (ha : a ∈ I) : D.val a ∈ I := by
    refine Submodule.span_induction (p := fun a _ => D.val a ∈ I) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨⟨i, j⟩, rfl⟩
      have h := congrArg (fun X : Matrix ι ι H => X i j) (hW D)
      change D.val (W i j) = ∑ l, W i l * φ (hopfLieMatrix U D) l j at h
      rw [h]
      exact I.sum_mem fun l _ => I.mul_mem_right _ (Ideal.subset_span ⟨(i, l), rfl⟩)
    · change D.val 0 ∈ I
      rw [map_zero]
      exact I.zero_mem
    · intro x y _ _ hx hy
      rw [map_add]
      exact I.add_mem hx hy
    · intro r x hx hd
      change D.val (r * x) ∈ I
      rw [D.val.leibniz, Algebra.id.smul_eq_mul, Algebra.id.smul_eq_mul]
      exact I.add_mem (I.mul_mem_left _ hd) (I.mul_mem_right _ hx)
  have hZero := hopfInvariantIdeal_eq_bot I hI hStable
  apply sub_eq_zero.mp
  apply Matrix.ext
  intro i j
  have h : W i j ∈ I := Ideal.subset_span ⟨(i, j), rfl⟩
  rw [hZero] at h
  exact h

end Universal

section Points

variable {k H A ι η : Type*} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsDomain H] [CommRing A] [Algebra k A]
  [Fintype ι] [DecidableEq ι] [Fintype η]

local notation "𝔤" => hopfInvariantDerivations k H
local notation "E" => hopfLieVectorInvariantDerivations (k := k) (H := H)

/-- The actual group fixes all scalar combinations of central Lie vectors,
over any coefficient algebra. -/
theorem hopfAdjoint_fixes_sum_centralDirections (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (p : H →ₐ[k] A) (z : η → center k 𝔤) (c : η → A) :
    let y : HopfLieVector k H A := ∑ i, c i •
      (Algebra.ofId k A).toLinearMap.comp ((E).symm (z i))
    hopfAdjoint p y = y := by
  let ρ := hopfLieMatrixHom U.val hD
  let φ := (algebraMap k A).mapMatrix (m := ι)
  let P := hopfPointMatrix U hD he p
  let y : HopfLieVector k H A := ∑ i, c i •
    (Algebra.ofId k A).toLinearMap.comp ((E).symm (z i))
  have hMat (i : η) : Commute P.val (φ (ρ (z i))) := by
    have h := commute_hopfMatrix_of_commute_all_tangents U.val hD he (ρ (z i)) (fun D => by
      apply sub_eq_zero.mp
      change ⁅ρ D, ρ (z i)⁆ = 0
      rw [← LieHom.map_lie, (z i).property, LieHom.map_zero])
    have h' := h.map p.toRingHom.mapMatrix
    have hComm : p.toRingHom.mapMatrix ((algebraMap k H).mapMatrix (ρ (z i))) =
        φ (ρ (z i)) := Matrix.ext fun _ _ => p.commutes _
    change Commute P.val (p.toRingHom.mapMatrix ((algebraMap k H).mapMatrix (ρ (z i)))) at h'
    rwa [hComm] at h'
  have hY (i : η) : hopfCotangentMatrix U.val ((Algebra.ofId k A).toLinearMap.comp
      ((E).symm (z i))) = φ (ρ (z i)) := by
    ext l m
    change algebraMap k A ((E).symm (z i) (hopfCotangentProjection k H (U.val l m))) =
      algebraMap k A ((ρ (z i)) l m)
    congr 1
    have h := congrArg (fun M : Matrix ι ι k => M l m)
      (hopfLieMatrix_invariantDerivations U.val ((E).symm (z i)))
    rwa [(E).apply_symm_apply, eq_comm] at h
  have hYmat : hopfCotangentMatrix U.val y = ∑ i, c i • φ (ρ (z i)) := by
    ext l m
    simp only [y, hopfCotangentMatrix, LinearMap.sum_apply, LinearMap.smul_apply,
      Matrix.sum_apply, Matrix.smul_apply]
    refine Finset.sum_congr rfl fun i _ => congrArg (fun a : A => c i • a) ?_
    exact congrArg (fun M : Matrix ι ι A => M l m) (hY i)
  have hC : Commute P.val (hopfCotangentMatrix U.val y) := by
    rw [hYmat]
    exact Commute.sum_right _ _ _ fun i _ => (hMat i).smul_right (c i)
  change hopfAdjoint p y = y
  apply hopfCotangentMatrix_injective U.val hGen
  rw [hopfCotangentMatrix_adjoint]
  change P.val * hopfCotangentMatrix U.val y * P.inv = hopfCotangentMatrix U.val y
  rw [hC.eq, mul_assoc, P.val_inv, mul_one]

end Points

end WideE
