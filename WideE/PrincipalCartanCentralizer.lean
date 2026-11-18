import WideE.LieMatrixCentralizer
import WideE.ReductiveCartanTorus
import WideE.Sl2IntegralWeights
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-! The principal Cartan element and the regular points of its Cartan have a toric centralizer. -/

noncomputable section

open scoped Matrix TensorProduct
open LieAlgebra LieModule Module

namespace WideE

section Signs

variable {k ι : Type*} [Field k] [CharZero k] [Fintype ι] [DecidableEq ι]

private theorem matrix_entry_zero_of_weight_ne (w : ι → ℤ) (X : Matrix ι ι k) (n : ℤ)
    (h : ⁅Matrix.diagonal (fun i => (w i : k)), X⁆ = (n : k) • X)
    (i j : ι) (hw : w i - w j ≠ n) : X i j = 0 := by
  have hv := congrArg (fun M : Matrix ι ι k => M i j) h
  change (Matrix.diagonal (fun i => (w i : k)) * X -
    X * Matrix.diagonal (fun i => (w i : k))) i j = ((n : k) • X) i j at hv
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul,
    mul_comm (X i j), ← sub_mul, ← Int.cast_sub] at hv
  have hx : ((w i - w j : ℤ) : k) ≠ (n : k) := fun he => hw (Int.cast_injective he)
  exact (mul_eq_mul_right_iff.mp hv).resolve_left hx

end Signs

section Centralizer

variable {k H Q ι η : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing H] [HopfAlgebra k H] [IsDomain H] [Algebra.FiniteType k H]
  [CommRing Q] [HopfAlgebra k Q] [IsDomain Q]
  [Fintype ι] [DecidableEq ι] [Fintype η] [DecidableEq η]

local notation "𝔤" => (hopfInvariantDerivations k H)
local notation "L" => (HopfLieVector k H k)

set_option maxHeartbeats 1600000 in
omit [DecidableEq η] in
/-- The weight-block centralizer is the torus quotient if the splitting torus contains
the whole zero part of the principal grading, including the center. -/
theorem hopfAdjointCentralizerIdeal_eq_ker_of_principalTriple
    (b : Basis η k (HopfCotangent k H)) (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (S : LieIdeal k 𝔤) (hC : IsCompl S (center k 𝔤))
    {h e f : S} (t : IsSl2Triple h e f) (hS : Module.End.IsSemisimple (ad k S h))
    (s : ι → k) (hDiag : hopfLieMatrix U.val (h : 𝔤) = Matrix.diagonal s)
    (π : H →ₐc[k] Q) (hπ : ∀ i j, i ≠ j → π (U.val i j) = 0)
    (hLiftZero : ∀ x : S, ⁅h, x⁆ = 0 → ∃ z : hopfInvariantDerivations k Q,
      hopfInvariantDerivationsMap π z = (x : 𝔤))
    (hLiftCenter : ∀ x : center k 𝔤, ∃ z : hopfInvariantDerivations k Q,
      hopfInvariantDerivationsMap π z = (x : 𝔤)) :
    hopfAdjointCentralizerIdeal b ((hopfLieVectorInvariantDerivations (k := k) (H := H)).symm h) =
      RingHom.ker (π : H →ₐ[k] Q).toRingHom := by
  classical
  letI := hopfCotangent_finiteDimensional k H
  let E := hopfLieVectorInvariantDerivations (k := k) (H := H)
  letI : FiniteDimensional k 𝔤 := FiniteDimensional.of_surjective E.toLinearMap E.surjective
  letI : FiniteDimensional k S := FiniteDimensional.of_injective S.toSubmodule.subtype Subtype.val_injective
  let T : Matrix ι ι k ≃ₐ[k] End k (ι → k) := Matrix.toLinAlgEquiv'
  let ρ := (T.toLieEquiv.toLieHom.comp (hopfLieMatrixHom U.val hΔ)).comp S.incl
  letI := LieRingModule.compLieHom (ι → k) ρ
  letI := LieModule.compLieHom (ι → k) ρ
  have hInt (i : ι) : ∃ n : ℤ, s i = n := by
    have hn : (Pi.single i (1 : k) : ι → k) ≠ 0 :=
      fun hz => (one_ne_zero : (1 : k) ≠ 0) (by simpa using congrFun hz i)
    apply exists_int_of_sl2Cartan_eigenvector t hn
    change T (hopfLieMatrix U.val (h : 𝔤)) (Pi.single i (1 : k)) = s i • Pi.single i (1 : k)
    rw [hDiag]
    change Matrix.diagonal s *ᵥ Pi.single i (1 : k) = _
    rw [Matrix.diagonal_mulVec_single, mul_one]
    funext j
    by_cases hj : j = i <;> simp [Pi.single_apply, hj, eq_comm, smul_eq_mul]
  choose w hw using hInt
  have hW : hopfLieMatrix U.val (h : 𝔤) = Matrix.diagonal (fun i => (w i : k)) :=
    hDiag.trans (congrArg Matrix.diagonal (funext hw))
  obtain ⟨B, d, hd⟩ := exists_eigenbasis_of_isSemisimple (ad k S h) hS
  have hIntB (i : Fin (finrank k S)) : ∃ n : ℤ, d i = n :=
    exists_int_of_sl2Cartan_eigenvector t (B.ne_zero i) (hd i)
  choose a ha using hIntB
  let Ipos := {i : Fin (finrank k S) // 0 < a i}
  let Ineg := {i : Fin (finrank k S) // a i < 0}
  let v (i : Fin (finrank k S)) : L := E.symm ((B i : S) : 𝔤)
  let vPos (i : Ipos) := v i.val
  let vNeg (i : Ineg) := v i.val
  have hBracket (i : Fin (finrank k S)) :
      ⁅Matrix.diagonal (fun j => (w j : k)), hopfCotangentMatrix U.val (v i)⁆ =
        (a i : k) • hopfCotangentMatrix U.val (v i) := by
    have hL : ⁅h, B i⁆ = (a i : k) • B i := (hd i).trans (by rw [ha])
    have hM := congrArg ((hopfLieMatrixHom U.val hΔ).comp S.incl) hL
    rw [LieHom.map_lie, LieHom.map_smul] at hM
    have hv : hopfCotangentMatrix U.val (v i) = hopfLieMatrix U.val (B i : 𝔤) := by
      rw [← hopfLieMatrix_invariantDerivations, show E (v i) = (B i : 𝔤) from E.apply_symm_apply _]
    simpa only [hv, ← hW] using hM
  have hLow (r : Ipos) (i j : ι) (hij : ¬ w j < w i) : hopfCotangentMatrix U.val (vPos r) i j = 0 :=
    matrix_entry_zero_of_weight_ne w _ _ (hBracket r.val) i j (by have := r.property; omega)
  have hHigh (r : Ineg) (i j : ι) (hij : ¬ w i < w j) : hopfCotangentMatrix U.val (vNeg r) i j = 0 :=
    matrix_entry_zero_of_weight_ne w _ _ (hBracket r.val) i j (by have := r.property; omega)
  let p := hopfLiePullback (A := k) (π : H →ₐ[k] Q) (BialgHomClass.counitAlgHom_comp π)
  have pEq (z : hopfInvariantDerivations k Q) :
      E (p ((hopfLieVectorInvariantDerivations (k := k) (H := Q)).symm z)) =
        hopfInvariantDerivationsMap π z := by
    apply E.symm.injective
    rw [LinearEquiv.symm_apply_apply]
    apply LinearMap.ext
    intro a
    obtain ⟨u, rfl⟩ := hopfCotangentProjection_surjective k H a
    rw [hopfLiePullback_projection, ← hopfLieVectorInvariantDerivations_counit,
      ← hopfLieVectorInvariantDerivations_counit,
      show hopfLieVectorInvariantDerivations ((hopfLieVectorInvariantDerivations (k := k) (H := H)).symm
        (hopfInvariantDerivationsMap π z)) = hopfInvariantDerivationsMap π z from E.apply_symm_apply _,
      show hopfLieVectorInvariantDerivations ((hopfLieVectorInvariantDerivations (k := k) (H := Q)).symm z) = z
        from LinearEquiv.apply_symm_apply _ _, hopfInvariantDerivationsMap_counit]
    rfl
  let G : ((Ipos ⊕ Ineg) → k) →ₗ[k] L := ∑ j,
    (LinearMap.toSpanSingleton k L (Sum.elim vPos vNeg j)).comp (LinearMap.proj j)
  have hG (c : (Ipos ⊕ Ineg) → k) : G c = ∑ j, c j • Sum.elim vPos vNeg j := by
    simp only [G, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.toSpanSingleton_apply]
  let A := p.coprod G
  have hLift (y : 𝔤) (hy : ∃ z : hopfInvariantDerivations k Q, hopfInvariantDerivationsMap π z = y) :
      E.symm y ∈ LinearMap.range A := by
    obtain ⟨z, hz⟩ := hy
    refine ⟨((hopfLieVectorInvariantDerivations (k := k) (H := Q)).symm z, 0), ?_⟩
    rw [LinearMap.coprod_apply, map_zero, add_zero]
    apply E.injective
    rw [pEq, E.apply_symm_apply, hz]
  have hGMem (j : Ipos ⊕ Ineg) : Sum.elim vPos vNeg j ∈ LinearMap.range A := by
    refine ⟨(0, Pi.single j (1 : k)), ?_⟩
    rw [LinearMap.coprod_apply, map_zero, zero_add, hG]
    rw [Finset.sum_eq_single j]
    · simp [Pi.single_apply]
    · intro i _ hi
      simp [Pi.single_apply, hi, Ne.symm hi]
    · exact fun h => (h (Finset.mem_univ j)).elim
  have hAll (i : Fin (finrank k S)) : v i ∈ LinearMap.range A := by
    rcases lt_trichotomy (a i) 0 with hi | hi | hi
    · exact hGMem (Sum.inr ⟨i, hi⟩)
    · apply hLift
      apply hLiftZero
      exact (hd i).trans (by rw [ha i, hi, Int.cast_zero, zero_smul])
    · exact hGMem (Sum.inl ⟨i, hi⟩)
  have hSpan : Function.Surjective fun z : HopfLieVector k Q k × ((Ipos ⊕ Ineg) → k) =>
      p z.1 + ∑ j, z.2 j • Sum.elim vPos vNeg j := by
    intro x
    have hx : E x ∈ S ⊔ center k 𝔤 := hC.sup_eq_top ▸ LieSubmodule.mem_top (E x)
    obtain ⟨y, hy, z, hz, hSum⟩ := (LieSubmodule.mem_sup _ _ _).mp hx
    have hYS : E.symm y ∈ LinearMap.range A := by
      let y' : S := ⟨y, hy⟩
      let F : S →ₗ[k] L := E.symm.toLinearMap.comp S.toSubmodule.subtype
      change F y' ∈ LinearMap.range A
      have hSum' := congrArg F (B.sum_repr y')
      simp only [map_sum, map_smul] at hSum'
      rw [← hSum']
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hAll i)
    have hZS : E.symm z ∈ LinearMap.range A := hLift z (hLiftCenter ⟨z, hz⟩)
    have hX : x ∈ LinearMap.range A := by
      rw [← E.symm_apply_apply x, ← hSum, map_add]
      exact Submodule.add_mem _ hYS hZS
    obtain ⟨c, hc⟩ := hX
    exact ⟨c, (by simpa only [A, LinearMap.coprod_apply, hG] using hc)⟩
  apply hopfAdjointCentralizerIdeal_eq_ker_of_spanning_exponentials b U hΔ hε hGen w
    (fun n : ℤ => (n : k)) (fun i j hn he => hn (Int.cast_injective he)) _ ?_ π
    (fun i j hn => hπ i j (fun he => hn (congrArg w he))) vPos vNeg hLow hHigh hSpan
  rw [← hopfLieMatrix_invariantDerivations, E.apply_symm_apply, hW]
  rfl

end Centralizer

end WideE
