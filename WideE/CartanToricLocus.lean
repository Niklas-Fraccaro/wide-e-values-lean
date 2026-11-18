import WideE.CartanAvoidancePolynomial
import WideE.DiagonalAdjointCentralizerExtension
import WideE.PrincipalCartanCentralizer
import WideE.ReductiveCartanOrbit

/-! A uniform open of Cartan parameters with the actual split torus as centralizer. -/

noncomputable section

open LieAlgebra LieAlgebra.IsKilling LieModule Module
open scoped Matrix TensorProduct

namespace WideE

universe u

variable {k : Type u} {H Q ι η τ : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing H] [HopfAlgebra k H] [IsDomain H] [Algebra.FiniteType k H]
  [CommRing Q] [HopfAlgebra k Q] [IsDomain Q]
  [Fintype ι] [DecidableEq ι] [Fintype η] [DecidableEq η] [Fintype τ]

attribute [local instance] hopfScalarExtension

local notation "𝔤" => hopfInvariantDerivations k H
local notation "J" => hopfLieVectorInvariantDerivations (k := k) (H := H)

variable {S : LieIdeal k (hopfInvariantDerivations k H)} [IsKilling k S] [FiniteDimensional k S]
  {C : LieSubalgebra k S} [C.IsCartanSubalgebra] [IsTriangularizable k C S]

local notation "Φ" => LieAlgebra.IsKilling.rootSystem C

set_option maxHeartbeats 2400000 in
/-- A principal open retains regular Cartan parameters and their scheme-theoretic
centralizer after arbitrary field extension. The principal stabilizer fixes the Cartan. -/
theorem exists_cartanToricLocus (b : Basis η k (HopfCotangent k H)) (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (hCompl : IsCompl S (center k 𝔤)) (cB : Basis τ k (C × center k 𝔤))
    (z₀ : C) (hz₀ : ∀ α : C.root, (Φ).root α z₀ ≠ 0) {e₀ f₀ : S}
    (ht : IsSl2Triple (z₀ : S) e₀ f₀)
    (π : H →ₐc[k] Q) (hSurj : Function.Surjective π)
    (hπ : ∀ i j, i ≠ j → π (U.val i j) = 0)
    (hLift : ∀ (x : C) (z : center k 𝔤), ∃ D : hopfInvariantDerivations k Q,
      hopfInvariantDerivationsMap π D = cartanCenterDirection C x z) :
    let v (i : τ) := cartanCenterLieEmbedding C (cB i)
    (∀ p : H →ₐ[k] k,
      hopfAdjoint p ((J).symm ((z₀ : S) : 𝔤)) = (J).symm ((z₀ : S) : 𝔤) →
      ∀ z : C, hopfAdjoint p ((J).symm ((z : S) : 𝔤)) = (J).symm ((z : S) : 𝔤)) ∧
    ∃ d : MvPolynomial τ k, d ≠ 0 ∧
      (∀ (c : τ → k), MvPolynomial.aeval c d ≠ 0 →
        ∀ α : C.root, (Φ).root α (∑ j, c j • cB j).1 ≠ 0) ∧
      (∀ (Ω : Type u) [Field Ω] [Algebra k Ω] (c : τ → Ω), MvPolynomial.aeval c d ≠ 0 →
        let b' := hopfCotangentBasisBaseChange (F := Ω) b
        let x' := hopfLieVectorBaseChange (F := Ω) (∑ j, c j • (Algebra.ofId k Ω).toLinearMap.comp (v j))
        letI := (hopfAdjointCentralizerIdeal_isHopf b' x').quotientHopf
        Nonempty (((Ω ⊗[k] H) ⧸ hopfAdjointCentralizerIdeal b' x') ≃ₐc[Ω] (Ω ⊗[k] Q))) := by
  classical
  let x₀ := (J).symm ((z₀ : S) : 𝔤)
  let n (z : C) := (J).symm ((z : S) : 𝔤)
  let v (i : τ) := cartanCenterLieEmbedding C (cB i)
  have hDiag (x : C) (z : center k 𝔤) :
      let M := hopfLieMatrix U.val (cartanCenterDirection C x z)
      M = Matrix.diagonal (fun i => M i i) := by
    obtain ⟨D, hD⟩ := hLift x z
    dsimp only
    rw [← hD]
    exact hopfLieMatrix_lift_to_diagonal U.val π hπ D
  have hZero (x : C) : cartanCenterDirection C x 0 = ((x : S) : 𝔤) := by simp [cartanCenterDirection]
  let w (i : ι) := hopfLieMatrix U.val ((z₀ : S) : 𝔤) i i
  have hMatrix₀ : hopfLieMatrix U.val ((z₀ : S) : 𝔤) = Matrix.diagonal w := by
    have h := hDiag z₀ 0
    dsimp only at h
    simpa only [hZero] using h
  have hX₀ : hopfCotangentMatrix U.val x₀ = Matrix.diagonal w := by
    rw [← hopfLieMatrix_invariantDerivations, show (J) x₀ = ((z₀ : S) : 𝔤) from (J).apply_symm_apply _]
    exact hMatrix₀
  have hJ := hopfAdjointCentralizerIdeal_eq_ker_of_principalTriple b U hD he hGen S hCompl ht
    (isSemisimple_ad_of_mem_isCartanSubalgebra (K := k) (H := C) z₀.property) w hMatrix₀ π hπ
    (fun x hx => by
      let z : C := ⟨x, (lie_regularCartan_eq_zero_iff_mem z₀ hz₀ x).mp hx⟩
      obtain ⟨D, hD⟩ := hLift z 0
      exact ⟨D, hD.trans (hZero z)⟩)
    (fun z => by simpa only [cartanCenterDirection, ZeroMemClass.coe_zero, zero_add] using hLift 0 z)
  have hBlocks := hopfAdjointCentralizerIdeal_eq_weightBlocks b U hD he hGen w id (fun _ _ h => h) x₀ hX₀
  have hKer : weightCentralizerIdeal w U.val = RingHom.ker (π : H →ₐ[k] Q).toRingHom := hBlocks.symm.trans hJ
  refine ⟨?_, ?_⟩
  · intro p hp z
    have hP := (hopfAdjoint_eq_self_iff_ker_le_of_separating_diagonal U hD he hGen w (π : H →ₐ[k] Q)
      hπ hKer x₀ w hX₀ (fun _ _ h => isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr h.symm)) p).mp hp
    change hopfAdjoint p (n z) = n z
    have hM (x : C) : hopfCotangentMatrix U.val (n x) =
        Matrix.diagonal (fun i => hopfLieMatrix U.val ((x : S) : 𝔤) i i) := by
      rw [← hopfLieMatrix_invariantDerivations, show (J) (n x) = ((x : S) : 𝔤) from (J).apply_symm_apply _]
      have h := hDiag x 0
      dsimp only at h
      simpa only [hZero] using h
    exact hopfAdjoint_eq_self_of_ker_le_of_diagonal U hD he hGen (π : H →ₐ[k] Q) hπ (n z) _ (hM z) p hP
  · let a (j : τ) (i : ι) := hopfCotangentMatrix U.val (v j) i i
    have hv (j : τ) : hopfCotangentMatrix U.val (v j) = Matrix.diagonal (a j) := by
      have h := hDiag (cB j).1 (cB j).2
      dsimp only at h
      simpa only [a, v, ← hopfLieMatrix_invariantDerivations, cartanCenterLieEmbedding_apply] using h
    let r (α : C.root) : (C × center k 𝔤) →ₗ[k] k := ((Φ).root α).comp (LinearMap.fst k C _)
    let c₀ (j : τ) := cB.repr (z₀, 0) j
    have hRoot (c : τ → k) (α : C.root) :
        (∑ j, c j * r α (cB j)) = (Φ).root α (∑ j, c j • cB j).1 := by
      change _ = r α (∑ j, c j • cB j)
      simp only [map_sum, map_smul, smul_eq_mul]
    have hR₀ (α : C.root) : ∑ j, c₀ j * r α (cB j) ≠ 0 := by
      rw [hRoot, cB.sum_repr]
      exact hz₀ α
    have hSumV : (∑ j, c₀ j • v j) = x₀ := by
      rw [show (∑ j, c₀ j • v j) = cartanCenterLieEmbedding C (∑ j, c₀ j • cB j) by
        simp only [v, map_sum, map_smul], cB.sum_repr]
      apply (J).injective
      rw [cartanCenterLieEmbedding_apply, (J).apply_symm_apply, hZero]
    have hA₀ (i : ι) : ∑ j, c₀ j * a j i = w i := by
      have h := congrArg (fun X => hopfCotangentMatrix U.val X i i) hSumV
      change (∑ j, c₀ j • v j) (hopfCotangentProjection k H (U.val i i)) = hopfCotangentMatrix U.val x₀ i i at h
      rw [hX₀, Matrix.diagonal_apply_eq] at h
      simpa only [a, hopfCotangentMatrix, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using h
    obtain ⟨d, hd, hOpen⟩ := exists_cartanAvoidancePolynomial (fun α j => r α (cB j)) a w c₀ hR₀ hA₀
    refine ⟨d, hd, ?_, ?_⟩
    · intro c hc α
      rw [← hRoot]
      exact (hOpen k c hc).1 α
    · intro Ω _ _ c hc
      let x : HopfLieVector k H Ω := ∑ j, c j • (Algebra.ofId k Ω).toLinearMap.comp (v j)
      let a' (i : ι) : Ω := ∑ j, c j * algebraMap k Ω (a j i)
      have hX : hopfCotangentMatrix U.val x = Matrix.diagonal a' := hopfCotangentMatrix_sum_diagonal U.val v a hv c
      exact ⟨bialgEquiv_hopfAdjointCentralizer_diagonal_baseChange b U hD he hGen w π hSurj
        hπ hKer x a' hX (hOpen Ω c hc).2⟩

end WideE
