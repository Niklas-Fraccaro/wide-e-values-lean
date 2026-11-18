import WideE.HopfAdjoint
import WideE.ToricCentralizerDescent

/-! The toric-centralizer reduction for the actual adjoint representation. -/

noncomputable section

open scoped Matrix

namespace WideE

section Centralizer

variable {F H ι : Type*} [Field F] [CommRing H] [HopfAlgebra F H]
variable [Fintype ι] [DecidableEq ι]

local notation "C" => HopfCotangent F H

/-- The equations defining the subgroup centralizing a rational Lie vector. -/
abbrev hopfAdjointCentralizerIdeal (b : Basis ι F C) (y : HopfLieVector F H F) : Ideal H :=
  vectorStabilizerIdeal (hopfAdjointMatrix b) (fun i => y (b i))

/-- The adjoint centralizer is a closed subgroup of the original Hopf group. -/
theorem hopfAdjointCentralizerIdeal_isHopf (b : Basis ι F C) (y : HopfLieVector F H F) :
    IsHopfIdeal F (hopfAdjointCentralizerIdeal b y) :=
  vectorStabilizerIdeal_isHopf (hopfAdjointMatrixUnit b) (hopfAdjointMatrix_comul b)
    (hopfAdjointMatrix_counit b) (fun i => y (b i))

/-- Points of the adjoint centralizer quotient fix the Lie vector under actual adjoint action. -/
def hopfAdjointCentralizerPoints {A : Type*} [CommRing A] [Algebra F A]
    (b : Basis ι F C) (y : HopfLieVector F H F) :
    ((H ⧸ hopfAdjointCentralizerIdeal b y) →ₐ[F] A) ≃
      {p : H →ₐ[F] A //
        hopfAdjoint p ((Algebra.ofId F A).toLinearMap.comp y) =
          (Algebra.ofId F A).toLinearMap.comp y} := by
  let v : HopfLieVector F H A := (Algebra.ofId F A).toLinearMap.comp y
  refine (vectorStabilizerPointEquiv (A := A) (hopfAdjointMatrix b) (fun i => y (b i))).trans
    (Equiv.subtypeEquivRight fun p => ?_)
  change (hopfAdjointMatrix b).map p *ᵥ (fun i => v (b i)) = (fun i => v (b i)) ↔
    hopfAdjoint p v = v
  rw [← hopfAdjoint_apply_basis b p v]
  exact ⟨fun h => b.ext fun i => congrFun h i,
    fun h => congrArg (fun t : HopfLieVector F H A => fun i => t (b i)) h⟩

end Centralizer

section Descent

variable {F Ω H Λ ι η : Type*} [Field F] [Field Ω] [Algebra F Ω] [CommRing H] [HopfAlgebra F H]
variable [Fintype ι] [DecidableEq ι]

local notation "C" => HopfCotangent F H

/-- Matrix Hilbert 90 selects a twisted fixed Lie vector in any given nonempty principal open. -/
theorem exists_twistedHopfLieVector_eval_ne_zero [Infinite F]
    (b : Basis ι F C) (E : FiniteGaloisIntermediateField F Ω)
    (c : (E ≃ₐ[F] E) → H →ₐ[F] E) (hc : IsHopfPointCocycle c)
    (p : MvPolynomial ι E) (hp : p ≠ 0) :
    ∃ x : HopfLieVector F H E, MvPolynomial.eval (fun i => x (b i)) p ≠ 0 ∧
      ∀ σ, hopfAdjoint (c σ) (σ.toAlgHom.toLinearMap.comp x) = x := by
  obtain ⟨u, hu, hFixed⟩ := exists_twistedHopfPoint_fixedPoint_eval_ne_zero
    (hopfAdjointMatrixUnit b) (hopfAdjointMatrix_comul b) (hopfAdjointMatrix_counit b) c hc p hp
  let x : HopfLieVector F H E := b.constr E u
  have hx (i : ι) : x (b i) = u i := b.constr_basis E u i
  refine ⟨x, ?_, fun σ => ?_⟩
  · exact fun h => hu (by simpa only [hx] using h)
  · apply b.ext
    intro i
    have h := hopfAdjoint_apply_basis b (c σ) (σ.toAlgHom.toLinearMap.comp x)
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgEquiv.coe_algHom, hx] at h
    exact (congrFun (h.trans (hFixed σ)) i).trans (hx i).symm

variable [CharZero F] [IsAlgClosed Ω] [IsGalois F Ω] [AddCommGroup Λ] [Finite η]

/-- A twisted fixed Lie vector conjugate to a rational vector with toric centralizer
trivializes its cocycle. The conjugator and torus may be defined over a larger Galois field. -/
theorem isHopfPointCoboundary_of_toricAdjointCentralizer
    (hF : IsC1 F) (hRoots : ∀ n : ℕ, 0 < n → (primitiveRoots n F).Nonempty)
    (basis : Basis η ℤ Λ) (b : Basis ι F C)
    (E L : FiniteGaloisIntermediateField F Ω) (hEL : E ≤ L)
    (c : (E ≃ₐ[F] E) → H →ₐ[F] E) (hc : IsHopfPointCocycle c)
    (x : HopfLieVector F H E) (y : HopfLieVector F H F) (a : H →ₐ[F] L)
    (hConj : hopfAdjoint a ((Algebra.ofId F L).toLinearMap.comp y) =
      (IntermediateField.inclusion hEL).toLinearMap.comp x)
    (hFixed : ∀ σ, hopfAdjoint (c σ) (σ.toAlgHom.toLinearMap.comp x) = x)
    (e : letI := (hopfAdjointCentralizerIdeal_isHopf b y).quotientHopf
         TorusHopfSplitting F L (H ⧸ hopfAdjointCentralizerIdeal b y) (Multiplicative Λ)) :
    IsHopfPointCoboundary c := by
  refine isHopfPointCoboundary_of_toricVectorStabilizer_after_extension hF hRoots basis E L hEL
    (hopfAdjointMatrixUnit b) (hopfAdjointMatrix_comul b) (hopfAdjointMatrix_counit b) c hc
    (fun i => x (b i)) (fun i => y (b i)) a ?_ ?_ e
  · have h := congrArg (fun t : HopfLieVector F H L => fun i => t (b i)) hConj
    change (fun i => hopfAdjoint a ((Algebra.ofId F L).toLinearMap.comp y) (b i)) =
      (fun i => (IntermediateField.inclusion hEL).toLinearMap.comp x (b i)) at h
    rw [hopfAdjoint_apply_basis] at h
    exact h
  · intro σ
    have h := congrArg (fun t : HopfLieVector F H E => fun i => t (b i)) (hFixed σ)
    change (fun i => hopfAdjoint (c σ) (σ.toAlgHom.toLinearMap.comp x) (b i)) =
      (fun i => x (b i)) at h
    rw [hopfAdjoint_apply_basis] at h
    exact h

end Descent

end WideE
