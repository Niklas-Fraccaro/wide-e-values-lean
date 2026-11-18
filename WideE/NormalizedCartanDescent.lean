import WideE.DiagonalAdjointCentralizerExtension
import WideE.PolynomialNormalizationSlice
import WideE.RegularSliceRatFunc
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-! Descent from a normalized Cartan slice with a geometric torus centralizer. -/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

variable {k Ω H ι η τ σ ν μ Λ : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω] [IsScalarTower k (RatFunc k) Ω]
  [IsGalois (RatFunc k) Ω] [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
  [Fintype ι] [DecidableEq ι] [Fintype η] [DecidableEq η] [Fintype τ] [Fintype σ] [Fintype ν]
  [AddCommGroup Λ] [Finite μ]

attribute [local instance] hopfScalarExtension

local notation "F₀" => RatFunc k
local notation "𝔩" => HopfLieVector k H

set_option maxHeartbeats 2200000 in
set_option synthInstance.maxHeartbeats 180000 in
/-- The geometric open, normalization, and torus centralizer give a coboundary. -/
theorem isHopfPointCoboundary_of_normalizedCartanSlice
    (b : Basis η k (HopfCotangent k H)) (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (e : 𝔩 k) (v : τ → 𝔩 k) (w : σ → 𝔩 k) (N : ν → Matrix ι ι k) (d : MvPolynomial τ k)
    (hLift : ∀ a : τ → k, MvPolynomial.aeval a d ≠ 0 → ∃ s, HopfSliceNormalization U e v w N a s)
    (hUnique : ∀ {y y' : 𝔩 k}, y ∈ normalizedHopfSlice U e v w N d →
      y' ∈ normalizedHopfSlice U e v w N d → ∀ g : H →ₐ[k] k, hopfAdjoint g y = y' → y = y')
    (p : MvPolynomial η k) (hp : p ≠ 0)
    (hOpen : ∀ x : 𝔩 Ω, MvPolynomial.aeval (fun i => x (b i)) p ≠ 0 →
      ∃ (g : H →ₐ[k] Ω) (a : τ → Ω), MvPolynomial.aeval a d ≠ 0 ∧
        x = hopfAdjoint g (∑ j, a j • (Algebra.ofId k Ω).toLinearMap.comp (v j)))
    (basis : Basis μ ℤ Λ)
    (hTorus : ∀ (a : τ → Ω), MvPolynomial.aeval a d ≠ 0 →
      let b' := hopfCotangentBasisBaseChange (F := Ω) b
      let x' := hopfLieVectorBaseChange (F := Ω) (∑ j, a j • (Algebra.ofId k Ω).toLinearMap.comp (v j))
      letI := (hopfAdjointCentralizerIdeal_isHopf b' x').quotientHopf
      letI := StrictEUnit.baseChangeBialgebra (k := k) (H := MonoidAlgebra k (Multiplicative Λ)) Ω
      Nonempty (((Ω ⊗[k] H) ⧸ hopfAdjointCentralizerIdeal b' x') ≃ₐc[Ω]
        (Ω ⊗[k] MonoidAlgebra k (Multiplicative Λ))))
    (E : FiniteGaloisIntermediateField F₀ Ω) (c : (E ≃ₐ[F₀] E) → H →ₐ[k] E)
    (hc : IsHopfPointCocycle c) : IsHopfPointCoboundary c := by
  let slice : Set (𝔩 Ω) := normalizedHopfSlice U e v w N d
  have hFamily (a : τ → Ω) : hopfAdjointSlice 0 v a =
      ∑ j, a j • (Algebra.ofId k Ω).toLinearMap.comp (v j) := by
    rw [hopfAdjointSlice, LinearMap.comp_zero, zero_add]
  apply isHopfPointCoboundary_of_stable_regularSlice_ratFunc b p hp slice ?_ ?_ basis ?_ E c hc
  · intro γ y hy
    exact normalizedHopfSlice_postcompose (γ.toAlgHom.restrictScalars k) γ.injective U e v w N d hy
  · intro x hx
    obtain ⟨g, a, ha, hg⟩ := hOpen x hx
    exact existsUnique_normalizedHopfSlice_of_cartanConjugacy b U hD he hGen e v w N d
      hLift hUnique x a ha g (by rw [hFamily, hg])
  · intro y hy
    obtain ⟨a, s, ha, ⟨_, q, _, _, _, hq⟩, rfl⟩ := hy
    let z : 𝔩 Ω := ∑ j, a j • (Algebra.ofId k Ω).toLinearMap.comp (v j)
    obtain ⟨t⟩ := hTorus a ha
    let b' := hopfCotangentBasisBaseChange (F := Ω) b
    let y' := hopfLieVectorBaseChange (F := Ω) (hopfAdjointSlice e w s)
    let z' := hopfLieVectorBaseChange (F := Ω) z
    have hq' : hopfAdjoint (scalarExtendPoint (A := Ω) q) y' = z' := by
      change hopfAdjoint (scalarExtendPoint (A := Ω) q)
        (hopfLieVectorBaseChange (F := Ω) (hopfAdjointSlice e w s)) = _
      rw [← hopfLieVectorBaseChange_adjoint, hq, hFamily]
    let t' := bialgEquiv_hopfAdjointCentralizer_conjugate b' (scalarExtendPoint (A := Ω) q) z' y' hq'
    letI := (hopfAdjointCentralizerIdeal_isHopf b' y').quotientHopf
    letI := (hopfAdjointCentralizerIdeal_isHopf b' z').quotientHopf
    letI := StrictEUnit.baseChangeBialgebra (k := k) (H := MonoidAlgebra k (Multiplicative Λ)) Ω
    exact ⟨t'.symm.trans (t.trans (monoidAlgebraBaseChangeBialgEquiv k Ω (Multiplicative Λ)))⟩

end WideE
