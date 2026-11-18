import WideE.AdjointCovariance
import WideE.GeometricToricDescent

/-! A unique representative on a rational adjoint slice descends along a twisted orbit. -/

noncomputable section

namespace WideE

variable {F Ω H ι η : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
  [CommRing H] [HopfAlgebra F H] [Fintype ι] [DecidableEq ι] [Fintype η]

local notation "C" => HopfCotangent F H
local notation "𝔤" => HopfLieVector F H

/-- The scalar extension of the affine slice with a given origin and linear directions. -/
def hopfAdjointSlice (e : 𝔤 F) (v : η → 𝔤 F) : (η → Ω) → 𝔤 Ω := fun a =>
  (Algebra.ofId F Ω).toLinearMap.comp e + ∑ i, a i • (Algebra.ofId F Ω).toLinearMap.comp (v i)

omit [IsGalois F Ω] in
private theorem hopfAdjointSlice_galois (e : 𝔤 F) (v : η → 𝔤 F) (a : η → Ω) (σ : Ω ≃ₐ[F] Ω) :
    σ.toAlgHom.toLinearMap.comp (hopfAdjointSlice e v a) = hopfAdjointSlice e v (fun i => σ (a i)) := by
  ext z
  simp only [hopfAdjointSlice, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, AlgHom.toLinearMap_apply, AlgEquiv.coe_algHom, map_add, map_sum,
    smul_eq_mul, map_mul, Algebra.ofId_apply, AlgEquiv.commutes]

/-- The unique point on a Galois-stable set in the orbit of a twisted fixed vector descends. -/
theorem exists_rationalHopfLieVector_of_unique_stable_representative (b : Basis ι F C)
    (E : FiniteGaloisIntermediateField F Ω) (c : (E ≃ₐ[F] E) → H →ₐ[F] E)
    (x : 𝔤 E) (hFixed : ∀ σ, hopfAdjoint (c σ) (σ.toAlgHom.toLinearMap.comp x) = x)
    (slice : Set (𝔤 Ω)) (hStable : ∀ (σ : Ω ≃ₐ[F] Ω) y,
      y ∈ slice → σ.toAlgHom.toLinearMap.comp y ∈ slice)
    (hSlice : ∃! y : 𝔤 Ω, y ∈ slice ∧
      ∃ g : H →ₐ[F] Ω, hopfAdjoint g y = E.toIntermediateField.val.toLinearMap.comp x) :
    ∃ (y : 𝔤 F) (g : H →ₐ[F] Ω),
      (Algebra.ofId F Ω).toLinearMap.comp y ∈ slice ∧
      hopfAdjoint g ((Algebra.ofId F Ω).toLinearMap.comp y) = E.toIntermediateField.val.toLinearMap.comp x := by
  let iE : E →ₐ[F] Ω := E.toIntermediateField.val
  let X := iE.toLinearMap.comp x
  letI : Group (H →ₐ[F] Ω) := hopfPointGroup
  obtain ⟨y, ⟨hy, ⟨g, hg⟩⟩, hUnique⟩ := hSlice
  change hopfAdjoint g y = X at hg
  have hY (σ : Ω ≃ₐ[F] Ω) : σ.toAlgHom.toLinearMap.comp y = y := by
    let τ := AlgEquiv.restrictNormalHom E σ
    have hi : σ.toAlgHom.comp iE = iE.comp τ.toAlgHom :=
      AlgHom.ext fun a => (σ.restrictNormal_commutes E a).symm
    have hFix : hopfAdjoint (iE.comp (c τ)) (σ.toAlgHom.toLinearMap.comp X) = X := by
      have hEq : σ.toAlgHom.toLinearMap.comp X = iE.toLinearMap.comp (τ.toAlgHom.toLinearMap.comp x) := by
        apply LinearMap.ext
        intro z
        exact DFunLike.congr_fun hi (x z)
      rw [hEq, ← hopfAdjoint_postcompose, hFixed]
    apply hUnique
    refine ⟨hStable σ y hy, iE.comp (c τ) * (σ.toAlgHom.comp g), ?_⟩
    rw [hopfAdjoint_mul b, ← hopfAdjoint_postcompose, hg]
    exact hFix
  let ev : MvPolynomial ι F →ₐ[F] Ω := MvPolynomial.aeval (fun i => y (b i))
  have hEv (σ : Ω ≃ₐ[F] Ω) : σ.toAlgHom.comp ev = ev := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa only [AlgHom.comp_apply, ev, MvPolynomial.aeval_X] using
      DFunLike.congr_fun (hY σ) (b j)
  obtain ⟨q, hq⟩ := exists_basePoint_of_galois_fixed ev (fun σ p => DFunLike.congr_fun (hEv σ) p)
  let Y := b.constr F (fun j => q (MvPolynomial.X j))
  have hYY : (Algebra.ofId F Ω).toLinearMap.comp Y = y := by
    apply b.ext
    intro j
    have hh := DFunLike.congr_fun hq (MvPolynomial.X j)
    change (Algebra.ofId F Ω) (q (MvPolynomial.X j)) = ev (MvPolynomial.X j) at hh
    rw [show ev (MvPolynomial.X j) = y (b j) from MvPolynomial.aeval_X _ _] at hh
    change (Algebra.ofId F Ω) (Y (b j)) = y (b j)
    rw [show Y (b j) = q (MvPolynomial.X j) from b.constr_basis _ _ _]
    exact hh
  exact ⟨Y, g, hYY.symm ▸ hy, hYY.symm ▸ hg⟩

/-- Specialization to an affine slice given by rational origin and directions. -/
theorem exists_rationalHopfLieVector_of_unique_slice (b : Basis ι F C)
    (E : FiniteGaloisIntermediateField F Ω) (c : (E ≃ₐ[F] E) → H →ₐ[F] E)
    (x : 𝔤 E) (hFixed : ∀ σ, hopfAdjoint (c σ) (σ.toAlgHom.toLinearMap.comp x) = x)
    (e : 𝔤 F) (v : η → 𝔤 F)
    (hSlice : ∃! y : 𝔤 Ω, y ∈ Set.range (hopfAdjointSlice e v) ∧
      ∃ g : H →ₐ[F] Ω, hopfAdjoint g y = E.toIntermediateField.val.toLinearMap.comp x) :
    ∃ (y : 𝔤 F) (g : H →ₐ[F] Ω),
      (Algebra.ofId F Ω).toLinearMap.comp y ∈ Set.range (hopfAdjointSlice e v) ∧
      hopfAdjoint g ((Algebra.ofId F Ω).toLinearMap.comp y) = E.toIntermediateField.val.toLinearMap.comp x :=
  exists_rationalHopfLieVector_of_unique_stable_representative b E c x hFixed
    (Set.range (hopfAdjointSlice e v)) (by
      rintro σ y ⟨a, rfl⟩
      exact ⟨fun j => σ (a j), (hopfAdjointSlice_galois e v a σ).symm⟩) hSlice

end WideE
