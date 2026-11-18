import WideE.AdjointToricDescent
import WideE.AdjointCovariance
import WideE.TorusSplittingField

/-! Toric adjoint descent when the conjugation data are initially geometric. -/

noncomputable section

open scoped TensorProduct

namespace WideE

section Descent

variable {F Ω H Λ ι η : Type*} [Field F] [CharZero F] [Field Ω] [Algebra F Ω]
variable [IsAlgClosed Ω] [IsGalois F Ω] [CommRing H] [HopfAlgebra F H] [Algebra.FiniteType F H]
variable [Fintype ι] [DecidableEq ι] [AddCommGroup Λ] [Finite η]

local notation "C" => HopfCotangent F H

/-- A geometric conjugator and torus splitting of the rational centralizer suffice.
Both descend to one finite Galois extension of the original cocycle field. -/
theorem isHopfPointCoboundary_of_geometricToricAdjointCentralizer
    (hF : IsC1 F) (hRoots : ∀ n : ℕ, 0 < n → (primitiveRoots n F).Nonempty)
    (basis : Basis η ℤ Λ) (b : Basis ι F C) (E : FiniteGaloisIntermediateField F Ω)
    (c : (E ≃ₐ[F] E) → H →ₐ[F] E) (hc : IsHopfPointCocycle c)
    (x : HopfLieVector F H E) (y : HopfLieVector F H F) (a : H →ₐ[F] Ω)
    (hConj : hopfAdjoint a ((Algebra.ofId F Ω).toLinearMap.comp y) =
      E.toIntermediateField.val.toLinearMap.comp x)
    (hFixed : ∀ σ, hopfAdjoint (c σ) (σ.toAlgHom.toLinearMap.comp x) = x)
    (e : letI := (hopfAdjointCentralizerIdeal_isHopf b y).quotientHopf
         TorusHopfSplitting F Ω (H ⧸ hopfAdjointCentralizerIdeal b y) (Multiplicative Λ)) :
    IsHopfPointCoboundary c := by
  let I := hopfAdjointCentralizerIdeal b y
  let J := H ⧸ I
  letI : HopfAlgebra F J := (hopfAdjointCentralizerIdeal_isHopf b y).quotientHopf
  letI : Algebra.FiniteType F J := Algebra.FiniteType.of_surjective inferInstance
    (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ_surjective F I)
  letI : Fintype η := Fintype.ofFinite η
  letI : AddGroup.FG Λ := Module.Finite.iff_addGroup_fg.mp (Module.Finite.of_basis basis)
  obtain ⟨M, hEM, aM, ha⟩ := exists_finiteGalois_field_of_definition E a
  obtain ⟨L, hML, ⟨d⟩⟩ := exists_finiteGalois_torusHopfSplitting_model M e
  let aL := (IntermediateField.inclusion hML).comp aM
  let hEL := hEM.trans hML
  have haL : L.toIntermediateField.val.comp aL = a := ha
  have hConj' : hopfAdjoint aL ((Algebra.ofId F L).toLinearMap.comp y) =
      (IntermediateField.inclusion hEL).toLinearMap.comp x := by
    apply LinearMap.ext
    intro z
    apply L.toIntermediateField.val.injective
    have h := hopfAdjoint_postcompose L.toIntermediateField.val aL ((Algebra.ofId F L).toLinearMap.comp y)
    rw [haL] at h
    exact (DFunLike.congr_fun h z).trans (DFunLike.congr_fun hConj z)
  exact isHopfPointCoboundary_of_toricAdjointCentralizer hF hRoots basis b E L hEL
    c hc x y aL hConj' hFixed d

/-- Geometric conjugation of a twisted regular vector to a rational one with toric
centralizer yields a coboundary. The nonempty principal open supplies that vector. -/
theorem isHopfPointCoboundary_of_regularAdjointConjugacy
    (hF : IsC1 F) (hRoots : ∀ n : ℕ, 0 < n → (primitiveRoots n F).Nonempty)
    (basis : Basis η ℤ Λ) (b : Basis ι F C) (E : FiniteGaloisIntermediateField F Ω)
    (c : (E ≃ₐ[F] E) → H →ₐ[F] E) (hc : IsHopfPointCocycle c)
    (p : MvPolynomial ι E) (hp : p ≠ 0)
    (hConjugate : ∀ x : HopfLieVector F H E, MvPolynomial.eval (fun i => x (b i)) p ≠ 0 →
      (∀ σ, hopfAdjoint (c σ) (σ.toAlgHom.toLinearMap.comp x) = x) →
      ∃ (y : HopfLieVector F H F) (a : H →ₐ[F] Ω),
        hopfAdjoint a ((Algebra.ofId F Ω).toLinearMap.comp y) =
          E.toIntermediateField.val.toLinearMap.comp x ∧
        Nonempty (letI := (hopfAdjointCentralizerIdeal_isHopf b y).quotientHopf
          TorusHopfSplitting F Ω (H ⧸ hopfAdjointCentralizerIdeal b y) (Multiplicative Λ))) :
    IsHopfPointCoboundary c := by
  obtain ⟨x, hEval, hFixed⟩ := exists_twistedHopfLieVector_eval_ne_zero b E c hc p hp
  obtain ⟨y, a, hConj, ⟨e⟩⟩ := hConjugate x hEval hFixed
  exact isHopfPointCoboundary_of_geometricToricAdjointCentralizer hF hRoots basis b E c hc
    x y a hConj hFixed e

end Descent

end WideE
