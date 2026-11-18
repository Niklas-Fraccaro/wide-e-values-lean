import WideE.AdjointCovariance
import WideE.AdjointCentralizerTangent
import WideE.AdjointToricDescent
import WideE.BigCellCentralizer
import WideE.GaloisKernelReduction

/-! The centralizer quotient is natural under an actual change of Hopf coordinates. -/

noncomputable section

namespace WideE

section Naturality

variable {k H J A : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing J] [HopfAlgebra k J] [CommRing A] [Algebra k A]

theorem hopfLiePullback_postcompose {B : Type*} [CommRing B] [Algebra k B]
    (f : H →ₐc[k] J) (g : A →ₐ[k] B) (x : HopfLieVector k J A) :
    hopfLiePullback (f : H →ₐ[k] J) (BialgHomClass.counitAlgHom_comp f) (g.toLinearMap.comp x) =
      g.toLinearMap.comp (hopfLiePullback (f : H →ₐ[k] J) (BialgHomClass.counitAlgHom_comp f) x) := by
  apply LinearMap.ext
  intro u
  obtain ⟨a, rfl⟩ := hopfCotangentProjection_surjective k H u
  simp only [LinearMap.comp_apply, hopfLiePullback_projection]

theorem hopfLiePullback_adjoint_bialg (f : H →ₐc[k] J) (p : J →ₐ[k] A) (x : HopfLieVector k J A) :
    let ψ := hopfLiePullback (f : H →ₐ[k] J) (BialgHomClass.counitAlgHom_comp f) (A := A)
    ψ (hopfAdjoint p x) = hopfAdjoint (p.comp (f : H →ₐ[k] J)) (ψ x) := by
  intro ψ
  let g : H →ₐ[k] J := f
  let i := TrivSqZeroExt.inlAlgHom k A A
  letI := hopfPointGroup (k := k) (H := H) (A := DualNumber A)
  letI := hopfPointGroup (k := k) (H := J) (A := DualNumber A)
  let F := hopfPointPrecompose (A := DualNumber A) f
  have hL : hopfLieInfinitesimalPoint (hopfAdjoint p x) =
      i.comp p * hopfLieInfinitesimalPoint x * (i.comp p)⁻¹ := by
    rw [← hopfInfinitesimal_conjugation, hopfConjugation_eval]
  have hR : hopfLieInfinitesimalPoint (hopfAdjoint (p.comp g) (ψ x)) =
      F (i.comp p) * hopfLieInfinitesimalPoint (ψ x) * (F (i.comp p))⁻¹ := by
    rw [← hopfInfinitesimal_conjugation, hopfConjugation_eval]
    rfl
  have hψ (y : HopfLieVector k J A) : hopfLieInfinitesimalPoint (ψ y) = F (hopfLieInfinitesimalPoint y) :=
    hopfLieInfinitesimalPoint_pullback g (BialgHomClass.counitAlgHom_comp f) y
  apply (hopfInfinitesimalPointEquiv k H A).injective
  apply Subtype.ext
  change hopfLieInfinitesimalPoint (ψ (hopfAdjoint p x)) = hopfLieInfinitesimalPoint (hopfAdjoint (p.comp g) (ψ x))
  rw [hψ, hL, hR, hψ, map_mul, map_mul, map_inv]

private theorem adjoint_rational_fixed_iff_pullback (f : H →ₐc[k] J) (hf : Function.Surjective f)
    (p : J →ₐ[k] A) (x : HopfLieVector k J k) :
    let ψ := hopfLiePullback (f : H →ₐ[k] J) (BialgHomClass.counitAlgHom_comp f)
    let X := (Algebra.ofId k A).toLinearMap.comp x
    let Y := (Algebra.ofId k A).toLinearMap.comp (ψ x)
    hopfAdjoint (p.comp (f : H →ₐ[k] J)) Y = Y ↔ hopfAdjoint p X = X := by
  intro ψ X Y
  let ψ' := hopfLiePullback (f : H →ₐ[k] J) (BialgHomClass.counitAlgHom_comp f) (A := A)
  have hY : ψ' X = Y := hopfLiePullback_postcompose f (Algebra.ofId k A) x
  rw [← hY, ← hopfLiePullback_adjoint_bialg f p X]
  exact (hopfLiePullback_injective _ _ hf).eq_iff

end Naturality

section Quotients

variable {k H J ι η : Type*} [Field k] [CommRing H] [HopfAlgebra k H] [CommRing J] [HopfAlgebra k J]
  [Fintype ι] [DecidableEq ι] [Fintype η] [DecidableEq η]

set_option maxHeartbeats 1000000 in
/-- An isomorphism of Hopf coordinates transports the actual adjoint centralizer. -/
def bialgEquiv_hopfAdjointCentralizer_pullback (e : H ≃ₐc[k] J)
    (b : Basis ι k (HopfCotangent k H)) (c : Basis η k (HopfCotangent k J))
    (x : HopfLieVector k J k) :
    let y := hopfLiePullback (e.toBialgHom : H →ₐ[k] J) (BialgHomClass.counitAlgHom_comp e.toBialgHom) x
    letI := (hopfAdjointCentralizerIdeal_isHopf b y).quotientHopf
    letI := (hopfAdjointCentralizerIdeal_isHopf c x).quotientHopf
    (H ⧸ hopfAdjointCentralizerIdeal b y) ≃ₐc[k] (J ⧸ hopfAdjointCentralizerIdeal c x) := by
  intro y
  let I := hopfAdjointCentralizerIdeal b y
  let Q := hopfAdjointCentralizerIdeal c x
  let hI := hopfAdjointCentralizerIdeal_isHopf b y
  let hQ := hopfAdjointCentralizerIdeal_isHopf c x
  letI := hI.quotientHopf
  letI := hQ.quotientHopf
  let f := e.toBialgHom
  let jI : H →ₐ[k] H ⧸ I := Ideal.Quotient.mkₐ k I
  let jQ : J →ₐ[k] J ⧸ Q := Ideal.Quotient.mkₐ k Q
  let p : H →ₐc[k] J ⧸ Q := hQ.quotientBialgHom.comp f
  have hp : Function.Surjective p := (Ideal.Quotient.mkₐ_surjective k Q).comp e.surjective
  let S₁ := hopfAdjointCentralizerPoints (A := J ⧸ Q) b y
  let S₂ := hopfAdjointCentralizerPoints (A := H ⧸ I) c x
  have hp₀ : hopfAdjoint jQ ((Algebra.ofId k (J ⧸ Q)).toLinearMap.comp x) =
      (Algebra.ofId k (J ⧸ Q)).toLinearMap.comp x :=
    ((hopfAdjointCentralizerPoints (A := J ⧸ Q) c x) (AlgHom.id k _)).prop
  have hP := (adjoint_rational_fixed_iff_pullback f e.surjective jQ x).mpr hp₀
  let p' := S₁.symm ⟨jQ.comp (f : H →ₐ[k] J), hP⟩
  have hp' : p'.comp jI = jQ.comp (f : H →ₐ[k] J) :=
    congrArg Subtype.val (S₁.apply_symm_apply _)
  let q : J →ₐ[k] H ⧸ I := jI.comp e.symm.toAlgEquiv.toAlgHom
  have hq : q.comp (f : H →ₐ[k] J) = jI := by
    apply AlgHom.ext
    intro h
    exact congrArg jI (e.symm_apply_apply h)
  have hQ₀ : hopfAdjoint jI ((Algebra.ofId k (H ⧸ I)).toLinearMap.comp y) =
      (Algebra.ofId k (H ⧸ I)).toLinearMap.comp y :=
    ((hopfAdjointCentralizerPoints (A := H ⧸ I) b y) (AlgHom.id k _)).prop
  have hQ' := (adjoint_rational_fixed_iff_pullback f e.surjective q x)
  rw [hq] at hQ'
  let q' := S₂.symm ⟨q, hQ'.mp hQ₀⟩
  have hq' : q'.comp jQ = q := congrArg Subtype.val (S₂.apply_symm_apply _)
  apply bialgEquiv_quotientOfKerEq hI p hp
  apply Ideal.ext
  intro h
  have h₁ : p' (jI h) = p h := DFunLike.congr_fun hp' h
  have h₂ : q' (p h) = jI h :=
    (DFunLike.congr_fun hq' (f h)).trans (DFunLike.congr_fun hq h)
  change h ∈ I ↔ p h = 0
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change jI h = 0 ↔ p h = 0
  constructor
  · intro hzero
    rw [← h₁, hzero, map_zero]
  · intro hzero
    rw [← h₂, hzero, map_zero]

end Quotients

end WideE
