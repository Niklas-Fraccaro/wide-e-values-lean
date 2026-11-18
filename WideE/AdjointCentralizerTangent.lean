import WideE.HopfLieDerivation

/-! The tangent space of the actual adjoint stabilizer is the kernel of the orbit derivative. -/

noncomputable section

open scoped Matrix

namespace WideE

section Pullback

variable {F H K A : Type*} [Field F] [CommRing H] [CommRing K]
  [HopfAlgebra F H] [HopfAlgebra F K] [CommRing A] [Algebra F A]

/-- Precomposition by a counit-preserving morphism pulls back Lie vectors. -/
def hopfLiePullback (π : H →ₐ[F] K)
    (he : (Bialgebra.counitAlgHom F K).comp π = Bialgebra.counitAlgHom F H) :
    HopfLieVector F K A →ₗ[F] HopfLieVector F H A := by
  let f : hopfCounitDerivations F K A →ₗ[F] hopfCounitDerivations F H A :=
    { toFun := fun y => ⟨y.val.comp π.toLinearMap, fun a b => by
        change y.val (π (a * b)) = Bialgebra.counitAlgHom F H a • y.val (π b) +
          Bialgebra.counitAlgHom F H b • y.val (π a)
        rw [map_mul, hopfCounitDerivations_mul,
          show Bialgebra.counitAlgHom F K (π a) = Bialgebra.counitAlgHom F H a from
            DFunLike.congr_fun he a,
          show Bialgebra.counitAlgHom F K (π b) = Bialgebra.counitAlgHom F H b from
            DFunLike.congr_fun he b]⟩
      map_add' := fun _ _ => Subtype.ext (LinearMap.ext fun _ => rfl)
      map_smul' := fun _ _ => Subtype.ext (LinearMap.ext fun _ => rfl) }
  exact (hopfLieDerivationEquiv F H A).symm.toLinearMap.comp
    (f.comp (hopfLieDerivationEquiv F K A).toLinearMap)

theorem hopfLiePullback_projection (π : H →ₐ[F] K)
    (he : (Bialgebra.counitAlgHom F K).comp π = Bialgebra.counitAlgHom F H)
    (y : HopfLieVector F K A) (a : H) :
    hopfLiePullback π he y (hopfCotangentProjection F H a) =
      y (hopfCotangentProjection F K (π a)) := by
  unfold hopfLiePullback
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hopfLieDerivationEquiv_symm_apply]
  rfl

theorem hopfLieInfinitesimalPoint_pullback (π : H →ₐ[F] K)
    (he : (Bialgebra.counitAlgHom F K).comp π = Bialgebra.counitAlgHom F H)
    (y : HopfLieVector F K A) :
    hopfLieInfinitesimalPoint (hopfLiePullback π he y) = (hopfLieInfinitesimalPoint y).comp π := by
  apply AlgHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · simp only [hopfLieInfinitesimalPoint_fst, AlgHom.comp_apply]
    exact congrArg (algebraMap F A) (DFunLike.congr_fun he a).symm
  · simp only [hopfLieInfinitesimalPoint_snd, AlgHom.comp_apply, hopfLiePullback_projection]

theorem hopfLiePullback_injective (π : H →ₐ[F] K)
    (he : (Bialgebra.counitAlgHom F K).comp π = Bialgebra.counitAlgHom F H)
    (hπ : Function.Surjective π) : Function.Injective (hopfLiePullback (A := A) π he) := by
  intro x y h
  apply LinearMap.ext
  intro v
  obtain ⟨a, rfl⟩ := hopfCotangentProjection_surjective F K v
  obtain ⟨b, rfl⟩ := hπ a
  rw [← hopfLiePullback_projection π he, ← hopfLiePullback_projection π he, h]

end Pullback

section Centralizer

variable {F H A ι : Type*} [Field F] [CommRing H] [HopfAlgebra F H] [CommRing A] [Algebra F A]
  [Fintype ι] [DecidableEq ι]

local notation "C" => HopfCotangent F H

/-- The orbit derivative as a linear map from the tangent Lie space. -/
def hopfAdjointTangentLinearMap (b : Basis ι F C) (x : ι → A) :
    HopfLieVector F H A →ₗ[F] (ι → A) where
  toFun y := hopfAdjointTangentMatrix b x *ᵥ (fun i => y (b i))
  map_add' y z := by
    change hopfAdjointTangentMatrix b x *ᵥ ((fun i => y (b i)) + (fun i => z (b i))) = _
    exact Matrix.mulVec_add _ _ _
  map_smul' c y := by
    change hopfAdjointTangentMatrix b x *ᵥ (c • fun i => y (b i)) = _
    exact Matrix.mulVec_smul _ _ _

omit [DecidableEq ι] in
@[simp]
theorem hopfAdjointTangentLinearMap_apply (b : Basis ι F C) (x : ι → A)
    (y : HopfLieVector F H A) :
    hopfAdjointTangentLinearMap b x y =
      hopfAdjointTangentMatrix b x *ᵥ (fun i => y (b i)) := rfl

/-- The cotangent dual of the scheme-theoretic centralizer is identified
with the kernel of the derivative of its orbit map. -/
def hopfAdjointCentralizerTangentEquiv (b : Basis ι F C) (x : HopfLieVector F H F) :
    let hJ := hopfAdjointCentralizerIdeal_isHopf b x
    letI := hJ.quotientHopf
    HopfLieVector F (H ⧸ hopfAdjointCentralizerIdeal b x) A ≃ₗ[F]
      LinearMap.ker (hopfAdjointTangentLinearMap b (fun i => algebraMap F A (x (b i)))) := by
  let J := hopfAdjointCentralizerIdeal b x
  let K := H ⧸ J
  let hJ := hopfAdjointCentralizerIdeal_isHopf b x
  letI := hJ.quotientHopf
  let π := Ideal.Quotient.mkₐ F J
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective F J
  have he : (Bialgebra.counitAlgHom F K).comp π = Bialgebra.counitAlgHom F H :=
    BialgHomClass.counitAlgHom_comp hJ.quotientBialgHom
  let xA : HopfLieVector F H A := (Algebra.ofId F A).toLinearMap.comp x
  let D := hopfAdjointTangentLinearMap b (fun i => xA (b i))
  let e := hopfAdjointCentralizerPoints (A := DualNumber A) b x
  have hxDual : hopfLieVector_toDual xA = (Algebra.ofId F (DualNumber A)).toLinearMap.comp x := by
    apply LinearMap.ext
    intro a
    exact (IsScalarTower.algebraMap_apply F A (DualNumber A) (x a)).symm
  let f : HopfLieVector F K A →ₗ[F] HopfLieVector F H A := hopfLiePullback π he
  have hf (u : HopfLieVector F K A) : f u ∈ LinearMap.ker D := by
    rw [LinearMap.mem_ker, hopfAdjointTangentLinearMap_apply]
    apply (hopfAdjoint_infinitesimal_eq_iff b xA (f u)).mp
    rw [show hopfLieInfinitesimalPoint (f u) = (hopfLieInfinitesimalPoint u).comp π from
      hopfLieInfinitesimalPoint_pullback π he u, hxDual]
    exact (e (hopfLieInfinitesimalPoint u)).prop
  let f' := f.codRestrict (LinearMap.ker D) hf
  refine LinearEquiv.ofBijective f' ⟨?_, ?_⟩
  · intro u v h
    exact hopfLiePullback_injective π he hπ (congrArg Subtype.val h)
  · intro v₀
    let v := v₀.val
    have hv : hopfAdjointTangentMatrix b (fun i => xA (b i)) *ᵥ (fun i => v (b i)) = 0 :=
      by simpa only [D, hopfAdjointTangentLinearMap_apply] using LinearMap.mem_ker.mp v₀.prop
    have hFix₀ := (hopfAdjoint_infinitesimal_eq_iff b xA v).mpr hv
    rw [hxDual] at hFix₀
    let z : {p : H →ₐ[F] DualNumber A // hopfAdjoint p
        ((Algebra.ofId F (DualNumber A)).toLinearMap.comp x) =
          (Algebra.ofId F (DualNumber A)).toLinearMap.comp x} :=
      ⟨hopfLieInfinitesimalPoint v, hFix₀⟩
    let p := e.symm z
    have hP : p.comp π = hopfLieInfinitesimalPoint v :=
      congrArg Subtype.val (e.apply_symm_apply z)
    have hFst (a : K) : (p a).fst = algebraMap F A (Bialgebra.counitAlgHom F K a) := by
      obtain ⟨s, rfl⟩ := hπ a
      rw [show p (π s) = hopfLieInfinitesimalPoint v s from DFunLike.congr_fun hP s,
        hopfLieInfinitesimalPoint_fst,
        show Bialgebra.counitAlgHom F K (π s) = Bialgebra.counitAlgHom F H s from
          DFunLike.congr_fun he s]
    let u := (hopfInfinitesimalPointEquiv F K A).symm ⟨p, hFst⟩
    have hu : hopfLieInfinitesimalPoint u = p :=
      congrArg Subtype.val ((hopfInfinitesimalPointEquiv F K A).apply_symm_apply ⟨p, hFst⟩)
    refine ⟨u, Subtype.ext ?_⟩
    apply LinearMap.ext
    intro t
    obtain ⟨s, rfl⟩ := hopfCotangentProjection_surjective F H t
    have h := hopfLieInfinitesimalPoint_pullback π he u
    rw [hu, hP] at h
    exact congrArg (fun g : H →ₐ[F] DualNumber A => (g s).snd) h

end Centralizer

end WideE
