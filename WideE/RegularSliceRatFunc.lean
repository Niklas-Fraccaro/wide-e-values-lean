import WideE.AdjointSliceDescent
import WideE.AdjointCentralizerBaseChange
import WideE.AdjointCentralizerTransport
import WideE.HopfScalarTower

/-! Descent of a constant group's cocycle from a stable regular adjoint slice. -/

noncomputable section

open scoped TensorProduct
open Module

namespace WideE

attribute [local instance] hopfScalarExtension

section ScalarExtension

variable {k F Ω H : Type*} [Field k] [Field F] [Field Ω] [CommRing H] [HopfAlgebra k H]
  [Algebra k F] [Algebra k Ω] [Algebra F Ω] [IsScalarTower k F Ω]

local notation "H₀" => (F ⊗[k] H)
local notation "H₁" => (Ω ⊗[k] H)
local notation "H₂" => (Ω ⊗[F] H₀)

private theorem existsUnique_adjoint_baseChange (slice : Set (HopfLieVector k H Ω))
    (x : HopfLieVector k H Ω)
    (h : ∃! y : HopfLieVector k H Ω, y ∈ slice ∧ ∃ g : H →ₐ[k] Ω, hopfAdjoint g y = x) :
    let φ := hopfLieVectorBaseChange (k := k) (F := F) (H := H) (B := Ω)
    ∃! y : HopfLieVector F H₀ Ω, y ∈ φ '' slice ∧ ∃ g : H₀ →ₐ[F] Ω, hopfAdjoint g y = φ x := by
  intro φ
  letI := hopfPointGroup (k := k) (H := H) (A := Ω)
  letI := hopfPointGroup (k := F) (H := H₀) (A := Ω)
  let ψ := scalarExtendPointMulEquiv (k := k) (F := F) (H := H) (B := Ω)
  obtain ⟨y, ⟨hy, p, hp⟩, hUnique⟩ := h
  refine ⟨φ y, ⟨⟨y, hy, rfl⟩, ψ p, ?_⟩, ?_⟩
  · exact (hopfLieVectorBaseChange_adjoint p y).symm.trans (congrArg φ hp)
  · rintro _ ⟨⟨z, hz, rfl⟩, q, hq⟩
    obtain ⟨q₀, rfl⟩ := ψ.surjective q
    apply congrArg φ
    refine hUnique z ⟨hz, q₀, φ.injective ?_⟩
    exact (hopfLieVectorBaseChange_adjoint q₀ z).trans hq

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 120000 in
private def centralizerTorusSplitting_scalarTower {ι Λ : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommGroup Λ]
    (b : Basis ι k (HopfCotangent k H)) (Y : HopfLieVector F H₀ F) (y : HopfLieVector k H Ω)
    (hY : hopfLieVectorBaseChange (F := F) y = (Algebra.ofId F Ω).toLinearMap.comp Y)
    (t : let bΩ := hopfCotangentBasisBaseChange (F := Ω) b
         let yΩ := hopfLieVectorBaseChange (F := Ω) y
         letI := (hopfAdjointCentralizerIdeal_isHopf bΩ yΩ).quotientHopf
         (H₁ ⧸ hopfAdjointCentralizerIdeal bΩ yΩ) ≃ₐc[Ω] MonoidAlgebra Ω (Multiplicative Λ)) :
    let bF := hopfCotangentBasisBaseChange (F := F) b
    letI := (hopfAdjointCentralizerIdeal_isHopf bF Y).quotientHopf
    TorusHopfSplitting F Ω (H₀ ⧸ hopfAdjointCentralizerIdeal bF Y) (Multiplicative Λ) := by
  intro bF
  let bΩ := hopfCotangentBasisBaseChange (F := Ω) b
  let b₂ := hopfCotangentBasisBaseChange (F := Ω) bF
  let yΩ := hopfLieVectorBaseChange (F := Ω) y
  let YΩ := hopfLieVectorBaseChangeRational (F := Ω) Y
  let e : H₁ ≃ₐc[Ω] H₂ := scalarExtendBialgCancelBaseChange.symm
  let w := hopfLiePullback (e.toBialgHom : H₁ →ₐ[Ω] H₂) (BialgHomClass.counitAlgHom_comp e.toBialgHom) YΩ
  have hw : w = yΩ := by
    change hopfLiePullback (e.toBialgHom : H₁ →ₐ[Ω] H₂) (BialgHomClass.counitAlgHom_comp e.toBialgHom)
      (hopfLieVectorBaseChange (F := Ω) ((Algebra.ofId F Ω).toLinearMap.comp Y)) = yΩ
    rw [← hY]
    exact hopfLieVectorBaseChange_cancel y
  let d (z : HopfLieVector Ω H₁ Ω) :=
    letI := (hopfAdjointCentralizerIdeal_isHopf bΩ z).quotientHopf
    letI := (hopfAdjointCentralizerIdeal_isHopf b₂ YΩ).quotientHopf
    (H₁ ⧸ hopfAdjointCentralizerIdeal bΩ z) ≃ₐc[Ω] (H₂ ⧸ hopfAdjointCentralizerIdeal b₂ YΩ)
  have e' : d w := bialgEquiv_hopfAdjointCentralizer_pullback e bΩ b₂ YΩ
  have eΩ : d yΩ := hw ▸ e'
  letI : HopfAlgebra F (H₀ ⧸ hopfAdjointCentralizerIdeal bF Y) :=
    (hopfAdjointCentralizerIdeal_isHopf bF Y).quotientHopf
  letI : HopfAlgebra Ω (H₁ ⧸ hopfAdjointCentralizerIdeal bΩ yΩ) :=
    (hopfAdjointCentralizerIdeal_isHopf bΩ yΩ).quotientHopf
  letI : HopfAlgebra Ω (H₂ ⧸ hopfAdjointCentralizerIdeal b₂ YΩ) :=
    (hopfAdjointCentralizerIdeal_isHopf b₂ YΩ).quotientHopf
  exact (hopfAdjointCentralizerBaseChange (F := Ω) bF Y).trans (eΩ.symm.trans t)

end ScalarExtension

section RationalFunction

variable {k Ω H ι ν Λ : Type*} [Field k] [CharZero k] [IsAlgClosed k] [Field Ω]
  [Algebra k Ω] [Algebra (RatFunc k) Ω] [IsScalarTower k (RatFunc k) Ω]
  [IsAlgClosed Ω] [IsGalois (RatFunc k) Ω]
  [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
  [Fintype ι] [DecidableEq ι] [Finite ν] [AddCommGroup Λ]

local notation "F₀" => RatFunc k
local notation "H₀" => (F₀ ⊗[k] H)
local notation "H₁" => (Ω ⊗[k] H)

set_option maxHeartbeats 1800000 in
set_option synthInstance.maxHeartbeats 120000 in
/-- A stable choice of a geometric representative on a regular open set with
toric stabilizers trivializes the actual cocycle over the rational function field. -/
theorem isHopfPointCoboundary_of_stable_regularSlice_ratFunc
    (b : Basis ι k (HopfCotangent k H)) (f : MvPolynomial ι k) (hf : f ≠ 0)
    (slice : Set (HopfLieVector k H Ω))
    (hStable : ∀ (σ : Ω ≃ₐ[F₀] Ω) y, y ∈ slice → (σ.toAlgHom.restrictScalars k).toLinearMap.comp y ∈ slice)
    (hSlice : ∀ x : HopfLieVector k H Ω, MvPolynomial.aeval (fun i => x (b i)) f ≠ 0 →
      ∃! y : HopfLieVector k H Ω, y ∈ slice ∧ ∃ g : H →ₐ[k] Ω, hopfAdjoint g y = x)
    (basis : Basis ν ℤ Λ)
    (hTorus : ∀ y ∈ slice,
      let bΩ := hopfCotangentBasisBaseChange (F := Ω) b
      let yΩ := hopfLieVectorBaseChange (F := Ω) y
      letI := (hopfAdjointCentralizerIdeal_isHopf bΩ yΩ).quotientHopf
      Nonempty ((H₁ ⧸ hopfAdjointCentralizerIdeal bΩ yΩ) ≃ₐc[Ω] MonoidAlgebra Ω (Multiplicative Λ)))
    (E : FiniteGaloisIntermediateField F₀ Ω) (c : (E ≃ₐ[F₀] E) → H →ₐ[k] E)
    (hc : IsHopfPointCocycle c) : IsHopfPointCoboundary c := by
  letI : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap k F₀).injective
  letI : Algebra.FiniteType F₀ H₀ := Algebra.FiniteType.baseChange (R := k) F₀
  let bF := hopfCotangentBasisBaseChange (F := F₀) b
  let cF := scalarExtendHopfPointCocycle c
  have hcF : IsHopfPointCocycle cF := (isHopfPointCocycle_scalarExtend_iff c).mpr hc
  let p := MvPolynomial.map (algebraMap k E) f
  have hp : p ≠ 0 := by
    intro h
    exact hf (MvPolynomial.map_injective _ (algebraMap k E).injective (h.trans (map_zero _).symm))
  obtain ⟨X, hX, hFixed⟩ := exists_twistedHopfLieVector_eval_ne_zero bF E cF hcF p hp
  let iE := E.toIntermediateField.val
  let φE := hopfLieVectorBaseChange (k := k) (F := F₀) (H := H) (B := E)
  let φΩ := hopfLieVectorBaseChange (k := k) (F := F₀) (H := H) (B := Ω)
  let xE := φE.symm X
  let x := (iE.restrictScalars k).toLinearMap.comp xE
  have hΦ : φΩ x = iE.toLinearMap.comp X := by
    change hopfLieVectorBaseChange (F := F₀) ((iE.restrictScalars k).toLinearMap.comp xE) = _
    rw [hopfLieVectorBaseChange_postcompose]
    exact congrArg (fun X' => iE.toLinearMap.comp X') (φE.apply_symm_apply X)
  have hXbasis (j : ι) : X (bF j) = xE (b j) :=
    (congrArg (fun z : HopfLieVector F₀ H₀ E => z (bF j)) (φE.apply_symm_apply X)).symm.trans
      (hopfLieVectorBaseChange_basis b xE j)
  have hx : MvPolynomial.aeval (fun j => x (b j)) f ≠ 0 := by
    have hScalar : (iE.toRingHom).comp (algebraMap k E) = algebraMap k Ω :=
      RingHom.ext fun z => (iE.restrictScalars k).commutes z
    have hCoordinates : (iE.toRingHom : E → Ω) ∘ (fun j => X (bF j)) = fun j => x (b j) :=
      funext fun j => congrArg iE (hXbasis j)
    have hValue : iE (MvPolynomial.eval (fun j => X (bF j)) p) =
        MvPolynomial.aeval (fun j => x (b j)) f := by
      change iE.toRingHom (MvPolynomial.eval (fun j => X (bF j)) p) =
        MvPolynomial.eval₂ (algebraMap k Ω) (fun j => x (b j)) f
      rw [MvPolynomial.eval₂_comp, hCoordinates, MvPolynomial.eval₂_map, hScalar]
    exact hValue ▸ fun h => hX (iE.injective (h.trans (map_zero iE).symm))
  let sliceF := φΩ '' slice
  have hStableF (σ : Ω ≃ₐ[F₀] Ω) (y : HopfLieVector F₀ H₀ Ω) (hy : y ∈ sliceF) :
      σ.toAlgHom.toLinearMap.comp y ∈ sliceF := by
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨_, hStable σ z hz, hopfLieVectorBaseChange_postcompose σ.toAlgHom z⟩
  have hSliceF := existsUnique_adjoint_baseChange (F := F₀) slice x (hSlice x hx)
  change ∃! y : HopfLieVector F₀ H₀ Ω, y ∈ sliceF ∧ ∃ g : H₀ →ₐ[F₀] Ω, hopfAdjoint g y = φΩ x at hSliceF
  rw [hΦ] at hSliceF
  obtain ⟨Y, g, hY, hg⟩ :=
    exists_rationalHopfLieVector_of_unique_stable_representative bF E cF X hFixed sliceF hStableF hSliceF
  obtain ⟨y, hy, hyY⟩ := hY
  obtain ⟨t⟩ := hTorus y hy
  have tY := centralizerTorusSplitting_scalarTower b Y y hyY t
  apply (isHopfPointCoboundary_scalarExtend_iff c).mp
  exact isHopfPointCoboundary_of_geometricToricAdjointCentralizer (ratFunc_isC1 k)
    (fun _ hn => primitiveRoots_nonempty_of_algClosed_subfield (k := k) hn) basis bF E cF hcF
    X Y g hg hFixed tY

end RationalFunction

end WideE
