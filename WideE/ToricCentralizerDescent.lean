import WideE.TorusHopfCoordinates
import WideE.TwistedRegularPoint
import WideE.VectorStabilizer
import WideE.GaloisInflation
import Mathlib.Algebra.CharZero.Infinite

/-!
# Descent of a Hopf point cocycle through a toric vector stabilizer

Conjugating a twisted fixpoint to a rational vector changes the cocycle
to one in the closed stabilizer of that vector. If the stabilizer has
a specified torus splitting, its torus cocycle trivialization gives
a trivialization in the original group.
-/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 150000

section PointMaps

variable {F L H : Type*} [Field F] [Field L] [Algebra F L]
variable [CommRing H] [HopfAlgebra F H]

private def galoisHopfPointMap (σ : L ≃ₐ[F] L) :
    letI := hopfPointGroup (k := F) (H := H) (A := L)
    (H →ₐ[F] L) →* (H →ₐ[F] L) := by
  letI := hopfPointGroup (k := F) (H := H) (A := L)
  exact {
    toFun := fun p => (σ.toAlgHom.restrictScalars F).comp p
    map_one' := hopfPointOne_postcompose _
    map_mul' := fun p q => hopfPointMul_postcompose _ p q }

private theorem galoisHopfPointMap_one (p : H →ₐ[F] L) :
    galoisHopfPointMap (1 : L ≃ₐ[F] L) p = p :=
  AlgHom.ext fun _ => rfl

private theorem galoisHopfPointMap_mul_apply (σ τ : L ≃ₐ[F] L) (p : H →ₐ[F] L) :
    galoisHopfPointMap (σ * τ) p = galoisHopfPointMap σ (galoisHopfPointMap τ p) :=
  AlgHom.ext fun _ => rfl

variable {J : Type*} [CommRing J] [HopfAlgebra F J]

private def hopfPointPrecompose (m : H →ₐc[F] J) :
    letI := hopfPointGroup (k := F) (H := H) (A := L)
    letI := hopfPointGroup (k := F) (H := J) (A := L)
    (J →ₐ[F] L) →* (H →ₐ[F] L) := by
  letI : Group (H →ₐ[F] L) := hopfPointGroup
  letI : Group (J →ₐ[F] L) := hopfPointGroup
  refine { toFun := fun p => p.comp (m : H →ₐ[F] J), map_one' := ?_, map_mul' := ?_ }
  · apply AlgHom.ext
    intro a
    change algebraMap F L (Coalgebra.counit (R := F) (m a)) =
      algebraMap F L (Coalgebra.counit (R := F) a)
    rw [CoalgHomClass.counit_comp_apply]
  · intro p q
    have hEval (z : H ⊗[F] H) :
        tensorPoint p q (TensorProduct.map m m z) =
          tensorPoint (p.comp (m : H →ₐ[F] J)) (q.comp (m : H →ₐ[F] J)) z := by
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x y => rfl
    apply AlgHom.ext
    intro a
    change tensorPoint p q (Coalgebra.comul (R := F) (m a)) =
      tensorPoint (p.comp (m : H →ₐ[F] J)) (q.comp (m : H →ₐ[F] J)) (Coalgebra.comul (R := F) a)
    rw [← CoalgHomClass.map_comp_comul_apply (R := F) m a, hEval]

end PointMaps

section Descent

variable {F Ω H Λ ι η : Type*} [Field F] [CharZero F] [Field Ω] [Algebra F Ω]
variable [IsAlgClosed Ω] [IsGalois F Ω] [CommRing H] [HopfAlgebra F H]
variable [Fintype ι] [DecidableEq ι] [AddCommGroup Λ] [Finite η]

/-- A cocycle trivializes if a twisted fixed vector is conjugate to a rational
vector whose actual stabilizer has a specified torus splitting. -/
theorem isHopfPointCoboundary_of_toricVectorStabilizer
    (hF : IsC1 F) (hRoots : ∀ n : ℕ, 0 < n → (primitiveRoots n F).Nonempty)
    (basis : Basis η ℤ Λ) (E : FiniteGaloisIntermediateField F Ω)
    (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := F) (U.val i j) = ∑ l, U.val i l ⊗ₜ[F] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := F) (U.val i j) = if i = j then 1 else 0)
    (c : (E ≃ₐ[F] E) → H →ₐ[F] E) (hc : IsHopfPointCocycle c)
    (x : ι → E) (y : ι → F) (a : H →ₐ[F] E)
    (hConj : U.val.map a *ᵥ (algebraMap F E ∘ y) = x)
    (hFixed : ∀ σ, U.val.map (c σ) *ᵥ (σ ∘ x) = x)
    (e : letI := (vectorStabilizerIdeal_isHopf U hD he y).quotientHopf
         TorusHopfSplitting F E (H ⧸ vectorStabilizerIdeal U.val y) (Multiplicative Λ)) :
    IsHopfPointCoboundary c := by
  let I := vectorStabilizerIdeal U.val y
  let Q := H ⧸ I
  let hI := vectorStabilizerIdeal_isHopf U hD he y
  letI : HopfAlgebra F Q := hI.quotientHopf
  letI : Group (H →ₐ[F] E) := hopfPointGroup
  letI : Group (Q →ₐ[F] E) := hopfPointGroup
  let v : ι → E := algebraMap F E ∘ y
  let M : (H →ₐ[F] E) →* (Matrix ι ι E)ˣ := hopfPointMatrix U hD he
  let d (σ : E ≃ₐ[F] E) := a⁻¹ * c σ * galoisHopfPointMap σ a
  have hcOne : c 1 = 1 := hc.1
  have hcMul (σ τ : E ≃ₐ[F] E) : c (σ * τ) = c σ * galoisHopfPointMap σ (c τ) :=
    hc.2 σ τ
  have hdOne : d 1 = 1 := by
    dsimp only [d]
    rw [hcOne, mul_one, galoisHopfPointMap_one, inv_mul_cancel]
  have hdMul (σ τ : E ≃ₐ[F] E) : d (σ * τ) = d σ * galoisHopfPointMap σ (d τ) := by
    dsimp only [d]
    rw [hcMul, galoisHopfPointMap_mul_apply, map_mul, map_mul, map_inv]
    simp only [mul_assoc, mul_inv_cancel_left]
  have hConj' : (M a).val *ᵥ v = x := hConj
  have hg (σ : E ≃ₐ[F] E) : (M (galoisHopfPointMap σ a)).val *ᵥ v = σ ∘ x := by
    change (hopfPointMatrix U hD he ((σ.toAlgHom.restrictScalars F).comp a)).val *ᵥ v = _
    rw [hopfPointMatrix_galois]
    have hV : (σ.toRingHom : E → E) ∘ v = v := funext fun i => σ.commutes (y i)
    have h := funext (RingHom.map_mulVec σ.toRingHom (M a).val v)
    rw [hV, hConj'] at h
    exact h.symm
  have hProd (σ : E ≃ₐ[F] E) : (M (c σ * galoisHopfPointMap σ a)).val *ᵥ v = x := by
    rw [map_mul M, Units.val_mul, ← Matrix.mulVec_mulVec, hg]
    exact hFixed σ
  have hStab (σ : E ≃ₐ[F] E) : U.val.map (d σ) *ᵥ v = v := by
    change (M (a⁻¹ * c σ * galoisHopfPointMap σ a)).val *ᵥ v = v
    rw [mul_assoc, map_mul M, Units.val_mul, ← Matrix.mulVec_mulVec, hProd, ← hConj',
      Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul M, inv_mul_cancel, map_one M,
      Units.val_one, Matrix.one_mulVec]
  let pointEquiv := vectorStabilizerPointEquiv (A := E) U.val y
  let j : (Q →ₐ[F] E) →* (H →ₐ[F] E) := hopfPointPrecompose hI.quotientBialgHom
  let t (σ : E ≃ₐ[F] E) : Q →ₐ[F] E := pointEquiv.symm ⟨d σ, hStab σ⟩
  have ht (σ : E ≃ₐ[F] E) : j (t σ) = d σ :=
    congrArg Subtype.val (pointEquiv.apply_symm_apply ⟨d σ, hStab σ⟩)
  have hInj : Function.Injective j := by
    intro p q h
    apply AlgHom.ext
    intro z
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mkₐ_surjective F I z
    exact DFunLike.congr_fun h w
  have hj (σ : E ≃ₐ[F] E) (b : Q →ₐ[F] E) :
      j (galoisHopfPointMap σ b) = galoisHopfPointMap σ (j b) := AlgHom.ext fun _ => rfl
  have htc : IsHopfPointCocycle t := by
    constructor
    · change t 1 = 1
      apply hInj
      rw [ht, map_one j, hdOne]
    · intro σ τ
      change t (σ * τ) = t σ * galoisHopfPointMap σ (t τ)
      apply hInj
      rw [map_mul j, hj, ht, ht, ht]
      exact hdMul σ τ
  obtain ⟨b, hb⟩ := isHopfPointCoboundary_of_torusHopfSplitting hF hRoots basis E e t htc
  let u := j b
  have hu (σ : E ≃ₐ[F] E) : d σ * galoisHopfPointMap σ u = u := by
    have h := congrArg j (hb σ)
    change j (t σ * galoisHopfPointMap σ b) = u at h
    rw [map_mul j, hj, ht] at h
    exact h
  refine ⟨a * u, fun σ => ?_⟩
  change c σ * galoisHopfPointMap σ (a * u) = a * u
  have hD' : a * d σ = c σ * galoisHopfPointMap σ a := by
    simp only [d, mul_assoc, mul_inv_cancel_left]
  rw [map_mul, ← mul_assoc, ← hD', mul_assoc, hu]

/-- The stabilizer may split over a larger finite Galois field than the
original cocycle. Triviality there descends to the original field. -/
theorem isHopfPointCoboundary_of_toricVectorStabilizer_after_extension
    (hF : IsC1 F) (hRoots : ∀ n : ℕ, 0 < n → (primitiveRoots n F).Nonempty)
    (basis : Basis η ℤ Λ) (E L : FiniteGaloisIntermediateField F Ω) (hEL : E ≤ L)
    (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := F) (U.val i j) = ∑ l, U.val i l ⊗ₜ[F] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := F) (U.val i j) = if i = j then 1 else 0)
    (c : (E ≃ₐ[F] E) → H →ₐ[F] E) (hc : IsHopfPointCocycle c)
    (x : ι → E) (y : ι → F) (a : H →ₐ[F] L)
    (hConj : U.val.map a *ᵥ (algebraMap F L ∘ y) = IntermediateField.inclusion hEL ∘ x)
    (hFixed : ∀ σ, U.val.map (c σ) *ᵥ (σ ∘ x) = x)
    (e : letI := (vectorStabilizerIdeal_isHopf U hD he y).quotientHopf
         TorusHopfSplitting F L (H ⧸ vectorStabilizerIdeal U.val y) (Multiplicative Λ)) :
    IsHopfPointCoboundary c := by
  letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
  letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' rfl
  apply (isHopfPointCoboundary_inflate_iff (L := L) hc).mp
  apply isHopfPointCoboundary_of_toricVectorStabilizer hF hRoots basis L U hD he
    (inflateHopfPointCocycle c) hc.inflate (IntermediateField.inclusion hEL ∘ x) y a hConj _ e
  intro σ
  let j := IntermediateField.inclusion hEL
  let τ := AlgEquiv.restrictNormalHom E σ
  have hσ : (σ : L → L) ∘ (j ∘ x) = j ∘ ((τ : E → E) ∘ x) :=
    funext fun i => (σ.restrictNormal_commutes E (x i)).symm
  change U.val.map (j.comp (c τ)) *ᵥ ((σ : L → L) ∘ (j ∘ x)) = j ∘ x
  calc
    U.val.map (j.comp (c τ)) *ᵥ ((σ : L → L) ∘ (j ∘ x)) =
        j ∘ (U.val.map (c τ) *ᵥ ((τ : E → E) ∘ x)) := by
      rw [hσ]
      exact (funext (RingHom.map_mulVec j.toRingHom (U.val.map (c τ))
        ((τ : E → E) ∘ x))).symm
    _ = j ∘ x := congrArg (fun w : ι → E => j ∘ w) (hFixed τ)

/-- It suffices to conjugate the vectors in one nonempty principal open to
rational vectors with split toric stabilizer after finite Galois enlargement. -/
theorem isHopfPointCoboundary_of_regularVectorConjugacy
    (hF : IsC1 F) (hRoots : ∀ n : ℕ, 0 < n → (primitiveRoots n F).Nonempty)
    (basis : Basis η ℤ Λ) (E : FiniteGaloisIntermediateField F Ω)
    (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := F) (U.val i j) = ∑ l, U.val i l ⊗ₜ[F] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := F) (U.val i j) = if i = j then 1 else 0)
    (c : (E ≃ₐ[F] E) → H →ₐ[F] E) (hc : IsHopfPointCocycle c)
    (p : MvPolynomial ι E) (hp : p ≠ 0)
    (hConjugate : ∀ x : ι → E, MvPolynomial.eval x p ≠ 0 →
      (∀ σ : E ≃ₐ[F] E, U.val.map (c σ) *ᵥ (σ ∘ x) = x) →
      ∃ (L : FiniteGaloisIntermediateField F Ω) (hEL : E ≤ L) (y : ι → F) (a : H →ₐ[F] L),
        U.val.map a *ᵥ (algebraMap F L ∘ y) = IntermediateField.inclusion hEL ∘ x ∧
        Nonempty (letI := (vectorStabilizerIdeal_isHopf U hD he y).quotientHopf
          TorusHopfSplitting F L (H ⧸ vectorStabilizerIdeal U.val y) (Multiplicative Λ))) :
    IsHopfPointCoboundary c := by
  obtain ⟨x, hx, hFixed⟩ := exists_twistedHopfPoint_fixedPoint_eval_ne_zero U hD he c hc p hp
  obtain ⟨L, hEL, y, a, hConj, ⟨e⟩⟩ := hConjugate x hx hFixed
  exact isHopfPointCoboundary_of_toricVectorStabilizer_after_extension hF hRoots basis E L hEL
    U hD he c hc x y a hConj hFixed e

end Descent

end WideE
