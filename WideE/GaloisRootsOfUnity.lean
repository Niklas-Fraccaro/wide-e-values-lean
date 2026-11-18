import WideE.GaloisCrossedProduct
import WideE.MatrixHilbert90

/-!
# Vanishing of root-of-unity cocycles after a finite extension

The unit-valued coboundary supplied by C₁ matrix splitting can be corrected
to take values in the same roots of unity after adjoining one root.
-/

noncomputable section

namespace WideE

open IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The scalar case of matrix Hilbert 90, in the unit-valued cocycle convention. -/
theorem unitHilbert90 [FiniteDimensional F E] (f : (E ≃ₐ[F] E) → Eˣ)
    (hf : ∀ σ τ, f (σ * τ) = f σ * (σ • f τ)) :
    ∃ a : Eˣ, ∀ σ, (σ • a) / a = f σ := by
  let c (σ : E ≃ₐ[F] E) : (Matrix (Fin 1) (Fin 1) E)ˣ :=
    Units.map (Matrix.scalar (Fin 1)).toMonoidHom (f σ)
  have hMap (σ : E ≃ₐ[F] E) (x : E) :
      (Matrix.scalar (Fin 1) x).map σ = Matrix.scalar (Fin 1) (σ x) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.scalar_apply]
  have hc (σ τ : E ≃ₐ[F] E) : (c (σ * τ) : Matrix (Fin 1) (Fin 1) E) =
      (c σ : Matrix (Fin 1) (Fin 1) E) * (c τ : Matrix (Fin 1) (Fin 1) E).map σ := by
    change Matrix.scalar (Fin 1) (f (σ * τ) : E) =
      Matrix.scalar (Fin 1) (f σ : E) * (Matrix.scalar (Fin 1) (f τ : E)).map σ
    rw [hMap, ← map_mul, hf, Units.val_mul]
    rfl
  obtain ⟨B, hB⟩ := matrixHilbert90 c hc
  let b : Eˣ := Units.map Matrix.detMonoidHom B
  have hb (σ : E ≃ₐ[F] E) : f σ * (σ • b) = b := by
    apply Units.ext
    have h := congrArg Matrix.det (hB σ)
    have hMapDet : ((B : Matrix (Fin 1) (Fin 1) E).map σ).det =
        σ ((B : Matrix (Fin 1) (Fin 1) E).det) :=
      (RingHom.map_det σ.toRingHom (B : Matrix (Fin 1) (Fin 1) E)).symm
    rw [Matrix.det_mul, hMapDet] at h
    change (Matrix.scalar (Fin 1) (f σ : E)).det * σ (b : E) = (b : E) at h
    simpa [Matrix.det_fin_one, Matrix.scalar_apply] using h
  refine ⟨b⁻¹, fun σ => ?_⟩
  rw [smul_inv', div_eq_mul_inv, inv_inv, mul_comm, ← div_eq_mul_inv]
  exact (div_eq_iff_eq_mul').mpr ((hb σ).symm.trans (mul_comm _ _))

namespace GaloisTwoCocycle

section Inflation

variable {L : Type*} [Field L] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
variable [Normal F E]

private theorem map_restrictNormalHom_smul (σ : L ≃ₐ[F] L) (u : Eˣ) :
    Units.map (algebraMap E L).toMonoidHom ((AlgEquiv.restrictNormalHom E σ) • u) =
      σ • Units.map (algebraMap E L).toMonoidHom u :=
  Units.ext (σ.restrictNormal_commutes E (u : E))

/-- Inflation of a unit-valued 2-cocycle to a larger field. -/
def inflate (c : GaloisTwoCocycle F E) : GaloisTwoCocycle F L where
  value σ τ := Units.map (algebraMap E L).toMonoidHom
    (c.value (AlgEquiv.restrictNormalHom E σ) (AlgEquiv.restrictNormalHom E τ))
  one_left σ := by simp
  one_right σ := by simp
  cocycle σ τ ρ := by
    let i := Units.map (algebraMap E L).toMonoidHom
    let r := AlgEquiv.restrictNormalHom (F := F) (K₁ := L) E
    change i (c.value (r σ) (r τ)) * i (c.value (r (σ * τ)) (r ρ)) =
      (σ • i (c.value (r τ) (r ρ))) * i (c.value (r σ) (r (τ * ρ)))
    rw [← map_mul i, ← map_restrictNormalHom_smul, ← map_mul i, map_mul r, map_mul r, c.cocycle]

private theorem inflate_has_rootsOfUnity_coboundary
    (c : GaloisTwoCocycle F E) {n : ℕ}
    (b : (E ≃ₐ[F] E) → Eˣ) (a : Eˣ) (v : Lˣ)
    (hb : ∀ σ τ, c.value σ τ = b σ * (σ • b τ) / b (σ * τ))
    (ha : ∀ σ : E ≃ₐ[F] E, (σ • a) / a = b σ ^ n)
    (hv : v ^ n = Units.map (algebraMap E L).toMonoidHom a) :
    ∃ d : (L ≃ₐ[F] L) → Lˣ, (∀ σ, d σ ^ n = 1) ∧
      ∀ σ τ, (c.inflate (L := L)).value σ τ = d σ * Units.map σ.toRingEquiv.toMonoidHom (d τ) / d (σ * τ) := by
  let i := Units.map (algebraMap E L).toMonoidHom
  let r := AlgEquiv.restrictNormalHom (F := F) (K₁ := L) E
  let lift (σ : L ≃ₐ[F] L) := i (b (r σ))
  let adjust (σ : L ≃ₐ[F] L) := v / (σ • v)
  refine ⟨fun σ => lift σ * adjust σ, ?_, ?_⟩
  · intro σ
    change (i (b (r σ)) * (v / (σ • v))) ^ n = 1
    rw [mul_pow, ← map_pow, ← ha, map_div, div_pow, ← smul_pow', hv]
    change (i ((AlgEquiv.restrictNormalHom E σ) • a) / i a) * (i a / (σ • i a)) = 1
    rw [map_restrictNormalHom_smul, div_mul_div_cancel, div_self']
  · intro σ τ
    have hAdjust : adjust σ * (σ • adjust τ) = adjust (σ * τ) := by
      dsimp only [adjust]
      rw [smul_div', ← mul_smul, div_mul_div_cancel]
    change i (c.value (r σ) (r τ)) =
      (lift σ * adjust σ) * (σ • (lift τ * adjust τ)) / (lift (σ * τ) * adjust (σ * τ))
    rw [smul_mul', mul_mul_mul_comm (lift σ), ← div_mul_div_comm, hAdjust, div_self', mul_one]
    change i (c.value (r σ) (r τ)) = i (b (r σ)) * (σ • i (b (r τ))) / i (b (r (σ * τ)))
    rw [show (σ • i (b (r τ))) = i ((r σ) • b (r τ)) from
      (map_restrictNormalHom_smul σ (b (r τ))).symm, map_mul r, ← map_mul i, ← map_div i, hb]

end Inflation

/-- A root-of-unity 2-cocycle over a finite Galois extension of a characteristic-zero
C₁ field acquires a root-of-unity-valued coboundary after a finite Galois extension. -/
theorem exists_finiteGalois_rootsOfUnity_coboundary [CharZero F]
    {Ω : Type*} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] [IsGalois F Ω]
    {E : IntermediateField F Ω} [FiniteDimensional F E] [IsGalois F E]
    (c : GaloisTwoCocycle F E) (hF : IsC1 F) {n : ℕ} (hn : 0 < n)
    (hc : ∀ σ τ, c.value σ τ ^ n = 1) :
    ∃ (L : IntermediateField F Ω) (hEL : E ≤ L),
      FiniteDimensional F L ∧ IsGalois F L ∧
      (letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
       letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' rfl
       ∃ d : (L ≃ₐ[F] L) → Lˣ, (∀ σ, d σ ^ n = 1) ∧
         ∀ σ τ, (c.inflate (L := L)).value σ τ =
           d σ * Units.map σ.toRingEquiv.toMonoidHom (d τ) / d (σ * τ)) := by
  obtain ⟨b, hb⟩ := c.isCoboundary_of_isC1 hF
  have hbPow (σ τ : E ≃ₐ[F] E) :
      b (σ * τ) ^ n = b σ ^ n * Units.map σ.toRingEquiv.toMonoidHom (b τ ^ n) := by
    have h := congrArg (fun u : Eˣ => u ^ n) (hb σ τ)
    dsimp only at h
    rw [hc, div_pow, mul_pow, ← smul_pow'] at h
    exact (div_eq_one.mp h.symm).symm
  obtain ⟨a, ha⟩ := unitHilbert90 (fun σ => b σ ^ n) hbPow
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq ((a : E) : Ω) hn
  let D := E ⊔ IntermediateField.adjoin F ({v} : Set Ω)
  letI : FiniteDimensional F (IntermediateField.adjoin F ({v} : Set Ω)) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral v)
  letI : FiniteDimensional F D := inferInstance
  let L := normalClosure F D Ω
  have hDL : D ≤ L := IntermediateField.le_normalClosure D
  have hEL : E ≤ L := le_sup_left.trans hDL
  have hAdjoinLe : IntermediateField.adjoin F ({v} : Set Ω) ≤ D := le_sup_right
  have hvL : v ∈ L := hDL (hAdjoinLe (IntermediateField.subset_adjoin F _ rfl))
  refine ⟨L, hEL, normalClosure.is_finiteDimensional F D Ω, inferInstance, ?_⟩
  letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
  letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' rfl
  let w : L := ⟨v, hvL⟩
  have hw : w ^ n = algebraMap E L (a : E) := Subtype.ext hv
  have hwne : w ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hw
    exact a.ne_zero ((algebraMap E L).injective (hw.symm.trans (map_zero _).symm))
  exact inflate_has_rootsOfUnity_coboundary c b a (Units.mk0 w hwne) hb ha (Units.ext hw)

end GaloisTwoCocycle

end WideE
