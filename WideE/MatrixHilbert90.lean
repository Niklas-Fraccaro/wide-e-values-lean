import WideE.GaloisTorsor
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Matrix Hilbert 90 via Artin independence and a basis of twisted fixed vectors. -/

noncomputable section

open scoped BigOperators Matrix

namespace WideE

variable {F L ι : Type*} [Field F] [Field L] [Algebra F L]
variable [Fintype ι] [DecidableEq ι]

local notation "Γ" => (L ≃ₐ[F] L)

private def twist (c : Γ → (Matrix ι ι L)ˣ) (σ : Γ) (v : ι → L) : ι → L :=
  (c σ : Matrix ι ι L) *ᵥ (σ ∘ v)

private theorem twist_smul (c : Γ → (Matrix ι ι L)ˣ) (σ : Γ) (a : L) (v : ι → L) :
    twist c σ (a • v) = σ a • twist c σ v := by
  have h : (σ : L → L) ∘ (a • v) = σ a • (σ ∘ v) := by
    funext i
    change σ (a * v i) = σ a * σ (v i)
    exact map_mul σ _ _
  simp only [twist, h, Matrix.mulVec_smul]

private theorem twist_mul (c : Γ → (Matrix ι ι L)ˣ)
    (hc : ∀ σ τ : Γ, (c (σ * τ) : Matrix ι ι L) =
      (c σ : Matrix ι ι L) * (c τ : Matrix ι ι L).map σ)
    (σ τ : Γ) (v : ι → L) :
    twist c σ (twist c τ v) = twist c (σ * τ) v := by
  have hMap : σ ∘ twist c τ v =
      ((c τ : Matrix ι ι L).map σ) *ᵥ (σ ∘ τ ∘ v) :=
    funext fun i => RingHom.map_mulVec σ.toRingHom (c τ : Matrix ι ι L) (τ ∘ v) i
  rw [twist, hMap, Matrix.mulVec_mulVec, ← hc σ τ]
  rfl

variable [FiniteDimensional F L]

private def orbitSum (c : Γ → (Matrix ι ι L)ˣ) (v : ι → L) : ι → L :=
  ∑ σ : Γ, twist c σ v

private theorem twist_orbitSum (c : Γ → (Matrix ι ι L)ˣ)
    (hc : ∀ σ τ : Γ, (c (σ * τ) : Matrix ι ι L) =
      (c σ : Matrix ι ι L) * (c τ : Matrix ι ι L).map σ)
    (σ : Γ) (v : ι → L) :
    twist c σ (orbitSum c v) = orbitSum c v := by
  calc
    twist c σ (orbitSum c v) = ∑ τ : Γ, twist c σ (twist c τ v) := by
      simp only [orbitSum, twist]
      have hs : (σ : L → L) ∘ (∑ τ : Γ, (c τ : Matrix ι ι L) *ᵥ (τ ∘ v)) =
          ∑ τ : Γ, (σ : L → L) ∘ ((c τ : Matrix ι ι L) *ᵥ (τ ∘ v)) := by
        ext i
        simp only [Function.comp_apply, Finset.sum_apply, map_sum]
      rw [hs, ← Matrix.mulVecLin_apply, map_sum]
      simp only [Matrix.mulVecLin_apply]
    _ = ∑ τ : Γ, twist c (σ * τ) v :=
      Finset.sum_congr rfl fun τ _ => twist_mul c hc σ τ v
    _ = orbitSum c v := Fintype.sum_bijective (fun τ : Γ => σ * τ)
      (Group.mulLeft_bijective σ) _ _ fun _ => rfl

private theorem span_orbitSum_eq_top (c : Γ → (Matrix ι ι L)ˣ) :
    Submodule.span L (Set.range (orbitSum c)) = ⊤ := by
  let W := Submodule.span L (Set.range (orbitSum c))
  by_contra hW
  obtain ⟨f, hf, hAnn⟩ := W.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hW) inferInstance
  have hZero (v : ι → L) : f (orbitSum c v) = 0 := by
    apply (Submodule.mem_bot L).mp
    rw [← hAnn]
    exact Submodule.mem_map.mpr ⟨_, Submodule.subset_span (Set.mem_range_self v), rfl⟩
  have hInd : LinearIndependent L (fun σ : Γ => (σ : L → L)) :=
    (linearIndependent_monoidHom L L).comp (fun σ : Γ => (σ : L →* L)) fun _ _ h =>
      DFunLike.ext _ _ fun a => DFunLike.congr_fun h a
  have hCoeff (v : ι → L) : ∀ σ : Γ, f (twist c σ v) = 0 := by
    apply (Fintype.linearIndependent_iff.mp hInd) (fun σ => f (twist c σ v))
    funext a
    change (∑ σ : Γ, f (twist c σ v) • (σ : L → L)) a = 0
    rw [← hZero (a • v)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, orbitSum, map_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [twist_smul, map_smul]
    exact mul_comm _ _
  apply hf
  apply LinearMap.ext
  intro v
  change f v = 0
  let w := (((c 1)⁻¹ : (Matrix ι ι L)ˣ) : Matrix ι ι L) *ᵥ v
  have hw : twist c 1 w = v := by
    rw [twist, show ((1 : Γ) : L → L) ∘ w = w from rfl, Matrix.mulVec_mulVec,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [← hw]
  exact hCoeff w 1

/-- A multiplicative matrix cocycle over a finite field extension is a
coboundary for the entrywise action of the automorphism group. -/
theorem matrixHilbert90 (c : Γ → (Matrix ι ι L)ˣ)
    (hc : ∀ σ τ : Γ, (c (σ * τ) : Matrix ι ι L) =
      (c σ : Matrix ι ι L) * (c τ : Matrix ι ι L).map σ) :
    ∃ b : (Matrix ι ι L)ˣ, ∀ σ : Γ, (c σ : Matrix ι ι L) * (b : Matrix ι ι L).map σ = b := by
  let standard := Pi.basisFun L ι
  let basis := Basis.ofSpan (span_orbitSum_eq_top c).ge
  let e := basis.indexEquiv standard
  let frame := basis.reindex e
  letI := standard.invertibleToMatrix frame
  refine ⟨unitOfInvertible (standard.toMatrix frame), fun σ => ?_⟩
  have hf (j : ι) : twist c σ (frame j) = frame j := by
    have hMem : frame j ∈ Set.range (orbitSum c) := by
      rw [show frame j = basis (e.symm j) from Basis.reindex_apply _ _ _]
      exact Basis.ofSpan_subset _ (Set.mem_range_self _)
    obtain ⟨v, hv⟩ := hMem
    rw [← hv, twist_orbitSum c hc]
  ext i j
  have h := congrFun (hf j) i
  simpa [standard, Matrix.mul_apply, Basis.toMatrix_apply, Pi.basisFun_repr,
    twist, Matrix.mulVec, dotProduct, Matrix.map_apply, Function.comp_apply] using h

/-- A determinant-one matrix cocycle admits a determinant-one trivialization. -/
theorem specialLinearHilbert90 (c : Γ → (Matrix ι ι L)ˣ)
    (hc : ∀ σ τ : Γ, (c (σ * τ) : Matrix ι ι L) =
      (c σ : Matrix ι ι L) * (c τ : Matrix ι ι L).map σ)
    (hdet : ∀ σ : Γ, (c σ : Matrix ι ι L).det = 1) :
    ∃ b : (Matrix ι ι L)ˣ, (b : Matrix ι ι L).det = 1 ∧
      ∀ σ : Γ, (c σ : Matrix ι ι L) * (b : Matrix ι ι L).map σ = b := by
  obtain ⟨b, hb⟩ := matrixHilbert90 c hc
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      letI := hempty
      exact ⟨b, Matrix.det_isEmpty, hb⟩
  | inr hnonempty =>
      obtain ⟨j⟩ := hnonempty
      let d := (b : Matrix ι ι L).det
      have hd : d ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
      have hFixed (σ : Γ) : σ d = d := by
        have h := congrArg Matrix.det (hb σ)
        rw [Matrix.det_mul, hdet σ, one_mul] at h
        exact (RingHom.map_det σ.toRingHom (b : Matrix ι ι L)).trans h
      let D : Matrix ι ι L := Matrix.diagonal fun i => if i = j then d⁻¹ else 1
      have hDdet : D.det = d⁻¹ := by
        simp only [D, Matrix.det_diagonal, Finset.prod_ite_eq', Finset.mem_univ, if_true]
      have hD : IsUnit D := (Matrix.isUnit_iff_isUnit_det _).mpr <| by
        rw [hDdet]
        exact isUnit_iff_ne_zero.mpr (inv_ne_zero hd)
      have hFixD (σ : Γ) : D.map σ = D := by
        ext i k
        by_cases hik : i = k
        · subst k
          by_cases hij : i = j
          · simp [D, hij, hFixed σ]
          · simp [D, hij]
        · simp [D, Matrix.diagonal_apply_ne _ hik]
      refine ⟨b * hD.unit, ?_, fun σ => ?_⟩
      · rw [Units.val_mul, hD.unit_spec, Matrix.det_mul, hDdet]
        exact mul_inv_cancel₀ hd
      · rw [Units.val_mul, hD.unit_spec]
        have hComp : ((b : Matrix ι ι L) * D).map σ =
            (b : Matrix ι ι L).map σ * D.map σ :=
          Matrix.map_mul (f := σ.toRingHom)
        rw [hComp, hFixD, ← mul_assoc, hb σ]

/-- Compatible coordinates identifying the group points with invertible matrices
transport matrix Hilbert 90 to the cocycle of the affine torsor. -/
theorem isHopfPointCoboundary_of_matrix_equiv
    {k H : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H] [Algebra k F] [Algebra k L]
    [IsScalarTower k F L] (e : (H →ₐ[k] L) ≃ (Matrix ι ι L)ˣ)
    (hMul : ∀ g h, (e (hopfPointMul g h) : Matrix ι ι L) =
      (e g : Matrix ι ι L) * (e h : Matrix ι ι L))
    (hGalois : ∀ (σ : Γ) g, (e ((σ.toAlgHom.restrictScalars k).comp g) : Matrix ι ι L) =
      (e g : Matrix ι ι L).map σ)
    (c : Γ → H →ₐ[k] L) (hc : IsHopfPointCocycle c) : IsHopfPointCoboundary c := by
  obtain ⟨b, hb⟩ := matrixHilbert90 (e ∘ c) (by
    intro σ τ
    change (e (c (σ * τ)) : Matrix ι ι L) =
      (e (c σ) : Matrix ι ι L) * (e (c τ) : Matrix ι ι L).map σ
    rw [hc.2 σ τ, hMul, hGalois])
  refine ⟨e.symm b, fun σ => e.injective (Units.ext ?_)⟩
  rw [hMul, hGalois, e.apply_symm_apply]
  exact hb σ

end WideE
