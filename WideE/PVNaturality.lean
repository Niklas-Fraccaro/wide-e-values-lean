import WideE.SectionComparison

/-! Naturality of normalized fundamental matrices for horizontal maps. -/

noncomputable section

namespace WideE

open StrictEUnit

variable {K : Type*} [Field K] [CharZero K] {m n : ℕ}
variable {A : Matrix (Fin m) (Fin m) (LaurentPolynomial K)}
variable {B : Matrix (Fin n) (Fin n) (LaurentPolynomial K)}

/-- A horizontal map intertwines the normalized formal solutions with its matrix at one. -/
theorem formalFundamentalAtOneUnit_naturality
    (F : Matrix (Fin n) (Fin m) (LaurentPolynomial K))
    (hF : F.map laurentDerivation = B * F - F * A) :
    F.map (formalAtOne K) * (formalFundamentalAtOneUnit A).val =
      (formalFundamentalAtOneUnit B).val * (F.map (evalAtOne K)).map (PowerSeries.C K) := by
  let e := (formalAtOne K).toRingHom
  let D := PowerSeries.derivative K
  let U := formalFundamentalAtOneUnit A
  let V := formalFundamentalAtOneUnit B
  have hU : U.val.map D = A.map e * U.val := by
    change U.val.map D = A.map (formalAtOne K) * U.val
    simp only [U, D, formalFundamentalAtOneUnit_val, formalFundamentalMatrix_derivative]
  have hV : V.val.map D = B.map e * V.val := by
    change V.val.map D = B.map (formalAtOne K) * V.val
    simp only [V, D, formalFundamentalAtOneUnit_val, formalFundamentalMatrix_derivative]
  have hForm : (F.map e).map D = B.map e * F.map e - F.map e * A.map e := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin m) (LaurentPolynomial K) => M.map e) hF
    change (F.map laurentDerivation).map e = (B * F - F * A).map e at h
    rw [Matrix.map_sub e e.map_sub, Matrix.map_mul, Matrix.map_mul] at h
    refine Eq.trans ?_ h
    apply Matrix.ext
    intro i j
    exact formalAtOne_derivative K (F i j)
  have hU₀ : U.val.map (PowerSeries.constantCoeff K) = 1 := by
    simp only [U, formalFundamentalAtOneUnit_val, formalFundamentalMatrix_constantCoeff]
  have hV₀ : V.val.map (PowerSeries.constantCoeff K) = 1 := by
    simp only [V, formalFundamentalAtOneUnit_val, formalFundamentalMatrix_constantCoeff]
  have h := horizontal_recover_of_specialized_gauge D (PowerSeries.constantCoeff K)
    (fun p hp => (powerSeries_eq_C_of_derivative_eq_zero p hp).symm) U.val V (F.map e)
    (horizontal_gauge_deriv_eq_zero D U V hU hV hForm) hU₀ hV₀
  have hEval : (F.map e).map (PowerSeries.constantCoeff K) = F.map (evalAtOne K) := by
    ext i j
    exact formalAtOne_constantCoeff K (F i j)
  rwa [hEval] at h

/-- Naturality descends to any common coefficient algebra containing the two formal solutions. -/
theorem liftedFundamentalMatrix_naturality {S : Type*} [CommRing S] [Algebra K S]
    (base : LaurentPolynomial K →ₐ[K] S) (emb : S →ₐ[K] PowerSeries K)
    (hEmb : Function.Injective emb) (hBase : emb.comp base = formalAtOne K)
    (U : (Matrix (Fin m) (Fin m) S)ˣ) (V : (Matrix (Fin n) (Fin n) S)ˣ)
    (hU : U.val.map emb = (formalFundamentalAtOneUnit A).val)
    (hV : V.val.map emb = (formalFundamentalAtOneUnit B).val)
    (F : Matrix (Fin n) (Fin m) (LaurentPolynomial K))
    (hF : F.map laurentDerivation = B * F - F * A) :
    F.map base * U.val = V.val * (F.map (evalAtOne K)).map (algebraMap K S) := by
  apply Matrix.map_injective (f := (emb : S → PowerSeries K)) hEmb
  change (F.map base * U.val).map emb.toRingHom =
    (V.val * (F.map (evalAtOne K)).map (algebraMap K S)).map emb.toRingHom
  have hLeft : (F.map base).map emb = F.map (formalAtOne K) := by
    apply Matrix.ext
    intro i j
    exact DFunLike.congr_fun hBase (F i j)
  have hRight : ((F.map (evalAtOne K)).map (algebraMap K S)).map emb =
      (F.map (evalAtOne K)).map (PowerSeries.C K) := by
    apply Matrix.ext
    intro i j
    exact emb.commutes (evalAtOne K (F i j))
  rw [Matrix.map_mul, Matrix.map_mul]
  change (F.map base).map emb * U.val.map emb =
    V.val.map emb * ((F.map (evalAtOne K)).map (algebraMap K S)).map emb
  rw [hLeft, hRight, hU, hV]
  exact formalFundamentalAtOneUnit_naturality F hF

section Normalization

variable {k S : Type*} [CommRing k] [CommRing S]
variable (E : S →+* k) (C : k →+* S)

/-- Precompose a comparison matrix by the inverse of its value at the chosen point. -/
def normalizeMatrixAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : (Matrix ι ι S)ˣ) : (Matrix ι ι S)ˣ :=
  U * (Units.map (C.comp E).mapMatrix.toMonoidHom U)⁻¹

@[simp] theorem normalizeMatrixAt_specialize {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hEC : Function.LeftInverse E C) (U : (Matrix ι ι S)ˣ) :
    (normalizeMatrixAt E C U).val.map E = 1 := by
  let e : Matrix ι ι S →* Matrix ι ι k := E.mapMatrix.toMonoidHom
  have h : Units.map e (Units.map (C.comp E).mapMatrix.toMonoidHom U) = Units.map e U := by
    apply Units.ext
    exact Matrix.ext (fun i j => hEC (E (U.val i j)))
  change (Units.map e (normalizeMatrixAt E C U)).val = 1
  simp only [normalizeMatrixAt, map_mul, map_inv, h, mul_inv_cancel, Units.val_one]

/-- Normalizing both comparison matrices preserves their naturality relation. -/
theorem normalizeMatrixAt_naturality {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (hEC : Function.LeftInverse E C) (U : (Matrix ι ι S)ˣ) (V : (Matrix κ κ S)ˣ)
    (F : Matrix κ ι S) (h : F * U.val = V.val * (F.map E).map C) :
    F * (normalizeMatrixAt E C U).val =
      (normalizeMatrixAt E C V).val * (F.map E).map C := by
  let p := C.comp E
  let U₀ := Units.map p.mapMatrix.toMonoidHom U
  let V₀ := Units.map p.mapMatrix.toMonoidHom V
  change F * U.val = V.val * F.map p at h
  have hp (a : S) : p (p a) = p a := congrArg C (hEC (E a))
  have hFixed : (F.map p).map p = F.map p := Matrix.ext (fun i j => hp (F i j))
  have hMap := congrArg (fun G : Matrix κ ι S => G.map p) h
  change (F * U.val).map p = (V.val * F.map p).map p at hMap
  rw [Matrix.map_mul, Matrix.map_mul, hFixed] at hMap
  change F.map p * U₀.val = V₀.val * F.map p at hMap
  have hInv : F.map p * (U₀⁻¹).val = (V₀⁻¹).val * F.map p := by
    calc
      _ = ((V₀⁻¹).val * V₀.val) * (F.map p * (U₀⁻¹).val) := by
        rw [Units.inv_mul, Matrix.one_mul]
      _ = ((V₀⁻¹).val * (V₀.val * F.map p)) * (U₀⁻¹).val := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [← hMap]
        simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  change F * (U.val * (U₀⁻¹).val) = (V.val * (V₀⁻¹).val) * F.map p
  rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, hInv, Matrix.mul_assoc]

end Normalization

end WideE
