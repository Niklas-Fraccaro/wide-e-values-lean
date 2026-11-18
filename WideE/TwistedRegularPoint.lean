import WideE.MatrixHilbert90
import WideE.HopfPointGroup
import WideE.ProjectiveOrbitTwist
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Nonvanishing on a twisted vector space

A semilinear Galois cocycle has a fixed basis by matrix Hilbert 90.
The rational linear combinations of that basis meet every polynomial
principal open that is nonempty over the extension field.
-/

noncomputable section

open scoped Matrix

namespace WideE

section Subfield

variable {F L ι : Type*} [Field F] [Field L] [Algebra F L]

private theorem eval_linearMap_coefficients (f : L →ₗ[F] F) (x : ι → F)
    (p : MvPolynomial ι L) :
    MvPolynomial.eval x (Finsupp.mapRange f f.map_zero p : MvPolynomial ι F) =
      f (MvPolynomial.eval (fun i => algebraMap F L (x i)) p) := by
  classical
  induction p using Finsupp.induction_linear with
  | zero => simp only [Finsupp.mapRange_zero, map_zero]
  | add a b ha hb =>
    rw [Finsupp.mapRange_add (map_add f) a b]
    simp only [map_add, ha, hb]
  | single d a =>
    rw [Finsupp.mapRange_single]
    change MvPolynomial.eval x (MvPolynomial.monomial d (f a)) =
      f (MvPolynomial.eval (fun i => algebraMap F L (x i)) (MvPolynomial.monomial d a))
    rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
    have hProd : d.prod (fun i n => (algebraMap F L (x i)) ^ n) =
        algebraMap F L (d.prod fun i n => (x i) ^ n) := by
      simp only [Finsupp.prod, map_prod, map_pow]
    rw [hProd, mul_comm a _, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

/-- A nonzero polynomial over a field extension cannot vanish on all tuples
from an infinite subfield. -/
theorem exists_eval_over_subfield_ne_zero [Infinite F] (p : MvPolynomial ι L) (hp : p ≠ 0) :
    ∃ x : ι → F, MvPolynomial.eval (fun i => algebraMap F L (x i)) p ≠ 0 := by
  classical
  obtain ⟨d, hd⟩ := Finsupp.support_nonempty_iff.mpr hp
  have hCoeff : p.coeff d ≠ 0 := Finsupp.mem_support_iff.mp hd
  let b := Module.Free.chooseBasis F L
  have hRepr : b.repr (p.coeff d) ≠ 0 :=
    fun h => hCoeff (b.repr.injective (h.trans (map_zero _).symm))
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hRepr
  let f := b.coord i
  have hf : f (p.coeff d) ≠ 0 := Finsupp.mem_support_iff.mp hi
  let q : MvPolynomial ι F := Finsupp.mapRange f f.map_zero p
  have hq : q ≠ 0 := by
    intro h
    have hAt := congrArg (MvPolynomial.coeff d) h
    exact hf hAt
  by_contra h
  push_neg at h
  apply hq
  apply MvPolynomial.funext
  intro x
  change MvPolynomial.eval x (Finsupp.mapRange f f.map_zero p : MvPolynomial ι F) = _
  rw [eval_linearMap_coefficients, h x, map_zero, map_zero]

end Subfield

section Twisted

variable {F L ι : Type*} [Field F] [Field L] [Algebra F L]
variable [Fintype ι] [DecidableEq ι]

private theorem matrixPolynomialSubstitution_one :
    matrixPolynomialSubstitution (1 : Matrix ι ι L) = AlgHom.id _ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  have hMap : (1 : Matrix ι ι L).map (MvPolynomial.C : L →+* MvPolynomial ι L) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  rw [matrixPolynomialSubstitution_X, hMap, Matrix.one_mulVec]
  rfl

/-- A matrix cocycle has a twisted Galois fixed vector outside the zero locus
of any prescribed nonzero polynomial. -/
theorem exists_twistedGalois_fixedPoint_eval_ne_zero [Infinite F] [FiniteDimensional F L]
    (c : (L ≃ₐ[F] L) → (Matrix ι ι L)ˣ)
    (hc : ∀ σ τ, (c (σ * τ)).val = (c σ).val * (c τ).val.map σ)
    (p : MvPolynomial ι L) (hp : p ≠ 0) :
    ∃ x : ι → L, MvPolynomial.eval x p ≠ 0 ∧
      ∀ σ, (c σ).val *ᵥ (σ ∘ x) = x := by
  obtain ⟨b, hb⟩ := matrixHilbert90 c hc
  let q := matrixPolynomialSubstitution b.val p
  have hq : q ≠ 0 := by
    intro h
    have hSub := matrixPolynomialSubstitution_mul b.val b.inv
    rw [b.val_inv, matrixPolynomialSubstitution_one] at hSub
    have hAt := DFunLike.congr_fun hSub p
    change p = matrixPolynomialSubstitution b.inv q at hAt
    rw [h, map_zero] at hAt
    exact hp hAt
  obtain ⟨v, hv⟩ := exists_eval_over_subfield_ne_zero (F := F) q hq
  let w : ι → L := fun i => algebraMap F L (v i)
  refine ⟨b.val *ᵥ w, ?_, fun σ => ?_⟩
  · have hEval := eval₂_matrixPolynomialSubstitution (RingHom.id L) b.val w p
    change MvPolynomial.eval w q = MvPolynomial.eval (b.val.map (RingHom.id L) *ᵥ w) p at hEval
    have hMap : b.val.map (RingHom.id L) = b.val := Matrix.ext fun _ _ => rfl
    rw [hMap] at hEval
    exact fun h => hv (hEval.trans h)
  · have hW : (σ : L → L) ∘ w = w := funext fun i => σ.commutes (v i)
    have hMap : (σ : L → L) ∘ (b.val *ᵥ w) = b.val.map σ *ᵥ w := by
      have h := funext (RingHom.map_mulVec σ.toRingHom b.val w)
      rw [show (σ.toRingHom : L → L) ∘ w = w from hW] at h
      exact h
    rw [hMap, Matrix.mulVec_mulVec, hb σ]

end Twisted

section HopfPointChoice

variable {F L H ι : Type*} [Field F] [Field L] [Algebra F L]
variable [CommRing H] [HopfAlgebra F H] [Fintype ι] [DecidableEq ι]

open scoped TensorProduct

/-- Galois conjugation of a point conjugates the entries of its representation matrix. -/
theorem hopfPointMatrix_galois (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := F) (U.val i j) = ∑ l, U.val i l ⊗ₜ[F] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := F) (U.val i j) = if i = j then 1 else 0)
    (σ : L ≃ₐ[F] L) (a : H →ₐ[F] L) :
    (hopfPointMatrix U hD he ((σ.toAlgHom.restrictScalars F).comp a)).val =
      (hopfPointMatrix U hD he a).val.map σ := rfl

/-- In an affine matrix representation, any prescribed nonempty polynomial
principal open contains a vector fixed by the twisted action of a Hopf point cocycle. -/
theorem exists_twistedHopfPoint_fixedPoint_eval_ne_zero [Infinite F] [FiniteDimensional F L]
    (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := F) (U.val i j) = ∑ l, U.val i l ⊗ₜ[F] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := F) (U.val i j) = if i = j then 1 else 0)
    (c : (L ≃ₐ[F] L) → H →ₐ[F] L) (hc : IsHopfPointCocycle c)
    (p : MvPolynomial ι L) (hp : p ≠ 0) :
    ∃ x : ι → L, MvPolynomial.eval x p ≠ 0 ∧
      ∀ σ, (U.val.map (c σ)) *ᵥ (σ ∘ x) = x := by
  letI : Group (H →ₐ[F] L) := hopfPointGroup
  let M : (H →ₐ[F] L) →* (Matrix ι ι L)ˣ := hopfPointMatrix U hD he
  have h : ∀ σ τ, (M (c (σ * τ))).val = (M (c σ)).val * (M (c τ)).val.map σ := by
    intro σ τ
    rw [hc.2]
    change (M (c σ * (σ.toAlgHom.restrictScalars F).comp (c τ))).val =
      (M (c σ)).val * (M (c τ)).val.map σ
    rw [map_mul M, Units.val_mul, hopfPointMatrix_galois U hD he]
  exact exists_twistedGalois_fixedPoint_eval_ne_zero (M ∘ c) h p hp

end HopfPointChoice

end WideE
