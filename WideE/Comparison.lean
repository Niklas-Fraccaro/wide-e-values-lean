import WideE.Laurent
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Normalization of finite comparison matrices

The two matrices act on different modules. The equations express preservation
of the coordinate product and the distinguished target vector for one.
-/

noncomputable section

open scoped Matrix BigOperators

namespace WideE

section Coordinates

variable {R ι κ : Type*} [CommRing R] [Fintype ι]

/-- The product from its coefficients in the two chosen bases. -/
def coordinateProduct (c : ι → ι → κ → R) :
    (ι → R) →ₗ[R] (ι → R) →ₗ[R] (κ → R) :=
  ∑ i, ∑ j, (LinearMap.proj i).smulRight ((LinearMap.proj j).smulRight (c i j))

theorem coordinateProduct_apply (c : ι → ι → κ → R) (x y : ι → R) (l : κ) :
    coordinateProduct c x y l = ∑ i, ∑ j, x i * (y j * c i j l) := by
  simp only [coordinateProduct, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply, LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul]

@[simp] theorem coordinateProduct_single_one [DecidableEq ι] (c : ι → ι → κ → R) (i j : ι) :
    coordinateProduct c (Pi.single i 1) (Pi.single j 1) = c i j := by
  funext l
  simp [coordinateProduct_apply, Pi.single_apply, ite_mul]

theorem map_coordinateProduct {S : Type*} [CommRing S] (φ : R →+* S)
    (c : ι → ι → κ → R) (x y : ι → R) (l : κ) :
    φ (coordinateProduct c x y l) =
      coordinateProduct (fun i j => φ ∘ c i j) (φ ∘ x) (φ ∘ y) l := by
  simp only [coordinateProduct_apply, map_sum, map_mul, Function.comp_apply]

end Coordinates

variable {R ι κ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A comparison of the product and one written in finite coordinates. -/
structure CoordinateComparison (c c' : ι → ι → κ → R) (d d' : κ → R) where
  onM : (Matrix ι ι R)ˣ
  onN : (Matrix κ κ R)ˣ
  preservesProduct (x y : ι → R) :
    coordinateProduct c' ((onM : Matrix ι ι R) *ᵥ x) ((onM : Matrix ι ι R) *ᵥ y) =
      (onN : Matrix κ κ R) *ᵥ coordinateProduct c x y
  preservesOne : (onN : Matrix κ κ R) *ᵥ d = d'

namespace CoordinateComparison

variable {c c' c'' : ι → ι → κ → R} {d d' d'' : κ → R}

/-- Equations (11.2)–(11.3) on basis vectors give a comparison on all vectors. -/
def ofBasis (A : (Matrix ι ι R)ˣ) (B : (Matrix κ κ R)ˣ)
    (hProduct : ∀ i j : ι,
      coordinateProduct c' (fun a => (A : Matrix ι ι R) a i) (fun b => (A : Matrix ι ι R) b j) =
        (B : Matrix κ κ R) *ᵥ c i j)
    (hOne : (B : Matrix κ κ R) *ᵥ d = d') :
    CoordinateComparison c c' d d' where
  onM := A
  onN := B
  preservesProduct x y := by
    let a := (A : Matrix ι ι R).mulVecLin
    let b := (B : Matrix κ κ R).mulVecLin
    have h : (coordinateProduct c').compl₁₂ a a = (coordinateProduct c).compr₂ b := by
      apply (Pi.basisFun R ι).ext
      intro i
      apply (Pi.basisFun R ι).ext
      intro j
      simpa only [a, b, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply, Matrix.mulVecLin_apply,
        Pi.basisFun_apply, Matrix.mulVec_single_one, Matrix.transpose_apply,
        coordinateProduct_single_one] using hProduct i j
    exact LinearMap.congr_fun (LinearMap.congr_fun h x) y
  preservesOne := hOne

theorem preservesProduct_basis (A : CoordinateComparison c c' d d') (i j : ι) :
    coordinateProduct c' (fun a => (A.onM : Matrix ι ι R) a i) (fun b => (A.onM : Matrix ι ι R) b j) =
      (A.onN : Matrix κ κ R) *ᵥ c i j := by
  simpa only [Matrix.mulVec_single_one, Matrix.transpose_apply, coordinateProduct_single_one]
    using A.preservesProduct (Pi.single i 1) (Pi.single j 1)

/-- Apply a coefficient homomorphism to the comparison equations on the basis. -/
def map {S : Type*} [CommRing S] (A : CoordinateComparison c c' d d') (φ : R →+* S) :
    CoordinateComparison (fun i j l => φ (c i j l)) (fun i j l => φ (c' i j l))
      (fun l => φ (d l)) (fun l => φ (d' l)) :=
  ofBasis (Units.map φ.mapMatrix.toMonoidHom A.onM) (Units.map φ.mapMatrix.toMonoidHom A.onN)
    (by
      intro i j
      funext l
      have h := congrArg (fun v : κ → R => φ (v l)) (A.preservesProduct_basis i j)
      simpa only [map_coordinateProduct, RingHom.map_mulVec] using h)
    (by
      funext l
      have h := congrArg (fun v : κ → R => φ (v l)) A.preservesOne
      simpa only [RingHom.map_mulVec] using h)

/-- Compose two comparisons, multiplying the coordinate matrices. -/
def trans (A : CoordinateComparison c c' d d') (B : CoordinateComparison c' c'' d' d'') :
    CoordinateComparison c c'' d d'' where
  onM := B.onM * A.onM
  onN := B.onN * A.onN
  preservesProduct x y := by
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec, B.preservesProduct, A.preservesProduct]
  preservesOne := by
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec, A.preservesOne, B.preservesOne]

/-- Inverting the matrices inverts the comparison. -/
def symm (A : CoordinateComparison c c' d d') : CoordinateComparison c' c d' d where
  onM := A.onM⁻¹
  onN := A.onN⁻¹
  preservesProduct x y := by
    have h := A.preservesProduct ((↑A.onM⁻¹ : Matrix ι ι R) *ᵥ x) ((↑A.onM⁻¹ : Matrix ι ι R) *ᵥ y)
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h
    rw [h, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  preservesOne := by
    calc
      (↑A.onN⁻¹ : Matrix κ κ R) *ᵥ d' =
          (↑A.onN⁻¹ : Matrix κ κ R) *ᵥ ((A.onN : Matrix κ κ R) *ᵥ d) :=
        congrArg (fun v => (↑A.onN⁻¹ : Matrix κ κ R) *ᵥ v) A.preservesOne.symm
      _ = d := by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

/-- Transport of a product equal to the distinguished unit vector, as in (8.2). -/
theorem transportInverse (A : CoordinateComparison c c' d d') {x y : ι → R}
    (h : coordinateProduct c x y = d) :
    coordinateProduct c' ((A.onM : Matrix ι ι R) *ᵥ x) ((A.onM : Matrix ι ι R) *ᵥ y) = d' := by
  rw [A.preservesProduct, h, A.preservesOne]

section Specialization

variable {K : Type*} [CommRing K]
variable (E : R →+* K) (C : K →+* R)
variable (A : CoordinateComparison
  (fun i j l => C (E (c i j l))) c (fun l => C (E (d l))) d)

private def specialize (hEC : Function.LeftInverse E C) : CoordinateComparison
    (fun i j l => C (E (c i j l))) (fun i j l => C (E (c i j l)))
    (fun l => C (E (d l))) (fun l => C (E (d l))) where
  onM := (A.map (C.comp E)).onM
  onN := (A.map (C.comp E)).onN
  preservesProduct x y := by
    have h (a : K) : E (C a) = a := hEC a
    simpa only [RingHom.comp_apply, h] using
      (A.map (C.comp E)).preservesProduct x y
  preservesOne := by
    have h (a : K) : E (C a) = a := hEC a
    simpa only [RingHom.comp_apply, h] using
      (A.map (C.comp E)).preservesOne

/-- Precompose by the inverse of the scalar extension of the specialization, as in (7.5). -/
def normalize (hEC : Function.LeftInverse E C) : CoordinateComparison
    (fun i j l => C (E (c i j l))) c (fun l => C (E (d l))) d :=
  (specialize E C A hEC).symm.trans A

private theorem normalize_unit_specialize {n : Type*} [Fintype n] [DecidableEq n]
    (hEC : Function.LeftInverse E C) (U : (Matrix n n R)ˣ) :
    E.mapMatrix (↑(U * (Units.map (C.comp E).mapMatrix.toMonoidHom U)⁻¹) : Matrix n n R) = 1 := by
  let e := (E.mapMatrix : Matrix n n R →+* Matrix n n K).toMonoidHom
  have h : Units.map e (Units.map (C.comp E).mapMatrix.toMonoidHom U) = Units.map e U := by
    apply Units.ext
    ext i j
    exact hEC (E ((U : Matrix n n R) i j))
  have h' : Units.map e (U * (Units.map (C.comp E).mapMatrix.toMonoidHom U)⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  exact congrArg Units.val h'

/-- The normalized comparison specializes to the identity on the input coordinates. -/
theorem normalize_onM_specialize (hEC : Function.LeftInverse E C) :
    E.mapMatrix (↑(A.normalize E C hEC).onM : Matrix ι ι R) = 1 :=
  normalize_unit_specialize E C hEC A.onM

/-- The normalized comparison specializes to the identity on the product coordinates. -/
theorem normalize_onN_specialize (hEC : Function.LeftInverse E C) :
    E.mapMatrix (↑(A.normalize E C hEC).onN : Matrix κ κ R) = 1 :=
  normalize_unit_specialize E C hEC A.onN

end Specialization
end CoordinateComparison

section LaurentCoordinates

open LaurentPolynomial

variable (K : Type*) [CommRing K] {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Coordinates of a comparison from the fiber at one to a Kummer pullback. -/
abbrev LaurentCoordinateComparison (q : ℕ)
    (c : ι → ι → κ → LaurentPolynomial K) (d : κ → LaurentPolynomial K) :=
  CoordinateComparison
    (fun i j l => C (evalAtOne K (kummer K q (c i j l))))
    (fun i j l => kummer K q (c i j l))
    (fun l => C (evalAtOne K (kummer K q (d l))))
    (fun l => kummer K q (d l))

/-- Lift an inverse relation with both vectors specializing to the given fiber vectors. -/
theorem exists_lifted_inverse_of_laurent_comparison
    {q : ℕ} {c : ι → ι → κ → LaurentPolynomial K} {d : κ → LaurentPolynomial K}
    (A : LaurentCoordinateComparison K q c d) {x y : ι → K}
    (h : coordinateProduct (fun i j l => evalAtOne K (c i j l)) x y = fun l => evalAtOne K (d l)) :
    ∃ X Y : ι → LaurentPolynomial K,
      (∀ i, evalAtOne K (X i) = x i) ∧ (∀ i, evalAtOne K (Y i) = y i) ∧
      coordinateProduct (fun i j l => kummer K q (c i j l)) X Y = fun l => kummer K q (d l) := by
  let normalized := A.normalize (evalAtOne K) C (evalAtOne_C K)
  have hM := A.normalize_onM_specialize (evalAtOne K) C (evalAtOne_C K)
  have hSpecializes (v : ι → K) (i : ι) :
      evalAtOne K (((normalized.onM : Matrix ι ι (LaurentPolynomial K)) *ᵥ (C ∘ v)) i) = v i := by
    rw [RingHom.map_mulVec]
    change ((evalAtOne K).mapMatrix ↑normalized.onM *ᵥ ((evalAtOne K) ∘ C ∘ v)) i = v i
    rw [hM, Matrix.one_mulVec]
    exact evalAtOne_C K (v i)
  refine ⟨(normalized.onM : Matrix ι ι (LaurentPolynomial K)) *ᵥ (C ∘ x),
    (normalized.onM : Matrix ι ι (LaurentPolynomial K)) *ᵥ (C ∘ y), hSpecializes x, hSpecializes y,
    normalized.transportInverse ?_⟩
  funext l
  have h' := congrArg C (congrFun h l)
  simpa only [map_coordinateProduct, Function.comp_apply, evalAtOne_kummer] using h'

end LaurentCoordinates
end WideE
