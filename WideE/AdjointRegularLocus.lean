import WideE.AdjointToricDescent
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Infinitesimal adjoint action and its regular locus

Differentiating the adjoint coefficients with respect to the actual
cotangent space gives the tangent matrix of each adjoint orbit.
Its universal characteristic polynomial detects the locus where the
multiplicity of zero is minimal.
-/

open scoped TensorProduct Matrix

noncomputable section

namespace WideE

section TangentPoints

variable {F H A : Type*} [Field F] [CommRing H] [HopfAlgebra F H]
  [CommRing A] [Algebra F A]

local notation "ε" => Bialgebra.counitAlgHom F H

/-- The genuine dual-number point of the Hopf group associated with a tangent vector. -/
def hopfLieInfinitesimalPoint (y : HopfLieVector F H A) : H →ₐ[F] DualNumber A where
  toFun a := ⟨algebraMap F A (ε a), y (hopfCotangentProjection F H a)⟩
  map_one' := by
    apply TrivSqZeroExt.ext
    · change algebraMap F A (ε 1) = 1
      rw [map_one, map_one]
    · change y (hopfCotangentProjection F H 1) = 0
      rw [hopfCotangentProjection_one, map_zero]
  map_zero' := by
    apply TrivSqZeroExt.ext
    · change algebraMap F A (ε 0) = 0
      rw [map_zero, map_zero]
    · change y (hopfCotangentProjection F H 0) = 0
      rw [map_zero, map_zero]
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · change algebraMap F A (ε (a * b)) = algebraMap F A (ε a) * algebraMap F A (ε b)
      rw [map_mul, map_mul]
    · rw [DualNumber.snd_mul]
      change y (hopfCotangentProjection F H (a * b)) =
        algebraMap F A (ε a) * y (hopfCotangentProjection F H b) +
          y (hopfCotangentProjection F H a) * algebraMap F A (ε b)
      rw [hopfCotangentProjection_mul, map_add, map_smul, map_smul,
        Algebra.smul_def, Algebra.smul_def, mul_comm (algebraMap F A (ε b))]
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · change algebraMap F A (ε (a + b)) = algebraMap F A (ε a) + algebraMap F A (ε b)
      rw [map_add, map_add]
    · change y (hopfCotangentProjection F H (a + b)) =
        y (hopfCotangentProjection F H a) + y (hopfCotangentProjection F H b)
      rw [map_add, map_add]
  commutes' c := by
    apply TrivSqZeroExt.ext
    · change algebraMap F A (ε (algebraMap F H c)) = algebraMap F A c
      rw [(ε).commutes]
      rfl
    · change y (hopfCotangentProjection F H (algebraMap F H c)) = 0
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hopfCotangentProjection_one, smul_zero, map_zero]

@[simp]
theorem hopfLieInfinitesimalPoint_fst (y : HopfLieVector F H A) (a : H) :
    (hopfLieInfinitesimalPoint y a).fst = algebraMap F A (ε a) := rfl

@[simp]
theorem hopfLieInfinitesimalPoint_snd (y : HopfLieVector F H A) (a : H) :
    (hopfLieInfinitesimalPoint y a).snd = y (hopfCotangentProjection F H a) := rfl

/-- Lift a Lie vector as constant coefficients in the dual-number algebra. -/
def hopfLieVector_toDual (x : HopfLieVector F H A) : HopfLieVector F H (DualNumber A) :=
  (IsScalarTower.toAlgHom F A (DualNumber A)).toLinearMap.comp x

@[simp]
theorem hopfLieVector_toDual_fst (x : HopfLieVector F H A) (a : HopfCotangent F H) :
    (hopfLieVector_toDual x a).fst = x a := rfl

@[simp]
theorem hopfLieVector_toDual_snd (x : HopfLieVector F H A) (a : HopfCotangent F H) :
    (hopfLieVector_toDual x a).snd = 0 := rfl

end TangentPoints

section OrbitDifferential

variable {F H A ι : Type*} [Field F] [CommRing H] [HopfAlgebra F H]
  [CommRing A] [Algebra F A] [Fintype ι] [DecidableEq ι]

local notation "C" => HopfCotangent F H

/-- The derivative of the orbit map at the identity, parameterized by the
coordinates of the Lie vector whose orbit is considered. -/
def hopfAdjointTangentMatrix (b : Basis ι F C) (x : ι → A) : Matrix ι ι A :=
  fun i l => ∑ j, algebraMap F A
    (b.repr (hopfCotangentProjection F H (hopfAdjointMatrix b i j)) l) * x j

omit [DecidableEq ι] in
private theorem lieVector_sum_basis (b : Basis ι F C) (y : HopfLieVector F H A) (c : C) :
    y c = ∑ l, algebraMap F A (b.repr c l) * y (b l) := by
  conv_lhs => rw [← b.sum_repr c]
  simp only [map_sum, map_smul, Algebra.smul_def]

/-- The constant part of the adjoint action by a tangent point is the original vector. -/
theorem hopfAdjoint_infinitesimal_fst (b : Basis ι F C) (x y : HopfLieVector F H A) (i : ι) :
    (hopfAdjoint (hopfLieInfinitesimalPoint y) (hopfLieVector_toDual x) (b i)).fst = x (b i) := by
  have h := congrFun (hopfAdjoint_apply_basis b (hopfLieInfinitesimalPoint y) (hopfLieVector_toDual x)) i
  change hopfAdjoint (hopfLieInfinitesimalPoint y) (hopfLieVector_toDual x) (b i) = _ at h
  rw [h]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, TrivSqZeroExt.fst_sum,
    TrivSqZeroExt.fst_mul, hopfLieInfinitesimalPoint_fst, hopfLieVector_toDual_fst]
  have hε (j : ι) : (Bialgebra.counitAlgHom F H) (hopfAdjointMatrix b i j) =
      if i = j then 1 else 0 := hopfAdjointMatrix_counit b i j
  simp_rw [hε, apply_ite (algebraMap F A), map_one, map_zero, ite_mul, one_mul, zero_mul]
  simp

omit [DecidableEq ι] in
/-- The first-order part of the actual adjoint action is the tangent matrix. -/
theorem hopfAdjoint_infinitesimal_snd (b : Basis ι F C) (x y : HopfLieVector F H A) (i : ι) :
    (hopfAdjoint (hopfLieInfinitesimalPoint y) (hopfLieVector_toDual x) (b i)).snd =
      (hopfAdjointTangentMatrix b (fun j => x (b j)) *ᵥ fun j => y (b j)) i := by
  have h := congrFun (hopfAdjoint_apply_basis b (hopfLieInfinitesimalPoint y) (hopfLieVector_toDual x)) i
  change hopfAdjoint (hopfLieInfinitesimalPoint y) (hopfLieVector_toDual x) (b i) = _ at h
  rw [h]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, TrivSqZeroExt.snd_sum,
    DualNumber.snd_mul, hopfLieVector_toDual_fst, hopfLieVector_toDual_snd,
    mul_zero, zero_add, hopfLieInfinitesimalPoint_snd, hopfAdjointTangentMatrix]
  have hCoeff (j : ι) : y (hopfCotangentProjection F H (hopfAdjointMatrix b i j)) =
      ∑ l, algebraMap F A (b.repr (hopfCotangentProjection F H (hopfAdjointMatrix b i j)) l) *
        y (b l) := lieVector_sum_basis b y _
  simp_rw [hCoeff, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ac_rfl

/-- Stabilization by an actual infinitesimal group point is the kernel
condition of the tangent map. -/
theorem hopfAdjoint_infinitesimal_eq_iff (b : Basis ι F C) (x y : HopfLieVector F H A) :
    hopfAdjoint (hopfLieInfinitesimalPoint y) (hopfLieVector_toDual x) = hopfLieVector_toDual x ↔
      hopfAdjointTangentMatrix b (fun i => x (b i)) *ᵥ (fun i => y (b i)) = 0 := by
  constructor
  · intro h
    funext i
    rw [← hopfAdjoint_infinitesimal_snd b x y i, h, hopfLieVector_toDual_snd]
    rfl
  · intro h
    apply b.ext
    intro i
    apply TrivSqZeroExt.ext
    · rw [hopfAdjoint_infinitesimal_fst b x y i, hopfLieVector_toDual_fst]
    · rw [hopfAdjoint_infinitesimal_snd b x y i, h, hopfLieVector_toDual_snd]
      rfl

end OrbitDifferential

section RegularLocus

variable {F H ι : Type*} [Field F] [CommRing H] [HopfAlgebra F H]
  [Fintype ι] [DecidableEq ι]

local notation "C" => HopfCotangent F H

/-- The tangent matrix with independent variables for the Lie coordinates. -/
def hopfAdjointUniversalTangentMatrix (b : Basis ι F C) :
    Matrix ι ι (MvPolynomial ι F) :=
  hopfAdjointTangentMatrix b MvPolynomial.X

omit [DecidableEq ι] in
theorem hopfAdjointUniversalTangentMatrix_aeval {A : Type*} [CommRing A] [Algebra F A]
    (b : Basis ι F C) (x : ι → A) :
    (hopfAdjointUniversalTangentMatrix b).map (MvPolynomial.aeval x).toRingHom =
      hopfAdjointTangentMatrix b x := by
  apply Matrix.ext
  intro i j
  change MvPolynomial.aeval x (∑ l, MvPolynomial.C
    (b.repr (hopfCotangentProjection F H (hopfAdjointMatrix b i l)) j) * MvPolynomial.X l) = _
  simp only [hopfAdjointTangentMatrix, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]

/-- The smallest multiplicity of the zero root in the universal
adjoint tangent characteristic polynomial. -/
def hopfAdjointGenericZeroMultiplicity (b : Basis ι F C) : ℕ :=
  (hopfAdjointUniversalTangentMatrix b).charpoly.natTrailingDegree

/-- The coefficient cutting out the failure to have generic zero-root multiplicity. -/
def hopfAdjointRegularPolynomial (b : Basis ι F C) : MvPolynomial ι F :=
  (hopfAdjointUniversalTangentMatrix b).charpoly.coeff (hopfAdjointGenericZeroMultiplicity b)

theorem hopfAdjointRegularPolynomial_ne_zero (b : Basis ι F C) :
    hopfAdjointRegularPolynomial b ≠ 0 :=
  Polynomial.coeff_natTrailingDegree_ne_zero.mpr (Matrix.charpoly_monic _).ne_zero

theorem hopfAdjointTangentMatrix_charpoly_coeff {A : Type*} [CommRing A] [Algebra F A]
    (b : Basis ι F C) (x : ι → A) (n : ℕ) :
    (hopfAdjointTangentMatrix b x).charpoly.coeff n =
      MvPolynomial.aeval x ((hopfAdjointUniversalTangentMatrix b).charpoly.coeff n) := by
  rw [← hopfAdjointUniversalTangentMatrix_aeval b x, Matrix.charpoly_map, Polynomial.coeff_map]
  rfl

/-- Specialization cannot decrease the zero-root multiplicity. -/
theorem hopfAdjointGenericZeroMultiplicity_le {A : Type*} [CommRing A] [Nontrivial A] [Algebra F A]
    (b : Basis ι F C) (x : ι → A) :
    hopfAdjointGenericZeroMultiplicity b ≤ (hopfAdjointTangentMatrix b x).charpoly.natTrailingDegree := by
  by_contra hn
  rw [not_le] at hn
  have h := Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hn
  exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr (Matrix.charpoly_monic _).ne_zero)
    ((hopfAdjointTangentMatrix_charpoly_coeff b x _).trans (by rw [h, map_zero]))

/-- Nonvanishing of the regular polynomial is exactly minimal multiplicity
of the zero root, compatibly with scalar extension. -/
theorem hopfAdjointTangentMatrix_regular_iff {A : Type*} [CommRing A] [Nontrivial A] [Algebra F A]
    (b : Basis ι F C) (x : ι → A) :
    MvPolynomial.aeval x (hopfAdjointRegularPolynomial b) ≠ 0 ↔
      (hopfAdjointTangentMatrix b x).charpoly.natTrailingDegree =
        hopfAdjointGenericZeroMultiplicity b := by
  change MvPolynomial.aeval x ((hopfAdjointUniversalTangentMatrix b).charpoly.coeff
      (hopfAdjointGenericZeroMultiplicity b)) ≠ 0 ↔ _
  rw [← hopfAdjointTangentMatrix_charpoly_coeff]
  constructor
  · intro h
    exact le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero h)
      (hopfAdjointGenericZeroMultiplicity_le b x)
  · intro h
    rw [← h]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr (Matrix.charpoly_monic _).ne_zero

/-- A twisted Lie space over an infinite ground field has a vector with
generic zero-root multiplicity. This uses the actual adjoint cocycle. -/
theorem exists_twistedHopfLieVector_regular {Ω : Type*} [Field Ω] [Algebra F Ω] [Infinite F]
    (b : Basis ι F C) (E : FiniteGaloisIntermediateField F Ω)
    (c : (E ≃ₐ[F] E) → H →ₐ[F] E) (hc : IsHopfPointCocycle c) :
    ∃ x : HopfLieVector F H E,
      (hopfAdjointTangentMatrix b (fun i => x (b i))).charpoly.natTrailingDegree =
        hopfAdjointGenericZeroMultiplicity b ∧
      ∀ σ, hopfAdjoint (c σ) (σ.toAlgHom.toLinearMap.comp x) = x := by
  let p := MvPolynomial.map (algebraMap F E) (hopfAdjointRegularPolynomial b)
  have hp : p ≠ 0 := by
    intro hp
    apply hopfAdjointRegularPolynomial_ne_zero b
    exact MvPolynomial.map_injective _ (RingHom.injective (algebraMap F E))
      (hp.trans (map_zero (MvPolynomial.map (algebraMap F E))).symm)
  obtain ⟨x, hx, hFix⟩ := exists_twistedHopfLieVector_eval_ne_zero b E c hc p hp
  refine ⟨x, (hopfAdjointTangentMatrix_regular_iff b (fun i => x (b i))).mp ?_, hFix⟩
  simpa only [p, MvPolynomial.eval_map, MvPolynomial.aeval_eq_eval₂Hom] using hx

end RegularLocus

end WideE
