import WideE.Comparison
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Matrix.RowCol
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.Abel

/-!
# Horizontal maps in the basis of fundamental solutions

The ordinary-point gauge transforms a horizontal map into a constant matrix. For
multiplication, the matrix on the source is the tensor square of the fundamental matrix.
-/

noncomputable section

open scoped Matrix Kronecker BigOperators

namespace WideE

section Derivation

variable {K L ι κ τ : Type*} [CommRing K] [CommRing L] [Algebra K L]
variable (D : Derivation K L L)

theorem matrix_deriv_mul [Fintype κ] (F : Matrix ι κ L) (G : Matrix κ τ L) :
    (F * G).map D = F.map D * G + F * G.map D := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, Derivation.leibniz, smul_eq_mul,
    Matrix.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_comm (G l j) (D (F i l)), add_comm]

@[simp] theorem matrix_deriv_one [DecidableEq ι] : (1 : Matrix ι ι L).map D = 0 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply, apply_ite D,
    Derivation.map_one_eq_zero, map_zero, ite_self, Matrix.zero_apply]

theorem matrix_deriv_inv [Fintype ι] [DecidableEq ι] (Y : (Matrix ι ι L)ˣ) :
    (↑Y⁻¹ : Matrix ι ι L).map D =
      -((↑Y⁻¹ : Matrix ι ι L) * (Y : Matrix ι ι L).map D * (↑Y⁻¹ : Matrix ι ι L)) := by
  have h : (↑Y⁻¹ : Matrix ι ι L).map D * (Y : Matrix ι ι L) +
      (↑Y⁻¹ : Matrix ι ι L) * (Y : Matrix ι ι L).map D = 0 := by
    rw [← matrix_deriv_mul, Units.inv_mul, matrix_deriv_one]
  have h' := congrArg (fun T : Matrix ι ι L => T * (↑Y⁻¹ : Matrix ι ι L)) h
  simp only [Matrix.add_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Matrix.zero_mul] at h'
  simpa only [Matrix.mul_assoc] using eq_neg_of_add_eq_zero_left h'

theorem matrix_deriv_kronecker {σ : Type*} (F : Matrix ι κ L) (G : Matrix τ σ L) :
    (F ⊗ₖ G).map D = F.map D ⊗ₖ G + F ⊗ₖ G.map D := by
  ext i j
  simp only [Matrix.map_apply, Matrix.kroneckerMap_apply, Matrix.add_apply, Derivation.leibniz,
    smul_eq_mul]
  rw [mul_comm (G i.2 j.2) (D (F i.1 j.1)), add_comm]

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The gauge of a horizontal rectangular matrix has entrywise derivative zero. -/
theorem horizontal_gauge_deriv_eq_zero
    {BM : Matrix ι ι L} {BN : Matrix κ κ L} {F : Matrix κ ι L}
    (YM : (Matrix ι ι L)ˣ) (YN : (Matrix κ κ L)ˣ)
    (hM : (YM : Matrix ι ι L).map D = BM * (YM : Matrix ι ι L))
    (hN : (YN : Matrix κ κ L).map D = BN * (YN : Matrix κ κ L))
    (hF : F.map D = BN * F - F * BM) :
    ((↑YN⁻¹ : Matrix κ κ L) * F * (YM : Matrix ι ι L)).map D = 0 := by
  simp only [matrix_deriv_mul, matrix_deriv_inv, hM, hN, hF, Matrix.add_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc,
    Units.mul_inv, Matrix.mul_one]
  abel

/-- The tensor square of a fundamental matrix is a fundamental matrix for the product rule. -/
theorem matrix_deriv_tensorSquare {B Y : Matrix ι ι L} (hY : Y.map D = B * Y) :
    (Y ⊗ₖ Y).map D = ((B ⊗ₖ (1 : Matrix ι ι L)) + ((1 : Matrix ι ι L) ⊗ₖ B)) * (Y ⊗ₖ Y) := by
  simp only [matrix_deriv_kronecker, hY, Matrix.add_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- The gauge of a horizontal multiplication matrix has entrywise derivative zero. -/
theorem horizontal_mul_gauge_deriv_eq_zero
    {BM : Matrix ι ι L} {BN : Matrix κ κ L} {F : Matrix κ (ι × ι) L}
    (YM : (Matrix ι ι L)ˣ) (YN : (Matrix κ κ L)ˣ)
    (hM : (YM : Matrix ι ι L).map D = BM * (YM : Matrix ι ι L))
    (hN : (YN : Matrix κ κ L).map D = BN * (YN : Matrix κ κ L))
    (hF : F.map D = BN * F - F * (BM ⊗ₖ (1 : Matrix ι ι L) + (1 : Matrix ι ι L) ⊗ₖ BM)) :
    ((↑YN⁻¹ : Matrix κ κ L) * F * ((YM : Matrix ι ι L) ⊗ₖ (YM : Matrix ι ι L))).map D = 0 := by
  let tensorSquare : (Matrix (ι × ι) (ι × ι) L)ˣ :=
    ⟨(YM : Matrix ι ι L) ⊗ₖ (YM : Matrix ι ι L), (↑YM⁻¹ : Matrix ι ι L) ⊗ₖ (↑YM⁻¹ : Matrix ι ι L),
      by rw [← Matrix.mul_kronecker_mul, Units.mul_inv, Matrix.one_kronecker_one],
      by rw [← Matrix.mul_kronecker_mul, Units.inv_mul, Matrix.one_kronecker_one]⟩
  exact horizontal_gauge_deriv_eq_zero D tensorSquare YN (matrix_deriv_tensorSquare D hM) hN hF

omit [Algebra K L] in
private theorem map_inv_eq_one (E : L →+* K) (Y : (Matrix κ κ L)ˣ)
    (hY : (Y : Matrix κ κ L).map E = 1) : (↑Y⁻¹ : Matrix κ κ L).map E = 1 := by
  have h := congrArg E.mapMatrix (Units.mul_inv Y)
  simpa only [map_mul, map_one, RingHom.mapMatrix_apply, hY, Matrix.one_mul] using h

/-- A horizontal gauge with zero derivative is the scalar extension of its specialization. -/
theorem horizontal_recover_of_specialized_gauge
    (E : L →+* K) (hE : ∀ x, D x = 0 → algebraMap K L (E x) = x)
    (YM : Matrix ι ι L) (YN : (Matrix κ κ L)ˣ) (F : Matrix κ ι L)
    (hGauge : ((↑YN⁻¹ : Matrix κ κ L) * F * YM).map D = 0)
    (hM0 : YM.map E = 1) (hN0 : (YN : Matrix κ κ L).map E = 1) :
    F * YM = (YN : Matrix κ κ L) * (F.map E).map (algebraMap K L) := by
  let G := (↑YN⁻¹ : Matrix κ κ L) * F * YM
  have hG0 : G.map E = F.map E := by
    simp only [G, Matrix.map_mul, map_inv_eq_one E YN hN0, Matrix.one_mul, hM0, Matrix.mul_one]
  have hG : G = (F.map E).map (algebraMap K L) := by
    rw [← hG0]
    ext i j
    exact (hE (G i j) (Matrix.ext_iff.mpr hGauge i j)).symm
  calc
    F * YM = (YN : Matrix κ κ L) * G := by
      simp only [G, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    _ = _ := congrArg (fun T => (YN : Matrix κ κ L) * T) hG

omit [DecidableEq κ] in
private theorem replicateCol_horizontal {BN : Matrix κ κ L} {u : κ → L}
    (hU : D ∘ u = BN *ᵥ u) : (Matrix.replicateCol Unit u).map D =
      BN * Matrix.replicateCol Unit u - Matrix.replicateCol Unit u * (0 : Matrix Unit Unit L) := by
  rw [Matrix.mul_zero, sub_zero, ← Matrix.replicateCol_mulVec]
  ext i j
  exact congrFun hU i

/-- The unit column is a horizontal map from the trivial rank-one system. -/
theorem horizontal_unit_gauge_deriv_eq_zero
    {BN : Matrix κ κ L} (YN : (Matrix κ κ L)ˣ) {u : κ → L}
    (hN : (YN : Matrix κ κ L).map D = BN * (YN : Matrix κ κ L))
    (hU : D ∘ u = BN *ᵥ u) :
    D ∘ ((↑YN⁻¹ : Matrix κ κ L) *ᵥ u) = 0 := by
  have h := horizontal_gauge_deriv_eq_zero D (1 : (Matrix Unit Unit L)ˣ) YN
    (by simp [Matrix.zero_mul]) hN (replicateCol_horizontal D hU)
  simp only [Units.val_one, Matrix.mul_one, ← Matrix.replicateCol_mulVec] at h
  funext i
  exact Matrix.ext_iff.mpr h i ()

end Derivation

section TensorMatrix

variable {R S ι κ τ σ : Type*} [CommRing R] [CommRing S]

theorem matrix_map_kronecker (E : R →+* S) (A : Matrix ι κ R) (B : Matrix τ σ R) :
    (A ⊗ₖ B).map E = A.map E ⊗ₖ B.map E := by
  ext i j
  exact E.map_mul (A i.1 j.1) (B i.2 j.2)

variable [Fintype ι]

/-- The product applied to two matrix columns is a column of the tensor product composite. -/
theorem coordinateProduct_columns_eq (F : Matrix κ (ι × ι) R) (A : Matrix ι ι R)
    (i j : ι) (l : κ) :
    coordinateProduct (fun a b m => F m (a, b)) (fun a => A a i) (fun b => A b j) l =
      (F * (A ⊗ₖ A)) l (i, j) := by
  simp only [coordinateProduct_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ac_rfl

variable [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The tensor matrix identity and the unit column identity give a coordinate comparison. -/
def CoordinateComparison.ofTensorMatrix {F₀ F : Matrix κ (ι × ι) R} {d₀ d : κ → R}
    (A : (Matrix ι ι R)ˣ) (B : (Matrix κ κ R)ˣ)
    (hF : F * ((A : Matrix ι ι R) ⊗ₖ (A : Matrix ι ι R)) = (B : Matrix κ κ R) * F₀)
    (hd : (B : Matrix κ κ R) *ᵥ d₀ = d) :
    CoordinateComparison (fun i j l => F₀ l (i, j)) (fun i j l => F l (i, j)) d₀ d :=
  CoordinateComparison.ofBasis A B (by
    intro i j
    funext l
    rw [coordinateProduct_columns_eq, hF]
    rfl) hd

end TensorMatrix

section OrdinaryPoint

variable {K ι κ : Type*} [CommRing K] [NoZeroSMulDivisors ℕ K]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem powerSeries_eq_C_of_derivative_eq_zero (p : PowerSeries K)
    (hp : PowerSeries.derivative K p = 0) : p = PowerSeries.C K (PowerSeries.constantCoeff K p) := by
  apply PowerSeries.derivative.ext
  · rw [hp, PowerSeries.derivative_C]
  · rw [PowerSeries.constantCoeff_C]

/-- A normalized formal fundamental matrix identifies multiplication with its fiber at one. -/
theorem horizontal_mul_at_ordinary_point
    {BM : Matrix ι ι (PowerSeries K)} {BN : Matrix κ κ (PowerSeries K)}
    {F : Matrix κ (ι × ι) (PowerSeries K)}
    (YM : (Matrix ι ι (PowerSeries K))ˣ) (YN : (Matrix κ κ (PowerSeries K))ˣ)
    (hM : (YM : Matrix ι ι (PowerSeries K)).map (PowerSeries.derivative K) =
      BM * (YM : Matrix ι ι (PowerSeries K)))
    (hN : (YN : Matrix κ κ (PowerSeries K)).map (PowerSeries.derivative K) =
      BN * (YN : Matrix κ κ (PowerSeries K)))
    (hF : F.map (PowerSeries.derivative K) =
      BN * F - F * (BM ⊗ₖ (1 : Matrix ι ι (PowerSeries K)) +
        (1 : Matrix ι ι (PowerSeries K)) ⊗ₖ BM))
    (hM₀ : (YM : Matrix ι ι (PowerSeries K)).map (PowerSeries.constantCoeff K) = 1)
    (hN₀ : (YN : Matrix κ κ (PowerSeries K)).map (PowerSeries.constantCoeff K) = 1) :
    F * ((YM : Matrix ι ι (PowerSeries K)) ⊗ₖ (YM : Matrix ι ι (PowerSeries K))) =
      (YN : Matrix κ κ (PowerSeries K)) *
        (F.map (PowerSeries.constantCoeff K)).map (PowerSeries.C K) := by
  exact horizontal_recover_of_specialized_gauge (PowerSeries.derivative K) (PowerSeries.constantCoeff K)
    (fun p hp => (powerSeries_eq_C_of_derivative_eq_zero p hp).symm) _ YN F
    (horizontal_mul_gauge_deriv_eq_zero (PowerSeries.derivative K) YM YN hM hN hF)
    (by rw [matrix_map_kronecker, hM₀, Matrix.one_kronecker_one]) hN₀

/-- The normalized formal fundamental matrix sends the fiber unit to the original unit column. -/
theorem horizontal_unit_at_ordinary_point
    {BN : Matrix κ κ (PowerSeries K)} {u : κ → PowerSeries K} (YN : (Matrix κ κ (PowerSeries K))ˣ)
    (hN : (YN : Matrix κ κ (PowerSeries K)).map (PowerSeries.derivative K) =
      BN * (YN : Matrix κ κ (PowerSeries K)))
    (hU : PowerSeries.derivative K ∘ u = BN *ᵥ u)
    (hN₀ : (YN : Matrix κ κ (PowerSeries K)).map (PowerSeries.constantCoeff K) = 1) :
    (YN : Matrix κ κ (PowerSeries K)) *ᵥ (PowerSeries.C K ∘ PowerSeries.constantCoeff K ∘ u) = u := by
  have h := horizontal_recover_of_specialized_gauge (PowerSeries.derivative K) (PowerSeries.constantCoeff K)
    (fun p hp => (powerSeries_eq_C_of_derivative_eq_zero p hp).symm)
    (1 : Matrix Unit Unit (PowerSeries K)) YN (Matrix.replicateCol Unit u)
    (by
      rw [Matrix.mul_one, ← Matrix.replicateCol_mulVec]
      apply Matrix.ext
      intro i j
      exact congrFun (horizontal_unit_gauge_deriv_eq_zero (PowerSeries.derivative K) YN hN hU) i)
    (Matrix.map_one _ (map_zero _) (map_one _)) hN₀
  have hCol : ((Matrix.replicateCol Unit u).map (PowerSeries.constantCoeff K)).map
      (algebraMap K (PowerSeries K)) =
      Matrix.replicateCol Unit (PowerSeries.C K ∘ PowerSeries.constantCoeff K ∘ u) := rfl
  rw [Matrix.mul_one, hCol, ← Matrix.replicateCol_mulVec] at h
  funext i
  exact (Matrix.ext_iff.mpr h i ()).symm

end OrdinaryPoint
end WideE
