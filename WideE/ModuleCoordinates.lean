import WideE.Comparison
import WideE.FiniteModule
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Tactic.Abel

/-!
# Coordinate equations of finite differential modules

The fundamental system matrix is the negative of the connection coefficients. The
Leibniz rule for the product and the derivative of one then give horizontal maps.
-/

noncomputable section

open scoped Matrix Kronecker BigOperators

namespace WideE

section Coordinates

variable {R M N ι κ : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (bM : Basis ι R M) (bN : Basis κ R N)

/-- The negative connection coefficients give the matrix of the fundamental system. -/
def connectionSystemMatrix (D : M →+ M) : Matrix ι ι R :=
  Matrix.of fun i j => -bM.repr (D (bM j)) i

/-- The matrix of multiplication in the chosen bases of the source and target. -/
def productCoefficientMatrix (P : M →ₗ[R] M →ₗ[R] N) : Matrix κ (ι × ι) R :=
  Matrix.of fun l ij => bN.repr (P (bM ij.1) (bM ij.2)) l

variable [Fintype ι]

/-- The bilinear coordinate product gives the coordinates of the original product. -/
theorem coordinateProduct_eq_repr (P : M →ₗ[R] M →ₗ[R] N) (x y : M) :
    coordinateProduct (fun i j l => productCoefficientMatrix bM bN P l (i, j))
      (bM.repr x) (bM.repr y) = bN.repr (P x y) := by
  funext l
  have h := congrArg₂ (fun p q : M => bN.repr (P p q) l) (bM.sum_repr x) (bM.sum_repr y)
  rw [coordinateProduct_apply]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum] at h
  rw [Finset.sum_comm] at h
  simpa only [productCoefficientMatrix, Matrix.of_apply, mul_left_comm] using h

variable (δ : R →+ R) (D : M →+ M) [DecidableEq ι]

/-- Differentiating a vector in coordinates adds the connection term. -/
theorem repr_connection
    (hD : ∀ (a : R) (x : M), D (a • x) = δ a • x + a • D x) (x : M) :
    (bM.repr (D x) : ι → R) = δ ∘ bM.repr x - connectionSystemMatrix bM D *ᵥ bM.repr x := by
  funext l
  have h := congrArg (fun v : M => bM.repr (D v) l) (bM.sum_repr x)
  simp only [map_sum, hD, map_add, map_smul, Finsupp.finset_sum_apply, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, Basis.repr_self, Finsupp.single_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h
  rw [← h]
  simp only [Pi.sub_apply, Function.comp_apply, connectionSystemMatrix, Matrix.of_apply,
    Matrix.mulVec, dotProduct, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]
  exact congrArg (δ (bM.repr x l) + ·) (Finset.sum_congr rfl fun _ _ => mul_comm _ _)

/-- The coordinate column of a horizontal element satisfies the fundamental system. -/
theorem repr_horizontal_unit
    (hD : ∀ (a : R) (x : M), D (a • x) = δ a • x + a • D x) {u : M} (hU : D u = 0) :
    δ ∘ bM.repr u = connectionSystemMatrix bM D *ᵥ bM.repr u := by
  have h := repr_connection bM δ D hD u
  rw [hU, map_zero, Finsupp.coe_zero] at h
  exact sub_eq_zero.mp h.symm

omit [DecidableEq ι] in
private theorem repr_product_basis_right (P : M →ₗ[R] M →ₗ[R] N) (x : M) (j : ι) (l : κ) :
    bN.repr (P x (bM j)) l = ∑ i, bM.repr x i * productCoefficientMatrix bM bN P l (i, j) := by
  have h := congrArg (fun v : M => bN.repr (P v (bM j)) l) (bM.sum_repr x)
  simpa only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul, productCoefficientMatrix,
    Matrix.of_apply] using h.symm

omit [DecidableEq ι] in
private theorem repr_product_basis_left (P : M →ₗ[R] M →ₗ[R] N) (i : ι) (y : M) (l : κ) :
    bN.repr (P (bM i) y) l = ∑ j, bM.repr y j * productCoefficientMatrix bM bN P l (i, j) := by
  have h := congrArg (fun v : M => bN.repr (P (bM i) v) l) (bM.sum_repr y)
  simpa only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul,
    productCoefficientMatrix, Matrix.of_apply] using h.symm

private theorem mul_kronecker_one_apply (F : Matrix κ (ι × ι) R) (B : Matrix ι ι R)
    (l : κ) (i j : ι) : (F * (B ⊗ₖ (1 : Matrix ι ι R))) l (i, j) = ∑ a, F l (a, j) * B a i := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem mul_one_kronecker_apply (F : Matrix κ (ι × ι) R) (B : Matrix ι ι R)
    (l : κ) (i j : ι) : (F * ((1 : Matrix ι ι R) ⊗ₖ B)) l (i, j) = ∑ b, F l (i, b) * B b j := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Matrix.kronecker_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

variable [Fintype κ] [DecidableEq κ]

/-- The coordinate matrix of a product satisfying Leibniz is horizontal. -/
theorem productCoefficientMatrix_horizontal (DN : N →+ N) (P : M →ₗ[R] M →ₗ[R] N)
    (hDN : ∀ (a : R) (x : N), DN (a • x) = δ a • x + a • DN x)
    (hP : ∀ x y, DN (P x y) = P (D x) y + P x (D y)) :
    (productCoefficientMatrix bM bN P).map δ =
      connectionSystemMatrix bN DN * productCoefficientMatrix bM bN P -
      productCoefficientMatrix bM bN P *
        (connectionSystemMatrix bM D ⊗ₖ (1 : Matrix ι ι R) +
          (1 : Matrix ι ι R) ⊗ₖ connectionSystemMatrix bM D) := by
  let F := productCoefficientMatrix bM bN P
  let BM := connectionSystemMatrix bM D
  let BN := connectionSystemMatrix bN DN
  change F.map δ = BN * F - F * (BM ⊗ₖ (1 : Matrix ι ι R) + (1 : Matrix ι ι R) ⊗ₖ BM)
  apply Matrix.ext
  rintro l ⟨i, j⟩
  have hLeft : (F * (BM ⊗ₖ (1 : Matrix ι ι R))) l (i, j) =
      -bN.repr (P (D (bM i)) (bM j)) l := by
    rw [mul_kronecker_one_apply, repr_product_basis_right bM bN P]
    simp only [BM, F, connectionSystemMatrix, Matrix.of_apply, mul_neg, Finset.sum_neg_distrib]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun _ _ => mul_comm _ _)
  have hRight : (F * ((1 : Matrix ι ι R) ⊗ₖ BM)) l (i, j) =
      -bN.repr (P (bM i) (D (bM j))) l := by
    rw [mul_one_kronecker_apply, repr_product_basis_left bM bN P]
    simp only [BM, F, connectionSystemMatrix, Matrix.of_apply, mul_neg, Finset.sum_neg_distrib]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun _ _ => mul_comm _ _)
  have h := congrFun (repr_connection bN δ DN hDN (P (bM i) (bM j))) l
  change bN.repr (DN (P (bM i) (bM j))) l = δ (F l (i, j)) - (BN * F) l (i, j) at h
  rw [hP, map_add, Finsupp.add_apply] at h
  simp only [Matrix.map_apply, Matrix.mul_add, Matrix.sub_apply, Matrix.add_apply, hLeft, hRight]
  rw [sub_eq_iff_eq_add.mp h.symm]
  abel

end Coordinates

section StableSubmodule

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (D : A →+ A) (M : Submodule R A)
variable (hM : ∀ x ∈ M, D x ∈ M)

/-- A stable submodule inherits the ambient connection. -/
def restrictConnection : M →+ M :=
  (D.restrict M).codRestrict M (fun x => hM x.val x.property)

@[simp] theorem restrictConnection_val (x : M) :
    (restrictConnection D M hM x).val = D x.val := rfl

theorem restrictConnection_smul (δ : R →+ R)
    (hD : ∀ (r : R) (a : A), D (r • a) = δ r • a + r • D a) (r : R) (x : M) :
    restrictConnection D M hM (r • x) = δ r • x + r • restrictConnection D M hM x :=
  Subtype.ext (hD r x.val)

variable (hLeib : ∀ x y : A, D (x * y) = D x * y + x * D y)

/-- The restricted connections on the module and its product span satisfy Leibniz. -/
theorem productBilinear_restrictConnection (x y : M) :
    restrictConnection D (M * M) (productModule_stable D hM hLeib) (productBilinear M x y) =
      productBilinear M (restrictConnection D M hM x) y +
      productBilinear M x (restrictConnection D M hM y) :=
  Subtype.ext (hLeib x.val y.val)

/-- The one in the product span is horizontal whenever the ambient derivative kills one. -/
theorem productOne_restrictConnection (h1 : (1 : A) ∈ M) (hD1 : D 1 = 0) :
    restrictConnection D (M * M) (productModule_stable D hM hLeib) (productOne M h1) = 0 :=
  Subtype.ext hD1

end StableSubmodule

section Specialization

variable {R S M N ι κ : Type*} [CommRing R] [CommRing S]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Fintype ι]

/-- A product congruence modulo an element killed by specialization gives a relation in coordinates. -/
theorem coordinateProduct_specialize_of_sub_eq_smul
    (φ : R →+* S) (bM : Basis ι R M) (bN : Basis κ R N) (P : M →ₗ[R] M →ₗ[R] N)
    {x y : M} {u w : N} {a : R} (ha : φ a = 0) (h : P x y - u = a • w) :
    coordinateProduct (fun i j l => φ (productCoefficientMatrix bM bN P l (i, j)))
      (φ ∘ bM.repr x) (φ ∘ bM.repr y) = φ ∘ bN.repr u := by
  funext l
  have hProduct := map_coordinateProduct φ (fun i j l => productCoefficientMatrix bM bN P l (i, j))
    (bM.repr x) (bM.repr y) l
  rw [coordinateProduct_eq_repr] at hProduct
  change coordinateProduct (fun i j l => φ (productCoefficientMatrix bM bN P l (i, j)))
    (φ ∘ bM.repr x) (φ ∘ bM.repr y) l = φ (bN.repr u l)
  refine hProduct.symm.trans ?_
  apply sub_eq_zero.mp
  have h' := congrArg (fun v : N => φ (bN.repr v l)) h
  simpa only [map_sub, Finsupp.sub_apply, map_smul, Finsupp.smul_apply, smul_eq_mul,
    map_mul, ha, zero_mul] using h'

end Specialization

section LaurentSpecialization

open LaurentPolynomial

variable {K M N ι κ : Type*} [CommRing K] [AddCommGroup M] [AddCommGroup N]
variable [Module (LaurentPolynomial K) M] [Module (LaurentPolynomial K) N] [Fintype ι]

/-- An inverse equation modulo `T - 1` in any two modules yields the fiber coordinate equation. -/
theorem inverse_coordinates_of_module_factorization
    (bM : Basis ι (LaurentPolynomial K) M) (bN : Basis κ (LaurentPolynomial K) N)
    (P : M →ₗ[LaurentPolynomial K] M →ₗ[LaurentPolynomial K] N)
    {x y : M} {u w : N} (h : P x y - u = (T 1 - 1 : LaurentPolynomial K) • w) :
    coordinateProduct (fun i j l => evalAtOne K (productCoefficientMatrix bM bN P l (i, j)))
      (evalAtOne K ∘ bM.repr x) (evalAtOne K ∘ bM.repr y) = evalAtOne K ∘ bN.repr u :=
  coordinateProduct_specialize_of_sub_eq_smul (evalAtOne K) bM bN P (by simp) h

end LaurentSpecialization

section InverseCoordinates

open LaurentPolynomial

variable {K A ι κ : Type*} [CommRing K] [CommRing A] [Algebra (LaurentPolynomial K) A]
variable [Fintype ι]

/-- The factorization of the residual product gives the inverse equation in the specialized bases. -/
theorem inverse_coordinates_of_factorization
    (M : Submodule (LaurentPolynomial K) A) (h1 : (1 : A) ∈ M)
    (bM : Basis ι (LaurentPolynomial K) M)
    (bN : Basis κ (LaurentPolynomial K) (M * M : Submodule (LaurentPolynomial K) A))
    (f g h : M) (hfactor : f.val * g.val - 1 = (T 1 - 1 : LaurentPolynomial K) • h.val) :
    coordinateProduct
      (fun i j l => evalAtOne K (productCoefficientMatrix bM bN (productBilinear M) l (i, j)))
      (evalAtOne K ∘ bM.repr f) (evalAtOne K ∘ bM.repr g) = evalAtOne K ∘ bN.repr (productOne M h1) := by
  let h' : (M * M : Submodule (LaurentPolynomial K) A) := ⟨h.val, le_productModule h1 h.property⟩
  exact inverse_coordinates_of_module_factorization bM bN (productBilinear M)
    (w := h') (Subtype.ext hfactor)

end InverseCoordinates
end WideE
