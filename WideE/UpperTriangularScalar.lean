import WideE.ScalarGroupQuotient
import WideE.ScalarKernelTorsor
import Mathlib.LinearAlgebra.Matrix.Block

/-! Scalar group coordinates of an upper triangular affine group representation. -/

noncomputable section

open scoped TensorProduct BigOperators Matrix
open TensorProduct

namespace WideE

section ScalarCoordinates

variable {k H : Type*} [Field k] [CommRing H] [HopfAlgebra k H]

attribute [local instance] additivePolynomialHopf

private def scalarBialgHomOfAlgHom {A : Type*} [CommRing A] [Bialgebra k A] (f : A →ₐ[k] H)
    (hε : (Bialgebra.counitAlgHom k H).comp f = Bialgebra.counitAlgHom k A)
    (hΔ : (Algebra.TensorProduct.map f f).comp (Bialgebra.comulAlgHom k A) =
      (Bialgebra.comulAlgHom k H).comp f) : A →ₐc[k] H :=
  BialgHom.ofAlgHom f (LinearMap.ext fun x => DFunLike.congr_fun hε x)
    (LinearMap.ext fun x => DFunLike.congr_fun hΔ x)

/-- A primitive element with counit zero gives the additive scalar map by evaluation. -/
def additiveScalarMap (x : H) (hε : Coalgebra.counit (R := k) x = 0)
    (hΔ : Coalgebra.comul (R := k) x = (1 : H) ⊗ₜ[k] x + x ⊗ₜ[k] (1 : H)) :
    Polynomial k →ₐc[k] H := by
  let f : Polynomial k →ₐ[k] H := Polynomial.aeval x
  have hf : f Polynomial.X = x := Polynomial.aeval_X x
  refine scalarBialgHomOfAlgHom f (Polynomial.algHom_ext ?_) (Polynomial.algHom_ext ?_)
  · change Coalgebra.counit (R := k) (f Polynomial.X) = Polynomial.aeval (0 : k) Polynomial.X
    rw [hf, hε, Polynomial.aeval_X]
  · change Algebra.TensorProduct.map f f (Bialgebra.comulAlgHom k (Polynomial k) Polynomial.X) =
      Coalgebra.comul (R := k) (f Polynomial.X)
    simp only [additivePolynomialHopf_comul_X, map_add, Algebra.TensorProduct.map_tmul,
      map_one, hf, hΔ]

@[simp] theorem additiveScalarMap_X (x : H) (hε : Coalgebra.counit (R := k) x = 0)
    (hΔ : Coalgebra.comul (R := k) x = (1 : H) ⊗ₜ[k] x + x ⊗ₜ[k] (1 : H)) :
    additiveScalarMap x hε hΔ Polynomial.X = x := Polynomial.aeval_X x

/-- A group-like unit with counit one gives the Laurent scalar map by evaluation. -/
def multiplicativeScalarMap (u : Hˣ) (hε : Coalgebra.counit (R := k) (u : H) = 1)
    (hΔ : Coalgebra.comul (R := k) (u : H) = (u : H) ⊗ₜ[k] (u : H)) :
    LaurentPolynomial k →ₐc[k] H := by
  let f : LaurentPolynomial k →ₐ[k] H := laurentKernelCoordinate u
  have hf : f (LaurentPolynomial.T 1) = u := laurentKernelCoordinate_T u
  refine scalarBialgHomOfAlgHom f (laurentAlgHom_ext ?_) (laurentAlgHom_ext ?_)
  · change Coalgebra.counit (R := k) (f (LaurentPolynomial.T 1)) =
      Coalgebra.counit (R := k) (LaurentPolynomial.T (R := k) 1)
    rw [hf, hε, LaurentPolynomial.counit_T]
  · change Algebra.TensorProduct.map f f (Coalgebra.comul (R := k) (LaurentPolynomial.T 1)) =
      Coalgebra.comul (R := k) (f (LaurentPolynomial.T 1))
    rw [LaurentPolynomial.comul_T, Algebra.TensorProduct.map_tmul, hf, hΔ]

@[simp] theorem multiplicativeScalarMap_T (u : Hˣ) (hε : Coalgebra.counit (R := k) (u : H) = 1)
    (hΔ : Coalgebra.comul (R := k) (u : H) = (u : H) ⊗ₜ[k] (u : H)) :
    multiplicativeScalarMap u hε hΔ (LaurentPolynomial.T 1) = u := laurentKernelCoordinate_T u

private def groupLikeUnit (x : H) (hε : Coalgebra.counit (R := k) x = 1)
    (hΔ : Coalgebra.comul (R := k) x = x ⊗ₜ[k] x) : Hˣ :=
  ⟨x, HopfAlgebra.antipode (R := k) x, by
    simpa only [hΔ, hε, LinearMap.lTensor_tmul, LinearMap.mul'_apply, map_one] using
      HopfAlgebra.mul_antipode_lTensor_comul_apply (R := k) x, by
    simpa only [hΔ, hε, LinearMap.rTensor_tmul, LinearMap.mul'_apply, map_one] using
      HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) x⟩

end ScalarCoordinates

section Diagonal

variable {k H ι : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [Fintype ι] [LinearOrder ι]

/-- Each diagonal coefficient of an upper triangular group matrix is group-like. -/
theorem upperTriangular_diagonal_comul (M : Matrix ι ι H)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (hUpper : M.BlockTriangular id) (i : ι) :
    Coalgebra.comul (R := k) (M i i) = M i i ⊗ₜ[k] M i i := by
  rw [hΔ, Finset.sum_eq_single i]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with hl | hl
    · rw [hUpper hl, zero_tmul]
    · rw [hUpper hl, tmul_zero]
  · simp

/-- The antipode supplies the inverse of a group-like diagonal coefficient. -/
def upperTriangular_diagonalUnit (M : Matrix ι ι H)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (hUpper : M.BlockTriangular id) (i : ι)
    (hεi : Coalgebra.counit (R := k) (M i i) = 1) : Hˣ :=
  groupLikeUnit (M i i) hεi (upperTriangular_diagonal_comul M hΔ hUpper i)

@[simp] theorem upperTriangular_diagonalUnit_val (M : Matrix ι ι H)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (hUpper : M.BlockTriangular id) (i : ι)
    (hεi : Coalgebra.counit (R := k) (M i i) = 1) :
    (upperTriangular_diagonalUnit M hΔ hUpper i hεi : H) = M i i := rfl

/-- The actual morphism to the multiplicative group given by a diagonal coefficient. -/
def upperTriangular_diagonalScalarMap (M : Matrix ι ι H)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (hUpper : M.BlockTriangular id) (i : ι)
    (hεi : Coalgebra.counit (R := k) (M i i) = 1) : LaurentPolynomial k →ₐc[k] H :=
  let hΔi := upperTriangular_diagonal_comul M hΔ hUpper i
  multiplicativeScalarMap (upperTriangular_diagonalUnit M hΔ hUpper i hεi) hεi hΔi

@[simp] theorem upperTriangular_diagonalScalarMap_T (M : Matrix ι ι H)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (hUpper : M.BlockTriangular id) (i : ι)
    (hεi : Coalgebra.counit (R := k) (M i i) = 1) :
    upperTriangular_diagonalScalarMap M hΔ hUpper i hεi (LaurentPolynomial.T 1) = M i i := by
  rw [upperTriangular_diagonalScalarMap, multiplicativeScalarMap_T]
  rfl

end Diagonal

section Superdiagonal

variable {k H : Type*} [Field k] [CommRing H] [HopfAlgebra k H] {n : ℕ}

attribute [local instance] additivePolynomialHopf

/-- An entry on the first nonzero superdiagonal of a unipotent upper triangular
group matrix is primitive. -/
theorem upperTriangular_firstSuperdiagonal_comul (M : Matrix (Fin n) (Fin n) H)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (hUpper : M.BlockTriangular id) (hDiag : ∀ i, M i i = 1)
    {i j : Fin n} (hij : i < j)
    (hZero : ∀ a b : Fin n, a < b → b.val - a.val < j.val - i.val → M a b = 0) :
    Coalgebra.comul (R := k) (M i j) = (1 : H) ⊗ₜ[k] M i j + M i j ⊗ₜ[k] (1 : H) := by
  have hTerm (l : Fin n) : M i l ⊗ₜ[k] M l j =
      (if l = i then (1 : H) ⊗ₜ[k] M i j else 0) +
      (if l = j then M i j ⊗ₜ[k] (1 : H) else 0) := by
    by_cases hli : l = i
    · subst l
      simp [hDiag, hij.ne]
    by_cases hlj : l = j
    · subst l
      simp [hDiag, hli]
    rcases lt_or_gt_of_ne hli with hli' | hil
    · simp only [hUpper hli', zero_tmul, if_neg hli, if_neg hlj, add_zero]
    rcases lt_or_gt_of_ne hlj with hlj' | hjl
    · have hlt : l.val - i.val < j.val - i.val := by omega
      simp only [hZero i l hil hlt, zero_tmul, if_neg hli, if_neg hlj, add_zero]
    · simp only [hUpper hjl, tmul_zero, if_neg hli, if_neg hlj, add_zero]
  rw [hΔ, Finset.sum_congr rfl (fun l _ => hTerm l), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- A nonidentity unipotent upper triangular group matrix has a nonzero primitive
coefficient on its first nonzero superdiagonal. -/
theorem exists_upperTriangular_primitiveEntry (M : Matrix (Fin n) (Fin n) H)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (hUpper : M.BlockTriangular id) (hDiag : ∀ i, M i i = 1) (hne : M ≠ 1) :
    ∃ i j : Fin n, i < j ∧ M i j ≠ 0 ∧
      Coalgebra.comul (R := k) (M i j) = (1 : H) ⊗ₜ[k] M i j + M i j ⊗ₜ[k] (1 : H) := by
  classical
  have hneEntry : ∃ i j : Fin n, i < j ∧ M i j ≠ 0 := by
    by_contra! h
    apply hne
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [h i j hij, Matrix.one_apply, if_neg hij.ne]
    · rw [hDiag, Matrix.one_apply, if_pos rfl]
    · rw [hUpper hji, Matrix.one_apply, if_neg hji.ne']
  let P := fun d : ℕ => ∃ i j : Fin n, i < j ∧ j.val - i.val = d ∧ M i j ≠ 0
  have hP : ∃ d, P d := by
    obtain ⟨i, j, hij, hij0⟩ := hneEntry
    exact ⟨j.val - i.val, i, j, hij, rfl, hij0⟩
  obtain ⟨i, j, hij, hdist, hij0⟩ := Nat.find_spec hP
  refine ⟨i, j, hij, hij0, upperTriangular_firstSuperdiagonal_comul M hΔ hUpper hDiag hij ?_⟩
  intro a b hab hlt
  by_contra hab0
  have hmin := Nat.find_min' hP (show P (b.val - a.val) from ⟨a, b, hab, rfl, hab0⟩)
  exact (not_lt_of_ge hmin) (hdist ▸ hlt)

/-- A nonidentity upper triangular group matrix determines an actual scalar
group map carrying the additive or multiplicative coordinate to a nontrivial entry. -/
theorem exists_upperTriangular_scalarMap (M : Matrix (Fin n) (Fin n) H)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (M i j) = if i = j then 1 else 0)
    (hUpper : M.BlockTriangular id) (hne : M ≠ 1) :
    (∃ (i : Fin n) (f : LaurentPolynomial k →ₐc[k] H),
      f (LaurentPolynomial.T 1) = M i i ∧ M i i ≠ 1) ∨
    (∃ (i j : Fin n) (f : Polynomial k →ₐc[k] H), i < j ∧ f Polynomial.X = M i j ∧ M i j ≠ 0) := by
  classical
  by_cases hDiag : ∀ i, M i i = 1
  · obtain ⟨i, j, hij, hij0, hijΔ⟩ := exists_upperTriangular_primitiveEntry M hΔ hUpper hDiag hne
    have hijε : Coalgebra.counit (R := k) (M i j) = 0 := (hε i j).trans (if_neg hij.ne)
    exact Or.inr ⟨i, j, additiveScalarMap (M i j) hijε hijΔ, hij, additiveScalarMap_X _ _ _, hij0⟩
  · obtain ⟨i, hi⟩ := not_forall.mp hDiag
    have hiε : Coalgebra.counit (R := k) (M i i) = 1 := (hε i i).trans (if_pos rfl)
    exact Or.inl ⟨i, upperTriangular_diagonalScalarMap M hΔ hUpper i hiε,
      upperTriangular_diagonalScalarMap_T M hΔ hUpper i hiε, hi⟩

end Superdiagonal

section MatrixReduction

variable {n : ℕ}

/-- Number of coefficients that differ from the identity matrix. -/
def matrixNonidentityEntryCount {H : Type*} [Semiring H] (M : Matrix (Fin n) (Fin n) H) : ℕ := by
  classical
  exact (Finset.univ.filter fun ij : Fin n × Fin n => M ij.1 ij.2 ≠ (1 : Matrix _ _ H) ij.1 ij.2).card

@[simp] theorem matrixNonidentityEntryCount_eq_zero {H : Type*} [Semiring H]
    {M : Matrix (Fin n) (Fin n) H} : matrixNonidentityEntryCount M = 0 ↔ M = 1 := by
  classical
  rw [matrixNonidentityEntryCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    exact Matrix.ext fun i j => not_not.mp (h (Finset.mem_univ (i, j)))
  · intro h
    simp [h]

/-- Specializing any nonidentity entry to its identity value strictly decreases
the number of remaining nonidentity entries. -/
theorem matrixNonidentityEntryCount_map_lt {H J : Type*} [Semiring H] [Semiring J]
    (M : Matrix (Fin n) (Fin n) H) (f : H →+* J) (i j : Fin n)
    (hij : M i j ≠ (1 : Matrix _ _ H) i j) (hKill : f (M i j) = (1 : Matrix _ _ J) i j) :
    matrixNonidentityEntryCount (M.map f) < matrixNonidentityEntryCount M := by
  classical
  have hOne (a b : Fin n) : f ((1 : Matrix _ _ H) a b) = (1 : Matrix _ _ J) a b := by
    simp only [Matrix.one_apply, apply_ite f, map_one, map_zero]
  unfold matrixNonidentityEntryCount
  apply Finset.card_lt_card
  have hsub : (Finset.univ.filter fun ab : Fin n × Fin n =>
      (M.map f) ab.1 ab.2 ≠ (1 : Matrix _ _ J) ab.1 ab.2) ⊆
      (Finset.univ.filter fun ab : Fin n × Fin n => M ab.1 ab.2 ≠ (1 : Matrix _ _ H) ab.1 ab.2) := by
    intro ab hab
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => ?_⟩
    exact (Finset.mem_filter.mp hab).2 ((congrArg f h).trans (hOne ab.1 ab.2))
  exact (Finset.ssubset_iff_of_subset hsub).mpr ⟨(i, j), by simp [hij], by simp [hKill]⟩

variable {k H J : Type*} [CommRing k] [CommRing H] [CommRing J]
  [Bialgebra k H] [Bialgebra k J]

/-- The group matrix relations survive a bialgebra map. -/
theorem hopfMatrixRelations_map (M : Matrix (Fin n) (Fin n) H) (π : H →ₐc[k] J)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (M i j) = if i = j then 1 else 0) :
    let N := M.map (π : H →ₐ[k] J).toRingHom
    (∀ i j, Coalgebra.comul (R := k) (N i j) = ∑ l, N i l ⊗ₜ[k] N l j) ∧
      (∀ i j, Coalgebra.counit (R := k) (N i j) = if i = j then 1 else 0) := by
  let f : H →ₐ[k] J := π
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have hc := DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom π) (M i j)
    change Algebra.TensorProduct.map f f (Coalgebra.comul (R := k) (M i j)) =
      Coalgebra.comul (R := k) (f (M i j)) at hc
    rw [hΔ, map_sum] at hc
    simpa only [Matrix.map_apply, Algebra.TensorProduct.map_tmul] using hc.symm
  · exact (DFunLike.congr_fun (BialgHomClass.counitAlgHom_comp π) (M i j)).trans (hε i j)

/-- The group matrix relations and its triangularity survive a bialgebra map. -/
theorem upperTriangularGroupMatrix_map (M : Matrix (Fin n) (Fin n) H) (π : H →ₐc[k] J)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (M i j) = if i = j then 1 else 0)
    (hUpper : M.BlockTriangular id) :
    let N := M.map (π : H →ₐ[k] J).toRingHom
    (∀ i j, Coalgebra.comul (R := k) (N i j) = ∑ l, N i l ⊗ₜ[k] N l j) ∧
      (∀ i j, Coalgebra.counit (R := k) (N i j) = if i = j then 1 else 0) ∧
      N.BlockTriangular id := by
  obtain ⟨hd, he⟩ := hopfMatrixRelations_map M π hΔ hε
  exact ⟨hd, he, hUpper.map (π : H →ₐ[k] J).toRingHom⟩

/-- A surjective coefficient map preserves generation by the matrix entries. -/
theorem generatingMatrix_map (M : Matrix (Fin n) (Fin n) H) (f : H →ₐ[k] J)
    (hf : Function.Surjective f)
    (hGen : Algebra.adjoin k (Set.range fun ij : Fin n × Fin n => M ij.1 ij.2) = ⊤) :
    Algebra.adjoin k (Set.range fun ij : Fin n × Fin n => (M.map f.toRingHom) ij.1 ij.2) = ⊤ := by
  change Algebra.adjoin k (Set.range (f ∘ fun ij : Fin n × Fin n => M ij.1 ij.2)) = ⊤
  rw [Set.range_comp, Algebra.adjoin_image, hGen, Algebra.map_top, AlgHom.range_eq_top]
  exact hf

/-- When the generating matrix is the identity, all coordinates are scalars. -/
theorem algebraMap_surjective_of_identity_generatingMatrix (M : Matrix (Fin n) (Fin n) H)
    (hGen : Algebra.adjoin k (Set.range fun ij : Fin n × Fin n => M ij.1 ij.2) = ⊤)
    (hM : M = 1) : Function.Surjective (algebraMap k H) := by
  have hle : Algebra.adjoin k (Set.range fun ij : Fin n × Fin n => M ij.1 ij.2) ≤
      (⊥ : Subalgebra k H) := by
    apply Algebra.adjoin_le
    rintro _ ⟨⟨i, j⟩, rfl⟩
    change M i j ∈ (⊥ : Subalgebra k H)
    rw [hM, Matrix.one_apply]
    split
    · exact (⊥ : Subalgebra k H).one_mem
    · exact (⊥ : Subalgebra k H).zero_mem
  rw [hGen] at hle
  exact fun a => Algebra.mem_bot.mp (hle (Algebra.mem_top (R := k) (A := H)))

end MatrixReduction

end WideE
