import WideE.LaurentEtaleFiber
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde

/-! A primitive-element chart of a finite étale Laurent algebra. -/

open scoped BigOperators Matrix TensorProduct

noncomputable section

namespace WideE

universe u

section Coordinates

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}
variable (b : Basis (Fin n) R A) (a : A)

/-- The change-of-coordinates matrix whose columns are the first powers of `a`. -/
def powerCoordinateMatrix : Matrix (Fin n) (Fin n) R :=
  b.toMatrix fun j : Fin n => a ^ j.val

/-- The open where the powers form a basis after specialization. -/
def powerCoordinateDet : R :=
  (powerCoordinateMatrix b a).det

/-- Laurent polynomial numerators of the coordinates in the power basis. -/
def powerCoordinateNumerator (s : A) : Fin n → R :=
  (powerCoordinateMatrix b a).adjugate *ᵥ (fun i => b.repr s i)

private def multiplicationMatrix : A →ₐ[R] Matrix (Fin n) (Fin n) R :=
  (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (Algebra.lmul R A)

/-- The monic characteristic polynomial of multiplication by the chosen element. -/
def primitiveCharpoly : Polynomial R :=
  (multiplicationMatrix b a).charpoly

theorem primitiveCharpoly_monic : (primitiveCharpoly b a).Monic :=
  Matrix.charpoly_monic _

theorem primitiveCharpoly_natDegree [Nontrivial R] : (primitiveCharpoly b a).natDegree = n := by
  simp [primitiveCharpoly]

theorem aeval_primitiveCharpoly : Polynomial.aeval a (primitiveCharpoly b a) = 0 := by
  have hMul : Function.Injective (Algebra.lmul R A) := by
    intro x y h
    have h' := LinearMap.congr_fun h (1 : A)
    change x * 1 = y * 1 at h'
    simpa only [mul_one] using h'
  apply ((LinearMap.toMatrixAlgEquiv b).injective.comp hMul :
    Function.Injective (multiplicationMatrix b))
  change multiplicationMatrix b (Polynomial.aeval a (primitiveCharpoly b a)) =
    multiplicationMatrix b 0
  rw [← Polynomial.aeval_algHom_apply, map_zero]
  exact Matrix.aeval_self_charpoly _

end Coordinates

section Specialization

variable {K R A : Type u} [Field K] [CommRing R] [CommRing A]
variable [Algebra K R] [Algebra K A] [Algebra R A] [IsScalarTower K R A]
variable {n : ℕ} (b : Basis (Fin n) R A) (a : A) (f : R →ₐ[K] K)

private theorem repr_evaluationFiberClass (s : A) (i : Fin n) :
    letI := f.toRingHom.toAlgebra
    (b.baseChange K).repr (evaluationFiberClass A f s) i = f (b.repr s i) := by
  letI := f.toRingHom.toAlgebra
  rw [evaluationFiberClass_apply, Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  rfl

theorem aeval_evaluationFiber_primitiveCharpoly :
    Polynomial.aeval (evaluationFiberClass A f a) ((primitiveCharpoly b a).map f.toRingHom) = 0 := by
  letI := f.toRingHom.toAlgebra
  let i : A →ₐ[R] EvaluationFiber A f := Algebra.TensorProduct.includeRight
  have h := congrArg i (aeval_primitiveCharpoly b a)
  rw [← Polynomial.aeval_algHom_apply, map_zero] at h
  change Polynomial.aeval (i a) ((primitiveCharpoly b a).map (algebraMap R K)) = 0
  rw [Polynomial.aeval_map_algebraMap]
  exact h

/-- The coefficients in the power basis at a specialization where its determinant is nonzero. -/
def evaluationPowerCoordinates (s : A) : Fin n → K :=
  ((powerCoordinateMatrix b a).map f)⁻¹ *ᵥ (fun i => f (b.repr s i))

omit [Algebra K A] [IsScalarTower K R A] in
theorem evaluationPowerCoordinates_eq_div (hD : f (powerCoordinateDet b a) ≠ 0)
    (s : A) (i : Fin n) :
    evaluationPowerCoordinates b a f s i =
      f (powerCoordinateNumerator b a s i) / f (powerCoordinateDet b a) := by
  let M := (powerCoordinateMatrix b a).map f
  let v (j : Fin n) := f (b.repr s j)
  have hdet : f (powerCoordinateDet b a) = M.det := RingHom.map_det f.toRingHom _
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr (hdet ▸ hD)
  have hval : (↑hu.unit⁻¹ : K) = M.det⁻¹ := by rw [Units.val_inv_eq_inv_val, hu.unit_spec]
  have hAdj : (powerCoordinateMatrix b a).adjugate.map f = M.adjugate :=
    f.toRingHom.map_adjugate _
  have h := RingHom.map_mulVec f.toRingHom (powerCoordinateMatrix b a).adjugate
    (fun j => b.repr s j) i
  change f (powerCoordinateNumerator b a s i) =
    ((powerCoordinateMatrix b a).adjugate.map f *ᵥ v) i at h
  change (M⁻¹ *ᵥ v) i = _
  rw [M.nonsing_inv_apply hu, hval, Matrix.smul_mulVec_assoc, Pi.smul_apply, smul_eq_mul,
    ← hAdj, ← h, hdet, div_eq_inv_mul]

theorem evaluationFiberClass_eq_sum_pow (hD : f (powerCoordinateDet b a) ≠ 0) (s : A) :
    evaluationFiberClass A f s =
      ∑ i : Fin n, evaluationPowerCoordinates b a f s i • (evaluationFiberClass A f a) ^ i.val := by
  letI := f.toRingHom.toAlgebra
  let c := evaluationFiberClass A f
  let M := (powerCoordinateMatrix b a).map f
  let d := evaluationPowerCoordinates b a f s
  have hu : IsUnit M.det :=
    isUnit_iff_ne_zero.mpr (fun h => hD ((RingHom.map_det f.toRingHom _).trans h))
  have hM : M *ᵥ d = (fun i => f (b.repr s i)) := by
    change M *ᵥ M⁻¹ *ᵥ (fun i => f (b.repr s i)) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hu, Matrix.one_mulVec]
  apply (b.baseChange K).repr.injective
  ext j
  change (b.baseChange K).repr (c s) j = (b.baseChange K).repr (∑ i : Fin n, d i • c a ^ i.val) j
  rw [repr_evaluationFiberClass]
  have hcoord := congrFun hM j
  change (∑ i : Fin n, f (b.repr (a ^ i.val) j) * d i) = f (b.repr s j) at hcoord
  rw [← hcoord]
  simp only [map_sum, Finsupp.finset_sum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← map_pow, repr_evaluationFiberClass, mul_comm]

/-- Recover the value of any element from the value of the primitive element. -/
theorem evaluationFiberPoint_apply_eq_sum (hD : f (powerCoordinateDet b a) ≠ 0)
    (p : EvaluationFiberPoint A f) (s : A) :
    p.val s = ∑ i : Fin n, evaluationPowerCoordinates b a f s i * (p.val a) ^ i.val := by
  let e := evaluationFiberPointsEquiv A f
  let g := e.symm p
  have hg (x : A) : g (evaluationFiberClass A f x) = p.val x := by
    rw [← evaluationFiberPointsEquiv_apply]
    exact congrArg (fun p : EvaluationFiberPoint A f => p.val x) (e.apply_symm_apply p)
  have h := congrArg g (evaluationFiberClass_eq_sum_pow b a f hD s)
  simpa only [map_sum, map_smul, map_pow, smul_eq_mul, hg] using h

theorem evaluationFiberPoint_sep_of_det_ne_zero (hD : f (powerCoordinateDet b a) ≠ 0) :
    Function.Injective (fun p : EvaluationFiberPoint A f => p.val a) := by
  intro p q h
  apply Subtype.ext
  apply AlgHom.ext
  intro s
  rw [evaluationFiberPoint_apply_eq_sum b a f hD p s, evaluationFiberPoint_apply_eq_sum b a f hD q s]
  change p.val a = q.val a at h
  rw [h]

theorem evaluationFiberPoint_isRoot (p : EvaluationFiberPoint A f) :
    ((primitiveCharpoly b a).map f.toRingHom).IsRoot (p.val a) := by
  let e := evaluationFiberPointsEquiv A f
  let g := e.symm p
  have hg : g (evaluationFiberClass A f a) = p.val a := by
    rw [← evaluationFiberPointsEquiv_apply]
    exact congrArg (fun p : EvaluationFiberPoint A f => p.val a) (e.apply_symm_apply p)
  have h := congrArg g (aeval_evaluationFiber_primitiveCharpoly b a f)
  rw [← Polynomial.aeval_algHom_apply, map_zero, hg] at h
  simpa only [Polynomial.IsRoot, Polynomial.aeval_def, Algebra.id.map_eq_id, Polynomial.eval] using h

omit [Algebra K A] [IsScalarTower K R A] in
theorem eval_primitiveCharpoly_natDegree :
    ((primitiveCharpoly b a).map f.toRingHom).natDegree = n := by
  rw [primitiveCharpoly, ← Matrix.charpoly_map]
  simp

end Specialization

section EtaleChart

variable {K R A : Type u} [Field K] [IsAlgClosed K] [CommRing R] [CommRing A]
variable [Algebra K R] [Algebra K A] [Algebra R A] [IsScalarTower K R A] [Algebra.Etale R A]
variable {n : ℕ} (b : Basis (Fin n) R A) (a : A) (f : R →ₐ[K] K)

/-- The points in each étale fiber are indexed by the indices of a basis of the covering algebra. -/
def evaluationFiberPoint_indexEquiv : Fin n ≃ EvaluationFiberPoint A f := by
  letI := f.toRingHom.toAlgebra
  letI := finite_evaluationFiberPoint A f
  letI := Fintype.ofFinite (EvaluationFiberPoint A f)
  exact ((b.baseChange K).map (evaluationFiberEquiv A f).toLinearEquiv).indexEquiv
    (Pi.basisFun K (EvaluationFiberPoint A f))

omit [IsAlgClosed K] [Algebra.Etale R A] in
private theorem eval_eq_sum_basis (p : EvaluationFiberPoint A f) (x : A) :
    p.val x = ∑ j, f (b.repr x j) * p.val (b j) := by
  have h := congrArg p.val (b.sum_repr x)
  rw [map_sum] at h
  have hg (r : R) : p.val (algebraMap R A r) = f r := DFunLike.congr_fun p.property r
  simpa only [Algebra.smul_def, map_mul, hg] using h.symm

/-- Distinct values at all points imply that the power basis determinant
specializes to a nonzero number. -/
theorem evaluationFiber_det_ne_zero_of_sep
    (hSep : Function.Injective (fun p : EvaluationFiberPoint A f => p.val a)) :
    f (powerCoordinateDet b a) ≠ 0 := by
  let e := evaluationFiberPoint_indexEquiv b f
  let E : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => (e i).val (b j)
  let M := (powerCoordinateMatrix b a).map f
  let v (i : Fin n) := (e i).val a
  have hv : Function.Injective v := hSep.comp e.injective
  have he : E * M = Matrix.vandermonde v := by
    ext i j
    change (∑ k : Fin n, (e i).val (b k) * f (b.repr (a ^ j.val) k)) = (v i) ^ j.val
    simp_rw [mul_comm ((e i).val (b _)), ← eval_eq_sum_basis]
    exact map_pow (e i).val a j.val
  intro hzero
  have hM : M.det = 0 := (RingHom.map_det f.toRingHom _).symm.trans hzero
  have h := congrArg Matrix.det he
  rw [Matrix.det_mul, hM, mul_zero] at h
  exact (Matrix.det_vandermonde_ne_zero_iff.mpr hv) h.symm

theorem exists_primitiveChart_at [Infinite K] : ∃ a : A, f (powerCoordinateDet b a) ≠ 0 := by
  obtain ⟨a, hSep⟩ := exists_separating_evaluationFiber_element A f
  exact ⟨a, evaluationFiber_det_ne_zero_of_sep b a f hSep⟩

private theorem evaluationFiber_roots_image
    (hD : f (powerCoordinateDet b a) ≠ 0) :
    let e := evaluationFiberPoint_indexEquiv b f
    let q := (primitiveCharpoly b a).map f.toRingHom
    letI := Classical.decEq K
    Finset.univ.image (fun i : Fin n => (e i).val a) = q.roots.toFinset := by
  classical
  let e := evaluationFiberPoint_indexEquiv b f
  let q := (primitiveCharpoly b a).map f.toRingHom
  let v (i : Fin n) := (e i).val a
  have hm : q.Monic := (primitiveCharpoly_monic b a).map _
  have hdeg : q.natDegree = n := eval_primitiveCharpoly_natDegree b a f
  have hv : Function.Injective v :=
    (evaluationFiberPoint_sep_of_det_ne_zero b a f hD).comp e.injective
  have hsub : Finset.univ.image v ⊆ q.roots.toFinset := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hm.ne_zero).mpr
      (evaluationFiberPoint_isRoot b a f (e i)))
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_image_of_injective _ hv, Finset.card_univ, Fintype.card_fin]
  exact (Multiset.toFinset_card_le _).trans (q.card_roots'.trans_eq hdeg)

/-- On the determinant open, the value of the primitive element is a
bijection between fiber points and roots of the specialized characteristic polynomial. -/
def evaluationFiberPointRootEquiv (hD : f (powerCoordinateDet b a) ≠ 0) :
    EvaluationFiberPoint A f ≃
      {y : K // ((primitiveCharpoly b a).map f.toRingHom).IsRoot y} := by
  classical
  let q := (primitiveCharpoly b a).map f.toRingHom
  let e := evaluationFiberPoint_indexEquiv b f
  refine Equiv.ofBijective (fun p => ⟨p.val a, evaluationFiberPoint_isRoot b a f p⟩) ⟨?_, ?_⟩
  · intro p p' he
    exact (evaluationFiberPoint_sep_of_det_ne_zero b a f hD) (congrArg Subtype.val he)
  · intro ⟨y, hy⟩
    have hm : q.Monic := (primitiveCharpoly_monic b a).map _
    have hymem : y ∈ q.roots.toFinset :=
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hm.ne_zero).mpr hy)
    rw [← evaluationFiber_roots_image b a f hD] at hymem
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hymem
    exact ⟨e i, Subtype.ext hi⟩

@[simp] theorem evaluationFiberPointRootEquiv_apply (hD : f (powerCoordinateDet b a) ≠ 0)
    (p : EvaluationFiberPoint A f) :
    (evaluationFiberPointRootEquiv b a f hD p).val = p.val a := rfl

theorem eval_primitiveCharpoly_separable (hD : f (powerCoordinateDet b a) ≠ 0) :
    ((primitiveCharpoly b a).map f.toRingHom).Separable := by
  classical
  let q := (primitiveCharpoly b a).map f.toRingHom
  let e := evaluationFiberPoint_indexEquiv b f
  have hm : q.Monic := (primitiveCharpoly_monic b a).map _
  have hdeg : q.natDegree = n := eval_primitiveCharpoly_natDegree b a f
  have hv : Function.Injective (fun i : Fin n => (e i).val a) :=
    (evaluationFiberPoint_sep_of_det_ne_zero b a f hD).comp e.injective
  have hcard : q.roots.toFinset.card = n := by
    rw [← evaluationFiber_roots_image b a f hD, Finset.card_image_of_injective _ hv,
      Finset.card_univ, Fintype.card_fin]
  apply (Polynomial.nodup_roots_iff_of_splits hm.ne_zero (IsAlgClosed.splits q)).mp
  apply Multiset.toFinset_card_eq_card_iff_nodup.mp
  rw [hcard]
  exact le_antisymm (by rw [← hcard]; exact Multiset.toFinset_card_le _) (q.card_roots'.trans_eq hdeg)

theorem eval_primitiveCharpoly_derivative_ne_zero (hD : f (powerCoordinateDet b a) ≠ 0)
    {y : K} (hy : ((primitiveCharpoly b a).map f.toRingHom).IsRoot y) :
    ((primitiveCharpoly b a).map f.toRingHom).derivative.eval y ≠ 0 := by
  exact (eval_primitiveCharpoly_separable b a f hD).eval₂_derivative_ne_zero (RingHom.id K) hy

end EtaleChart

end WideE
