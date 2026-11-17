import WideE.Tsen
import Mathlib.RingTheory.Norm.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# The C₁ property and field extensions

For a form over a finite extension, choose coordinates in a basis, then take the
determinant of its multiplication matrix. The resulting form over the base has
both its number of variables and its degree multiplied by the extension degree.
-/

noncomputable section

open scoped BigOperators Matrix
open MvPolynomial

namespace WideE

section PolynomialNorm

variable {K L σ ι : Type*} [Field K] [Field L] [Algebra K L]

private def coefficientProjection (l : L →ₗ[K] K) (p : MvPolynomial σ L) : MvPolynomial σ K :=
  ∑ s ∈ p.support, monomial s (l (p.coeff s))

private theorem eval_coefficientProjection (l : L →ₗ[K] K) (p : MvPolynomial σ L) (x : σ → K) :
    eval x (coefficientProjection l p) = l (eval (algebraMap K L ∘ x) p) := by
  rw [coefficientProjection, map_sum, eval_eq (algebraMap K L ∘ x), map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [eval_monomial]
  have h : (∏ i ∈ s.support, (algebraMap K L ∘ x) i ^ s i) =
      algebraMap K L (∏ i ∈ s.support, x i ^ s i) := by
    simp only [Function.comp_apply, map_prod, map_pow]
  rw [h, mul_comm (p.coeff s), ← Algebra.smul_def, l.map_smul, smul_eq_mul, mul_comm]
  rfl

private theorem coefficientProjection_homogeneous (l : L →ₗ[K] K) {p : MvPolynomial σ L}
    {d : ℕ} (hp : p.IsHomogeneous d) : (coefficientProjection l p).IsHomogeneous d := by
  apply IsHomogeneous.sum
  intro s hs
  exact isHomogeneous_monomial _
    ((congrFun Finsupp.degree_eq_weight_one s).trans (hp (mem_support_iff.mp hs)))

variable [Fintype ι] [DecidableEq ι]

private def normCoefficientMatrix (b : Basis ι K L) (p : MvPolynomial σ L) :
    Matrix ι ι (MvPolynomial σ K) :=
  Matrix.of fun i j =>
    coefficientProjection ((Matrix.entryLinearMap K K i j).comp (Algebra.leftMulMatrix b).toLinearMap) p

/-- The determinant of multiplication by a polynomial, expressed over the base field. -/
def polynomialNorm (b : Basis ι K L) (p : MvPolynomial σ L) : MvPolynomial σ K :=
  (normCoefficientMatrix b p).det

theorem eval_polynomialNorm (b : Basis ι K L) (p : MvPolynomial σ L) (x : σ → K) :
    eval x (polynomialNorm b p) = Algebra.norm K (eval (algebraMap K L ∘ x) p) := by
  rw [polynomialNorm, RingHom.map_det, Algebra.norm_eq_matrix_det b]
  congr 1
  apply Matrix.ext
  intro i j
  exact eval_coefficientProjection
    ((Matrix.entryLinearMap K K i j).comp (Algebra.leftMulMatrix b).toLinearMap) p x

theorem polynomialNorm_isHomogeneous (b : Basis ι K L) {p : MvPolynomial σ L} {d : ℕ}
    (hp : p.IsHomogeneous d) : (polynomialNorm b p).IsHomogeneous (Fintype.card ι * d) := by
  rw [polynomialNorm, Matrix.det_apply']
  apply IsHomogeneous.sum
  intro π _
  have hprod : (∏ i, normCoefficientMatrix b p (π i) i).IsHomogeneous (Fintype.card ι * d) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      IsHomogeneous.prod Finset.univ (fun i => normCoefficientMatrix b p (π i) i)
        (fun _ => d) (fun i _ => coefficientProjection_homogeneous
          ((Matrix.entryLinearMap K K (π i) i).comp (Algebra.leftMulMatrix b).toLinearMap) hp)
  have hsign : ((Equiv.Perm.sign π : ℤ) : MvPolynomial σ K).IsHomogeneous 0 := by
    rw [← map_intCast (C : K →+* MvPolynomial σ K)]
    exact isHomogeneous_C _ _
  simpa only [zero_add] using hsign.mul hprod

end PolynomialNorm

section FieldExtensions

variable {K L σ ι : Type*} [Field K] [Field L] [Algebra K L] [Fintype ι]

private def basisCoordinateExpression (b : Basis ι K L) (j : ι → σ) : MvPolynomial σ L :=
  ∑ i, C (b i) * X (j i)

private theorem basisCoordinateExpression_homogeneous (b : Basis ι K L) (j : ι → σ) :
    (basisCoordinateExpression b j).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  simpa only [zero_add] using (isHomogeneous_C σ (b i)).mul (isHomogeneous_X L (j i))

private theorem eval_basisCoordinateExpression (b : Basis ι K L) (j : ι → σ) (x : σ → K) :
    eval (algebraMap K L ∘ x) (basisCoordinateExpression b j) = b.equivFun.symm (x ∘ j) := by
  rw [basisCoordinateExpression, map_sum, Basis.equivFun_symm_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_mul, eval_C, eval_X, Function.comp_apply, Algebra.smul_def, mul_comm]

omit [Algebra K L] in
private theorem eval₂_isHomogeneous_of_linear_forms {τ : Type*} {p : MvPolynomial τ L} {d : ℕ}
    (hp : p.IsHomogeneous d) {g : τ → MvPolynomial σ L}
    (hg : ∀ i, (g i).IsHomogeneous 1) : (eval₂ C g p).IsHomogeneous d := by
  rw [eval₂_eq]
  apply IsHomogeneous.sum
  intro s hs
  have hsd : s.degree = d :=
    (congrFun Finsupp.degree_eq_weight_one s).trans (hp (mem_support_iff.mp hs))
  have hm := IsHomogeneous.prod s.support (fun i => g i ^ s i) s
    (fun i _ => by simpa only [one_mul] using (hg i).pow (s i))
  change (∏ i ∈ s.support, g i ^ s i).IsHomogeneous s.degree at hm
  simpa only [zero_add, hsd] using (isHomogeneous_C σ (p.coeff s)).mul hm

/-- The C₁ property passes to a finite field extension by the polynomial norm. -/
theorem isC1_of_finiteDimensional [FiniteDimensional K L] (hK : IsC1 K) : IsC1 L := by
  classical
  intro r d p hp hd hdr
  let m := Module.finrank K L
  let b : Basis (Fin m) K L := Module.finBasis K L
  let e := finProdFinEquiv (m := r) (n := m)
  let g (i : Fin r) : MvPolynomial (Fin (r * m)) L :=
    basisCoordinateExpression b (fun j => e (i, j))
  let P := eval₂ C g p
  let N := polynomialNorm b P
  have hP : P.IsHomogeneous d :=
    eval₂_isHomogeneous_of_linear_forms hp (fun _ => basisCoordinateExpression_homogeneous b _)
  have hN : N.IsHomogeneous (m * d) := by
    simpa only [N, Fintype.card_fin] using polynomialNorm_isHomogeneous b hP
  have hm : 0 < m := Module.finrank_pos
  have hmd : m * d < r * m := by
    rw [Nat.mul_comm m d]
    exact Nat.mul_lt_mul_of_pos_right hdr hm
  obtain ⟨x, hx, hxN⟩ := hK N hN (Nat.mul_pos hm hd) hmd
  let y (i : Fin r) : L := b.equivFun.symm (fun j => x (e (i, j)))
  refine ⟨y, ?_, ?_⟩
  · intro hy
    apply hx
    funext l
    obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective l
    have h := congrArg (fun a : L => b.equivFun a j) (congrFun hy i)
    simpa only [y, LinearEquiv.apply_symm_apply, Pi.zero_apply, map_zero] using h
  · have hEval : eval (algebraMap K L ∘ x) P = eval y p := by
      dsimp only [P]
      rw [eval₂_comp_left]
      have hC : (eval (algebraMap K L ∘ x)).comp C = RingHom.id L :=
        RingHom.ext fun a => eval_C a
      rw [hC]
      have hVars : (eval (algebraMap K L ∘ x)) ∘ g = y := by
        funext i
        exact eval_basisCoordinateExpression b (fun j => e (i, j)) x
      rw [hVars]
      rfl
    have he := eval_polynomialNorm b P x
    rw [hEval] at he
    exact Algebra.norm_eq_zero_iff.mp (he.symm.trans hxN)

/-- Every norm from a finite extension of a C₁ field is surjective. -/
theorem norm_surjective_of_isC1 [FiniteDimensional K L] (hK : IsC1 K) :
    Function.Surjective (Algebra.norm K : L →* K) := by
  classical
  intro a
  let m := Module.finrank K L
  let b : Basis (Fin m) K L := Module.finBasis K L
  let P : MvPolynomial (Fin (m + 1)) L := basisCoordinateExpression b Fin.castSucc
  let N := polynomialNorm b P
  let Q := N - C a * X (Fin.last m) ^ m
  have hm : 0 < m := Module.finrank_pos
  have hN : N.IsHomogeneous m := by
    simpa only [N, Fintype.card_fin, mul_one] using
      polynomialNorm_isHomogeneous b (basisCoordinateExpression_homogeneous b Fin.castSucc)
  have hTail : (C a * X (Fin.last m) ^ m).IsHomogeneous m := by
    simpa only [zero_add, one_mul] using
      (isHomogeneous_C (Fin (m + 1)) a).mul ((isHomogeneous_X K (Fin.last m)).pow m)
  obtain ⟨x, hx, hxQ⟩ := hK Q (hN.sub hTail) hm (Nat.lt_succ_self m)
  let y : L := b.equivFun.symm (x ∘ Fin.castSucc)
  let z := x (Fin.last m)
  have hEval : (Algebra.norm K) y = a * z ^ m := by
    have h := eval_polynomialNorm b P x
    rw [eval_basisCoordinateExpression b Fin.castSucc x] at h
    change eval x N = (Algebra.norm K) y at h
    rw [← h]
    apply sub_eq_zero.mp
    simpa only [Q, map_sub, map_mul, eval_C, map_pow, eval_X, z] using hxQ
  have hz : z ≠ 0 := by
    intro hz
    have hny : (Algebra.norm K) y = 0 := by
      rw [hEval, hz, zero_pow (Nat.ne_of_gt hm), mul_zero]
    have hy : y = 0 := Algebra.norm_eq_zero_iff.mp hny
    apply hx
    funext j
    refine Fin.lastCases hz (fun l => ?_) j
    have h := congrArg (fun v : L => b.equivFun v l) hy
    simpa only [y, LinearEquiv.apply_symm_apply, map_zero, Pi.zero_apply, Function.comp_apply] using h
  refine ⟨algebraMap K L z⁻¹ * y, ?_⟩
  rw [map_mul, Algebra.norm_algebraMap, inv_pow, hEval]
  calc
    (z ^ m)⁻¹ * (a * z ^ m) = a * ((z ^ m)⁻¹ * z ^ m) := by ac_rfl
    _ = a := by rw [inv_mul_cancel₀ (pow_ne_zero m hz), mul_one]

/-- The norm is surjective on units for a finite extension of a C₁ field. -/
theorem units_norm_surjective_of_isC1 [FiniteDimensional K L] (hK : IsC1 K) :
    Function.Surjective (Units.map (Algebra.norm K : L →* K)) := by
  intro a
  obtain ⟨x, hx⟩ := norm_surjective_of_isC1 (L := L) hK (a : K)
  have hx₀ : x ≠ 0 := by
    intro h
    exact a.ne_zero (hx.symm.trans (Algebra.norm_eq_zero_iff.mpr h))
  exact ⟨Units.mk0 x hx₀, Units.ext hx⟩

end FieldExtensions

section AlgebraicExtension

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The C₁ property passes to any algebraic extension by adjoining the finitely many coefficients. -/
theorem isC1_of_isAlgebraic [Algebra.IsAlgebraic K L] (hK : IsC1 K) : IsC1 L := by
  classical
  intro r d p hp hd hdr
  let S : Finset L := p.support.image p.coeff
  let E := IntermediateField.adjoin K (S : Set L)
  letI : FiniteDimensional K E := IntermediateField.finiteDimensional_adjoin
    (K := K) (S := (S : Set L)) (fun a _ => Algebra.IsIntegral.isIntegral a)
  let c (s : p.support) : E :=
    ⟨p.coeff s.val, IntermediateField.subset_adjoin K (S : Set L)
      (Finset.mem_image_of_mem p.coeff s.property)⟩
  let q : MvPolynomial (Fin r) E := ∑ s ∈ p.support.attach, monomial s.val (c s)
  have hq : q.IsHomogeneous d := by
    apply IsHomogeneous.sum
    intro s _
    exact isHomogeneous_monomial _ ((congrFun Finsupp.degree_eq_weight_one s.val).trans
      (hp (mem_support_iff.mp s.property)))
  have hmap : map E.val.toRingHom q = p := by
    calc
      map E.val.toRingHom q = ∑ s ∈ p.support.attach, monomial s.val (p.coeff s.val) := by
        dsimp only [q]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro s _
        rw [map_monomial]
        rfl
      _ = ∑ s ∈ p.support, monomial s (p.coeff s) :=
        Finset.sum_attach p.support (fun s => monomial s (p.coeff s))
      _ = p := p.as_sum.symm
  obtain ⟨x, hx, hz⟩ := isC1_of_finiteDimensional (K := K) (L := E) hK q hq hd hdr
  refine ⟨E.val ∘ x, ?_, ?_⟩
  · intro h
    apply hx
    funext j
    apply E.val.injective
    simpa only [Function.comp_apply, Pi.zero_apply, map_zero] using congrFun h j
  · change eval (E.val.toRingHom ∘ x) p = 0
    rw [← hmap, eval_map, ← eval₂_comp, hz, map_zero]

end AlgebraicExtension

end WideE
