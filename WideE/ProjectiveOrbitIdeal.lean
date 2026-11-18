import WideE.ProjectiveOrbitPoint
import Mathlib.RingTheory.Polynomial.Basic

/-! The homogeneous ideal of the closure of the affine cone on a projective orbit. -/

open scoped TensorProduct Matrix

noncomputable section

namespace WideE

set_option maxHeartbeats 1700000
set_option synthInstance.maxHeartbeats 100000

section FlatKernel

variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Module.Flat R S]

/-- Flat scalar extension carries an algebra homomorphism's kernel ideal to
its base-changed kernel. -/
theorem kernel_tensor_map_of_flat (f : A →ₐ[R] B) :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R S) f) =
      (RingHom.ker f).map (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) := by
  rw [← Submodule.restrictScalars_inj R]
  rw [Ideal.map_includeRight_eq]
  ext x
  change x ∈ LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor S S f.toLinearMap) ↔
    x ∈ LinearMap.range ((Submodule.subtype ((RingHom.ker f).restrictScalars R)).lTensor S)
  rw [Module.Flat.ker_lTensor_eq S S f.toLinearMap]
  rfl

end FlatKernel

section Cone

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k H ι : Type*} [CommRing k] [CommRing H] [Algebra k H] [Fintype ι]

/-- The vector obtained by applying the universal matrix to the original vector. -/
def orbitVector (U : Matrix ι ι H) (v : ι → k) : ι → H := U *ᵥ (algebraMap k H ∘ v)

/-- Evaluate on the universal orbit vector multiplied by a polynomial parameter. -/
def orbitConeEvaluation (U : Matrix ι ι H) (v : ι → k) : MvPolynomial ι k →ₐ[k] Polynomial H :=
  MvPolynomial.aeval (fun i => Polynomial.C (orbitVector U v i) * Polynomial.X)

@[simp] theorem orbitConeEvaluation_X (U : Matrix ι ι H) (v : ι → k) (i : ι) :
    orbitConeEvaluation U v (MvPolynomial.X i) = Polynomial.C (orbitVector U v i) * Polynomial.X :=
  MvPolynomial.aeval_X _ _

/-- The ideal of the orbit cone is the kernel of the universal orbit evaluation. -/
def orbitConeIdeal (U : Matrix ι ι H) (v : ι → k) : Ideal (MvPolynomial ι k) :=
  RingHom.ker (orbitConeEvaluation U v).toRingHom

theorem orbitConeEvaluation_homogeneous (U : Matrix ι ι H) (v : ι → k)
    {p : MvPolynomial ι k} {d : ℕ} (hp : p.IsHomogeneous d) :
    orbitConeEvaluation U v p = Polynomial.C (p.eval₂ (algebraMap k H) (orbitVector U v)) * Polynomial.X ^ d := by
  change p.eval₂ (algebraMap k (Polynomial H))
    (fun i => Polynomial.C (orbitVector U v i) * Polynomial.X) = _
  have hcoeff : algebraMap k (Polynomial H) = Polynomial.C.comp (algebraMap k H) :=
    IsScalarTower.algebraMap_eq k H (Polynomial H)
  rw [hcoeff, show (fun i => Polynomial.C (orbitVector U v i) * Polynomial.X) =
    fun i => Polynomial.X * (Polynomial.C ∘ orbitVector U v) i from funext fun _ => mul_comm _ _,
    homogeneous_eval₂_scale _ _ hp, ← MvPolynomial.eval₂_comp_left, mul_comm]

/-- The orbit cone ideal is homogeneous because its degree pieces map to
separate coefficients of the cone parameter. -/
theorem orbitConeIdeal_isHomogeneous (U : Matrix ι ι H) (v : ι → k) :
    (orbitConeIdeal U v).IsHomogeneous (MvPolynomial.homogeneousSubmodule ι k) := by
  apply (Ideal.isHomogeneous_iff_forall_subset _ _).mpr
  intro d p hp
  have hp₀ : orbitConeEvaluation U v p = 0 := RingHom.mem_ker.mp hp
  have hProj : GradedRing.proj (MvPolynomial.homogeneousSubmodule ι k) d p =
      MvPolynomial.homogeneousComponent d p := by
    rw [GradedRing.proj_apply]
    exact MvPolynomial.decomposition.decompose'_apply p d
  change GradedRing.proj (MvPolynomial.homogeneousSubmodule ι k) d p ∈ orbitConeIdeal U v
  rw [hProj]
  apply RingHom.mem_ker.mpr
  change orbitConeEvaluation U v (MvPolynomial.homogeneousComponent d p) = 0
  by_cases hd : d ≤ p.totalDegree
  · have hsum : ∑ j ∈ Finset.range (p.totalDegree + 1),
        orbitConeEvaluation U v (MvPolynomial.homogeneousComponent j p) = 0 := by
      rw [← map_sum, MvPolynomial.sum_homogeneousComponent, hp₀]
    have h := congrArg (fun q : Polynomial H => q.coeff d) hsum
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_zero,
      orbitConeEvaluation_homogeneous U v (MvPolynomial.homogeneousComponent_isHomogeneous _ _),
      Polynomial.coeff_C_mul_X_pow] at h
    rw [Finset.sum_eq_single d] at h
    · simp only [if_true] at h
      rw [orbitConeEvaluation_homogeneous U v (MvPolynomial.homogeneousComponent_isHomogeneous _ _),
        h, Polynomial.C_0, zero_mul]
    · intro j _ hj
      rw [if_neg (Ne.symm hj)]
    · intro hmissing
      exact False.elim (hmissing (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hd)))
  · rw [MvPolynomial.homogeneousComponent_eq_zero d p (Nat.lt_of_not_ge hd), map_zero]

end Cone

section ConeBaseChange

variable {k H ι : Type*} [Field k] [CommRing H] [Algebra k H] [Fintype ι]

local notation "P" => Polynomial H
local notation "A" => H ⊗[k] Polynomial H

private def orbitConeEvaluationOver (U : Matrix ι ι H) (v : ι → k) :
    MvPolynomial ι H →+* A :=
  (Algebra.TensorProduct.map (AlgHom.id k H) (orbitConeEvaluation U v)).toRingHom.comp
    (MvPolynomial.algebraTensorAlgEquiv (σ := ι) k H).symm.toRingHom

private theorem orbitConeEvaluationOver_C (U : Matrix ι ι H) (v : ι → k) (c : H) :
    orbitConeEvaluationOver U v (MvPolynomial.C c) = c ⊗ₜ[k] (1 : P) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := ι) k H
  have h : e (c ⊗ₜ[k] (1 : MvPolynomial ι k)) = MvPolynomial.C c := by
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, map_one, Algebra.smul_def, mul_one]
    rfl
  change (Algebra.TensorProduct.map (AlgHom.id k H) (orbitConeEvaluation U v)) (e.symm _) = _
  rw [← h, AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

private theorem orbitConeEvaluationOver_X (U : Matrix ι ι H) (v : ι → k) (i : ι) :
    orbitConeEvaluationOver U v (MvPolynomial.X i) =
      (1 : H) ⊗ₜ[k] (Polynomial.C (orbitVector U v i) * Polynomial.X) := by
  change (Algebra.TensorProduct.map (AlgHom.id k H) (orbitConeEvaluation U v))
    ((MvPolynomial.algebraTensorAlgEquiv k H).symm (MvPolynomial.X i)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_symm_X, Algebra.TensorProduct.map_tmul, map_one,
    orbitConeEvaluation_X]

private theorem orbitConeIdeal_baseChange (U : Matrix ι ι H) (v : ι → k) :
    scalarExtendedPolynomialIdeal H (orbitConeIdeal U v) = RingHom.ker (orbitConeEvaluationOver U v) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := ι) k H
  let inc : MvPolynomial ι k →ₐ[k] H ⊗[k] MvPolynomial ι k := Algebra.TensorProduct.includeRight
  have hBase : e.toRingHom.comp inc.toRingHom = MvPolynomial.map (algebraMap k H) := by
    apply RingHom.ext
    intro p
    change e ((1 : H) ⊗ₜ[k] p) = _
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  change (orbitConeIdeal U v).map (MvPolynomial.map (algebraMap k H)) = _
  rw [← hBase, ← Ideal.map_map]
  change ((RingHom.ker (orbitConeEvaluation U v).toRingHom).map inc).map e.toRingHom = _
  have hKer := kernel_tensor_map_of_flat (S := H) (orbitConeEvaluation U v)
  change RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k H) (orbitConeEvaluation U v)).toRingHom =
    (RingHom.ker (orbitConeEvaluation U v).toRingHom).map inc at hKer
  rw [← hKer]
  exact Ideal.map_comap_of_equiv e.toRingEquiv

end ConeBaseChange

section ConeInvariance

variable {k H ι : Type*} [Field k] [CommRing H] [Bialgebra k H] [Fintype ι]

local notation "P" => Polynomial H
local notation "A" => H ⊗[k] Polynomial H
local notation "iL" => (Algebra.TensorProduct.includeLeft : H →ₐ[k] A)
local notation "iP" => (Algebra.TensorProduct.includeRight : P →ₐ[k] A)
local notation "t" => ((1 : H) ⊗ₜ[k] (Polynomial.X : P))

private def polynomialCoefficient : H →ₐ[k] P := IsScalarTower.toAlgHom k H P

private def coneRightCoefficient : H →ₐ[k] A :=
  (iP).comp (polynomialCoefficient (k := k) (H := H))

/-- Apply the group comultiplication to the coefficients of the cone. -/
private def coneCoefficientComul : H →ₐ[k] A :=
  (Algebra.TensorProduct.map (AlgHom.id k H) (polynomialCoefficient (k := k) (H := H))).comp
    (Bialgebra.comulAlgHom k H)

private def conePolynomialComul : P →+* A :=
  Polynomial.eval₂RingHom (coneCoefficientComul (k := k) (H := H)).toRingHom t

private theorem coneComul_matrix (U : Matrix ι ι H)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U i j) = ∑ l, U i l ⊗ₜ[k] U l j) :
    U.map (coneCoefficientComul (k := k) (H := H)).toRingHom =
      U.map (iL).toRingHom * U.map (coneRightCoefficient (k := k) (H := H)).toRingHom := by
  apply Matrix.ext
  intro i j
  change (Algebra.TensorProduct.map (AlgHom.id k H) (polynomialCoefficient (k := k) (H := H)))
      (Coalgebra.comul (R := k) (U i j)) =
    ∑ l, ((U i l) ⊗ₜ[k] (1 : P)) * ((1 : H) ⊗ₜ[k] Polynomial.C (U l j))
  rw [hU, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    AlgHom.id_apply]
  rfl

private theorem coneComul_vector (U : Matrix ι ι H)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U i j) = ∑ l, U i l ⊗ₜ[k] U l j) (v : ι → k) :
    coneCoefficientComul ∘ orbitVector U v =
      U.map (iL).toRingHom *ᵥ (coneRightCoefficient ∘ orbitVector U v) := by
  let δ : H →ₐ[k] A := coneCoefficientComul
  let ιR : H →ₐ[k] A := coneRightCoefficient
  let x := algebraMap k H ∘ v
  have hδ : δ.toRingHom ∘ x = ιR.toRingHom ∘ x := by
    funext i
    exact (δ.commutes (v i)).trans (ιR.commutes (v i)).symm
  have hR : ιR.toRingHom ∘ (U *ᵥ x) = U.map ιR.toRingHom *ᵥ (ιR.toRingHom ∘ x) :=
    funext (RingHom.map_mulVec ιR.toRingHom U x)
  change δ.toRingHom ∘ (U *ᵥ x) = U.map (iL).toRingHom *ᵥ (ιR.toRingHom ∘ (U *ᵥ x))
  have h := funext (RingHom.map_mulVec δ.toRingHom U x)
  rw [show U.map δ.toRingHom = _ from coneComul_matrix U hU, hδ, ← Matrix.mulVec_mulVec, ← hR] at h
  exact h

private theorem orbitConeEvaluationOver_substitution (U : Matrix ι ι H)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U i j) = ∑ l, U i l ⊗ₜ[k] U l j) (v : ι → k) :
    ((orbitConeEvaluationOver U v).comp (matrixPolynomialSubstitution U).toRingHom).comp
      (MvPolynomial.map (algebraMap k H)) =
    (conePolynomialComul (k := k)).comp (orbitConeEvaluation U v).toRingHom := by
  let ev := orbitConeEvaluationOver U v
  let δ : H →ₐ[k] A := coneCoefficientComul
  let φ : P →+* A := conePolynomialComul
  let ιR : H →ₐ[k] A := coneRightCoefficient
  apply MvPolynomial.ringHom_ext
  · intro c
    change ev (matrixPolynomialSubstitution U (MvPolynomial.map (algebraMap k H) (MvPolynomial.C c))) =
      φ (orbitConeEvaluation U v (MvPolynomial.C c))
    rw [MvPolynomial.map_C, matrixPolynomialSubstitution_C]
    have hc : orbitConeEvaluation U v (MvPolynomial.C c) = Polynomial.C (algebraMap k H c) := by
      change orbitConeEvaluation U v (algebraMap k _ c) = _
      rw [AlgHom.commutes, IsScalarTower.algebraMap_eq k H (Polynomial H)]
      rfl
    rw [hc, show ev _ = _ from orbitConeEvaluationOver_C U v (algebraMap k H c)]
    change iL (algebraMap k H c) = Polynomial.eval₂ δ.toRingHom t
      (Polynomial.C (algebraMap k H c))
    rw [Polynomial.eval₂_C]
    exact ((iL).commutes c).trans (δ.commutes c).symm
  · intro i
    change ev (matrixPolynomialSubstitution U (MvPolynomial.map (algebraMap k H) (MvPolynomial.X i))) =
      φ (orbitConeEvaluation U v (MvPolynomial.X i))
    rw [MvPolynomial.map_X, matrixPolynomialSubstitution_X, orbitConeEvaluation_X, RingHom.map_mulVec]
    have hConst : (U.map (MvPolynomial.C : H →+* MvPolynomial ι H)).map ev = U.map (iL).toRingHom :=
      Matrix.ext fun i j => orbitConeEvaluationOver_C U v (U i j)
    have hVar : ev ∘ MvPolynomial.X = t • (ιR.toRingHom ∘ orbitVector U v) := by
      funext j
      change ev (MvPolynomial.X j) = t * ((1 : H) ⊗ₜ[k] Polynomial.C (orbitVector U v j))
      rw [show ev (MvPolynomial.X j) = _ from orbitConeEvaluationOver_X U v j,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm (Polynomial.X : P)]
    have hVec : U.map (iL).toRingHom *ᵥ (ιR.toRingHom ∘ orbitVector U v) =
        δ.toRingHom ∘ orbitVector U v := (coneComul_vector U hU v).symm
    rw [hConst, hVar, Matrix.mulVec_smul, hVec]
    change t * δ (orbitVector U v i) = φ (Polynomial.C (orbitVector U v i) * Polynomial.X)
    rw [map_mul]
    change t * δ (orbitVector U v i) =
      Polynomial.eval₂ δ.toRingHom t (Polynomial.C (orbitVector U v i)) *
        Polynomial.eval₂ δ.toRingHom t Polynomial.X
    rw [Polynomial.eval₂_C, Polynomial.eval₂_X, mul_comm]
    rfl

/-- The universal matrix carries the base extension of the cone ideal into itself. -/
theorem orbitConeIdeal_map_le (U : Matrix ι ι H)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U i j) = ∑ l, U i l ⊗ₜ[k] U l j) (v : ι → k) :
    (scalarExtendedPolynomialIdeal H (orbitConeIdeal U v)).map (matrixPolynomialSubstitution U).toRingHom ≤
      scalarExtendedPolynomialIdeal H (orbitConeIdeal U v) := by
  calc
    _ = (orbitConeIdeal U v).map ((matrixPolynomialSubstitution U).toRingHom.comp
          (MvPolynomial.map (algebraMap k H))) := Ideal.map_map _ _
    _ ≤ RingHom.ker (orbitConeEvaluationOver U v) := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro p hp
      change orbitConeEvaluationOver U v
        (matrixPolynomialSubstitution U (MvPolynomial.map (algebraMap k H) p)) = 0
      have h : orbitConeEvaluationOver U v
          (matrixPolynomialSubstitution U (MvPolynomial.map (algebraMap k H) p)) =
        conePolynomialComul (orbitConeEvaluation U v p) :=
        DFunLike.congr_fun (orbitConeEvaluationOver_substitution U hU v) p
      rw [h, show orbitConeEvaluation U v p = 0 from RingHom.mem_ker.mp hp, map_zero]
    _ = _ := (orbitConeIdeal_baseChange U v).symm

end ConeInvariance

section Noetherian

private theorem ideal_eq_of_map_le_of_noetherian {A : Type*} [CommRing A] [IsNoetherianRing A]
    (e : A ≃+* A) (I : Ideal A) (h : I.map e.toRingHom ≤ I) : I.map e.toRingHom = I := by
  let f : Ideal A → Ideal A := Ideal.map e.symm.toRingHom
  have hleft : e.symm.toRingHom.comp e.toRingHom = RingHom.id A :=
    RingHom.ext e.symm_apply_apply
  have hright : e.toRingHom.comp e.symm.toRingHom = RingHom.id A :=
    RingHom.ext e.apply_symm_apply
  have hinitial : I ≤ f I := by
    have h' := Ideal.map_mono (f := e.symm.toRingHom) h
    rwa [Ideal.map_map, hleft, Ideal.map_id] at h'
  have hmono : Monotone f := fun _ _ => Ideal.map_mono
  have hinj : Function.Injective f := (Ideal.relIsoOfBijective e.symm.toRingHom e.symm.bijective).symm.injective
  let F : ℕ →o Ideal A := ⟨fun n => f^[n] I, monotone_nat_of_le_succ fun n => by
    rw [Function.iterate_succ_apply]
    exact (hmono.iterate n) hinitial⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian A A) F
  have hEq := hn n.succ (Nat.le_succ n)
  change f^[n] I = f^[n.succ] I at hEq
  rw [Function.iterate_succ_apply] at hEq
  have hI : I = f I := (hinj.iterate n) hEq
  have h' := congrArg (Ideal.map e.toRingHom) hI
  change I.map e.toRingHom = (I.map e.symm.toRingHom).map e.toRingHom at h'
  rwa [Ideal.map_map, hright, Ideal.map_id] at h'

end Noetherian

section Invariance

variable {k H ι : Type*} [Field k] [CommRing H] [Bialgebra k H]
  [Fintype ι] [DecidableEq ι]

private theorem matrixPolynomialSubstitution_one :
    matrixPolynomialSubstitution (1 : Matrix ι ι H) = AlgHom.id H (MvPolynomial ι H) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [matrixPolynomialSubstitution_X, Matrix.map_one _ (map_zero MvPolynomial.C) (map_one MvPolynomial.C),
    Matrix.one_mulVec, AlgHom.id_apply]

private def matrixPolynomialAutomorphism (U : (Matrix ι ι H)ˣ) :
    MvPolynomial ι H ≃ₐ[H] MvPolynomial ι H :=
  AlgEquiv.ofAlgHom (matrixPolynomialSubstitution U.val) (matrixPolynomialSubstitution (U⁻¹).val)
    (by rw [← matrixPolynomialSubstitution_mul, Units.inv_mul, matrixPolynomialSubstitution_one])
    (by rw [← matrixPolynomialSubstitution_mul, Units.mul_inv, matrixPolynomialSubstitution_one])

/-- The homogeneous orbit cone ideal is invariant under the universal
invertible group matrix, over the group coordinate ring itself. -/
theorem orbitConeIdeal_invariant [IsNoetherianRing H] (U : (Matrix ι ι H)ˣ)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (v : ι → k) :
    (scalarExtendedPolynomialIdeal H (orbitConeIdeal U.val v)).map
        (matrixPolynomialSubstitution U.val).toRingHom =
      scalarExtendedPolynomialIdeal H (orbitConeIdeal U.val v) := by
  exact ideal_eq_of_map_le_of_noetherian (matrixPolynomialAutomorphism U).toRingEquiv _
    (orbitConeIdeal_map_le U.val hU v)

end Invariance

section BasePoint

variable {k H ι : Type*} [Field k] [CommRing H] [Bialgebra k H] [Fintype ι] [DecidableEq ι]

/-- The identity group point evaluates the cone at its defining vector. -/
theorem orbitConeIdeal_vanishes_at_vector (U : Matrix ι ι H)
    (hOne : U.map (Bialgebra.counitAlgHom k H).toRingHom = 1) (v : ι → k)
    {p : MvPolynomial ι k} (hp : p ∈ orbitConeIdeal U v) : p.eval v = 0 := by
  let ε := Bialgebra.counitAlgHom k H
  let e := Polynomial.eval₂RingHom ε.toRingHom (1 : k)
  have h : e.comp (orbitConeEvaluation U v).toRingHom = MvPolynomial.eval v := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change e (orbitConeEvaluation U v (algebraMap k _ a)) = MvPolynomial.eval v (MvPolynomial.C a)
      rw [AlgHom.commutes, IsScalarTower.algebraMap_eq k H (Polynomial H), RingHom.comp_apply,
        MvPolynomial.eval_C]
      change Polynomial.eval₂ ε.toRingHom 1 (Polynomial.C (algebraMap k H a)) = a
      rw [Polynomial.eval₂_C]
      exact ε.commutes a
    · intro i
      change e (orbitConeEvaluation U v (MvPolynomial.X i)) = MvPolynomial.eval v (MvPolynomial.X i)
      rw [orbitConeEvaluation_X, map_mul, MvPolynomial.eval_X]
      change Polynomial.eval₂ ε.toRingHom 1 (Polynomial.C (orbitVector U v i)) *
        Polynomial.eval₂ ε.toRingHom 1 Polynomial.X = v i
      rw [Polynomial.eval₂_C, Polynomial.eval₂_X, mul_one]
      have hvec := RingHom.map_mulVec ε.toRingHom U (algebraMap k H ∘ v) i
      change ε.toRingHom (orbitVector U v i) = (U.map ε.toRingHom *ᵥ
        (ε.toRingHom ∘ algebraMap k H ∘ v)) i at hvec
      rw [show U.map ε.toRingHom = 1 from hOne, Matrix.one_mulVec] at hvec
      exact hvec.trans (ε.commutes (v i))
  have he := DFunLike.congr_fun h p
  change e (orbitConeEvaluation U v p) = p.eval v at he
  rw [show orbitConeEvaluation U v p = 0 from RingHom.mem_ker.mp hp, map_zero] at he
  exact he.symm

end BasePoint

section TorsorCone

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k R S H F ι : Type*} [Field k] [CommRing R] [CommRing S] [CommRing H]
  [IsDomain R] [IsPrincipalIdealRing R] [Field F] [Algebra R F] [IsFractionRing R F]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
  [Algebra k F] [IsScalarTower k R F] [HopfAlgebra k H] [Fintype ι] [DecidableEq ι]

local notation "q₁" => (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S)
local notation "q₂" => (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S)

/-- For a generically pointed torsor, the twisted equations of the cone have
primitive coordinates over the base inducing the original orbit line at that point. -/
theorem AffineHopfTorsor.exists_primitiveOrbitConePoint (T : AffineHopfTorsor k R S H)
    (U : (Matrix ι ι H)ˣ)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hOne : U.val.map (Bialgebra.counitAlgHom k H).toRingHom = 1)
    (v : ι → k) (hv : v ≠ 0) (f : S →ₐ[R] F) :
    ∃ (g : (Matrix ι ι S)ˣ) (J : Ideal (MvPolynomial ι R)) (y : ι → R) (c : Fˣ),
      J.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι R) ∧
      J.map (MvPolynomial.map (algebraMap R S)) = twistedPolynomialIdeal (orbitConeIdeal U.val v) g.val ∧
      g.val.map (q₁).toRingHom = U.val.map T.overlapPoint.toRingHom * g.val.map (q₂).toRingHom ∧
      Ideal.span (Set.range y) = ⊤ ∧
      g.val.map f.toRingHom *ᵥ (algebraMap R F ∘ y) = (c : F) • (algebraMap k F ∘ v) ∧
      ∀ q ∈ J, q.eval y = 0 := by
  letI := T.group_finiteType
  letI : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  obtain ⟨g, J, hHom, hJ, hg⟩ := T.exists_twistedPolynomialIdeal U hU (orbitConeIdeal U.val v)
    (orbitConeIdeal_isHomogeneous U.val v) (orbitConeIdeal_invariant U hU v)
  obtain ⟨y, c, hPrimitive, hLine, hEq⟩ := exists_twistedPolynomialIdeal_primitivePoint
    (orbitConeIdeal U.val v) J g hHom hJ f v hv
    (fun _ hp => orbitConeIdeal_vanishes_at_vector U.val hOne v hp)
  exact ⟨g, J, y, c, hHom, hJ, hg, hPrimitive, hLine, hEq⟩

end TorsorCone

end WideE
