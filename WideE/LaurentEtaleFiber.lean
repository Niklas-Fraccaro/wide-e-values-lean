import WideE.ComponentPullback
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Etale.Field

/-! Finite étale fibers and their evaluation at rational points. -/

open scoped TensorProduct

noncomputable section

namespace WideE

universe u

section Split

variable {K B : Type u} [Field K] [IsAlgClosed K] [CommRing B] [Algebra K B]

private theorem exists_etaleProduct [Algebra.Etale K B] :
    ∃ (ι : Type u), Finite ι ∧ Nonempty (B ≃ₐ[K] (ι → K)) := by
  obtain ⟨ι, hFinite, C, hField, hAlgebra, e, h⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K B).mp inferInstance
  let e₁ (i : ι) : K ≃ₐ[K] C i := by
    letI := (h i).1
    exact AlgEquiv.ofBijective (Algebra.ofId K (C i))
      IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact ⟨ι, hFinite, ⟨e.trans (AlgEquiv.piCongrRight fun i => (e₁ i).symm)⟩⟩

omit [IsAlgClosed K] in
private theorem piPoints_bijective {ι : Type u} [Finite ι] (e : B ≃ₐ[K] (ι → K)) :
    Function.Bijective
      (fun i => (Pi.evalAlgHom K (fun _ : ι => K) i).comp e.toAlgHom) := by
  classical
  constructor
  · intro i j h
    by_contra hij
    have he := DFunLike.congr_fun h (e.symm (Pi.single i 1))
    change e (e.symm (Pi.single i 1)) i = e (e.symm (Pi.single i 1)) j at he
    rw [e.apply_symm_apply] at he
    simp [Pi.single_apply, Ne.symm hij] at he
  · intro p
    obtain ⟨i, hi⟩ := (p.comp e.symm.toAlgHom).eq_piEvalAlgHom
    refine ⟨i, ?_⟩
    apply AlgHom.ext
    intro x
    have h := DFunLike.congr_fun hi (e x)
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_algHom, e.symm_apply_apply] using h.symm

/-- A finite étale algebra over an algebraically closed field has finitely many points. -/
theorem finite_etalePoints [Algebra.Etale K B] : Finite (B →ₐ[K] K) := by
  obtain ⟨ι, hi, ⟨e⟩⟩ := exists_etaleProduct (K := K) (B := B)
  exact Finite.of_surjective _ (piPoints_bijective e).2

/-- Simultaneous evaluation is the canonical splitting of a finite étale algebra
over an algebraically closed field. -/
def etalePointProductEquiv [Algebra.Etale K B] : B ≃ₐ[K] ((B →ₐ[K] K) → K) :=
  AlgEquiv.ofBijective (Pi.algHom K (fun _ : B →ₐ[K] K => K) id) (by
    obtain ⟨ι, hi, ⟨e⟩⟩ := exists_etaleProduct (K := K) (B := B)
    let p (i : ι) := (Pi.evalAlgHom K (fun _ : ι => K) i).comp e.toAlgHom
    have hp : Function.Bijective p := piPoints_bijective e
    constructor
    · intro x y h
      apply e.injective
      funext i
      exact congrFun h (p i)
    · intro v
      refine ⟨e.symm (v ∘ p), ?_⟩
      funext x
      obtain ⟨i, rfl⟩ := hp.2 x
      change e (e.symm (v ∘ p)) i = v (p i)
      rw [e.apply_symm_apply]
      rfl)

@[simp] theorem etalePointProductEquiv_apply [Algebra.Etale K B] (x : B) (p : B →ₐ[K] K) :
    etalePointProductEquiv x p = p x := rfl

end Split

section Evaluation

variable {K R : Type u} [CommRing K] [CommRing R] [Algebra K R]
variable (A : Type u) [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower K R A]
variable (f : R →ₐ[K] K)

/-- Algebra maps on a specified fiber, represented as maps on the covering algebra. -/
def EvaluationFiberPoint := {p : A →ₐ[K] K // p.comp (IsScalarTower.toAlgHom K R A) = f}

/-- The fiber of an algebra above the evaluation map. -/
abbrev EvaluationFiber :=
  letI := f.toRingHom.toAlgebra
  K ⊗[R] A

/-- The map from the covering algebra to the specified fiber. -/
def evaluationFiberClass : A →ₐ[K] EvaluationFiber A f := by
  letI := f.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom f
  exact (Algebra.TensorProduct.includeRight : A →ₐ[R] EvaluationFiber A f).restrictScalars K

@[simp] theorem evaluationFiberClass_apply (a : A) :
    letI := f.toRingHom.toAlgebra
    evaluationFiberClass A f a = (1 : K) ⊗ₜ[R] a := rfl

theorem evaluationFiberClass_surjective :
    Function.Surjective (evaluationFiberClass A f) := by
  letI := f.toRingHom.toAlgebra
  exact Algebra.TensorProduct.includeRight_surjective A fun a => ⟨algebraMap K R a, f.commutes a⟩

/-- A point of the tensor fiber corresponds to a point of the covering algebra
with the prescribed restriction to the base. -/
def evaluationFiberPointsEquiv : (EvaluationFiber A f →ₐ[K] K) ≃ EvaluationFiberPoint A f := by
  letI := f.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom f
  refine (componentSections R K A).trans ?_
  exact
    { toFun := fun p => ⟨p.restrictScalars K, AlgHom.ext fun r => p.commutes r⟩
      invFun := fun p => { p.val.toRingHom with
        commutes' := fun r => DFunLike.congr_fun p.property r }
      left_inv := fun p => rfl
      right_inv := by intro p; exact Subtype.ext rfl }

@[simp] theorem evaluationFiberPointsEquiv_apply (p : EvaluationFiber A f →ₐ[K] K) (a : A) :
    (evaluationFiberPointsEquiv A f p).val a = p (evaluationFiberClass A f a) := rfl

end Evaluation

section Fiber

variable {K R : Type u} [Field K] [IsAlgClosed K] [CommRing R] [Algebra K R]
variable (A : Type u) [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower K R A]
variable [Algebra.Etale R A] (f : R →ₐ[K] K)

omit [IsAlgClosed K] [Algebra K A] [IsScalarTower K R A] [Algebra.Etale R A] in
theorem evaluationFiber_finite [Module.Finite R A] : Module.Finite K (EvaluationFiber A f) := by
  letI := f.toRingHom.toAlgebra
  infer_instance

omit [IsAlgClosed K] [Algebra K A] [IsScalarTower K R A] in
theorem evaluationFiber_reduced : IsReduced (EvaluationFiber A f) := by
  letI := f.toRingHom.toAlgebra
  exact Algebra.FormallyUnramified.isReduced_of_field K (EvaluationFiber A f)

theorem finite_evaluationFiberPoint : Finite (EvaluationFiberPoint A f) := by
  letI := f.toRingHom.toAlgebra
  letI : Finite (EvaluationFiber A f →ₐ[K] K) := finite_etalePoints
  exact Finite.of_surjective _ (evaluationFiberPointsEquiv A f).surjective

/-- The fiber is a product of copies of the coefficient field, indexed by its points. -/
def evaluationFiberEquiv : EvaluationFiber A f ≃ₐ[K] (EvaluationFiberPoint A f → K) := by
  letI := f.toRingHom.toAlgebra
  let e := evaluationFiberPointsEquiv A f
  exact etalePointProductEquiv.trans
    { toFun := fun v p => v (e.symm p)
      invFun := fun v p => v (e p)
      left_inv := by
        intro v
        funext p
        exact congrArg v (e.symm_apply_apply p)
      right_inv := by
        intro v
        funext p
        exact congrArg v (e.apply_symm_apply p)
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }

@[simp] theorem evaluationFiberEquiv_class (a : A) (p : EvaluationFiberPoint A f) :
    evaluationFiberEquiv A f (evaluationFiberClass A f a) p = p.val a := by
  change (evaluationFiberPointsEquiv A f).symm p (evaluationFiberClass A f a) = p.val a
  rw [← evaluationFiberPointsEquiv_apply, Equiv.apply_symm_apply]

/-- A single global element separates all points of this fiber over an infinite field. -/
theorem exists_separating_evaluationFiber_element [Infinite K] :
    ∃ a : A, Function.Injective (fun p : EvaluationFiberPoint A f => p.val a) := by
  letI := finite_evaluationFiberPoint A f
  classical
  letI := Fintype.ofFinite (EvaluationFiberPoint A f)
  let v : EvaluationFiberPoint A f → K :=
    (Infinite.natEmbedding K) ∘ Fin.val ∘ Fintype.equivFin (EvaluationFiberPoint A f)
  obtain ⟨a, ha⟩ := evaluationFiberClass_surjective A f ((evaluationFiberEquiv A f).symm v)
  refine ⟨a, ?_⟩
  have hv (p : EvaluationFiberPoint A f) : p.val a = v p := by
    rw [← evaluationFiberEquiv_class, ha, AlgEquiv.apply_symm_apply]
  intro p q h
  change p.val a = q.val a at h
  rw [hv p, hv q] at h
  exact (Infinite.natEmbedding K).injective.comp (Fin.val_injective.comp
    (Fintype.equivFin (EvaluationFiberPoint A f)).injective) h

end Fiber

section Laurent

open LaurentPolynomial

variable {K : Type u} [CommRing K]

/-- Evaluate the Laurent variable at a nonzero point. -/
def laurentEvalAlg (z : Kˣ) : LaurentPolynomial K →ₐ[K] K where
  __ := LaurentPolynomial.eval₂ (RingHom.id K) z
  commutes' c := LaurentPolynomial.eval₂_C _ _ c

@[simp] theorem laurentEvalAlg_T (z : Kˣ) (n : ℤ) :
    laurentEvalAlg z (T n) = (z ^ n).val :=
  LaurentPolynomial.eval₂_T _ _ _

@[simp] theorem laurentEvalAlg_C (z : Kˣ) (c : K) : laurentEvalAlg z (C c) = c :=
  (laurentEvalAlg z).commutes c

variable (A : Type u) [CommRing A] [Algebra K A] [Algebra (LaurentPolynomial K) A]
  [IsScalarTower K (LaurentPolynomial K) A]

/-- The fiber points of a Laurent algebra at the nonzero argument. -/
abbrev LaurentFiberPoint (z : Kˣ) := EvaluationFiberPoint A (laurentEvalAlg z)

end Laurent

section LaurentEtale

variable {K : Type u} [Field K] [IsAlgClosed K]
variable (A : Type u) [CommRing A] [Algebra K A] [Algebra (LaurentPolynomial K) A]
  [IsScalarTower K (LaurentPolynomial K) A]
  [Algebra.Etale (LaurentPolynomial K) A]

theorem finite_laurentFiberPoint (z : Kˣ) : Finite (LaurentFiberPoint A z) :=
  finite_evaluationFiberPoint A (laurentEvalAlg z)

/-- The Laurent fiber is split by evaluation at all of its points. -/
abbrev laurentEtaleFiberEquiv (z : Kˣ) :=
  evaluationFiberEquiv A (laurentEvalAlg z)

theorem exists_separating_laurentFiber_element (z : Kˣ) :
    ∃ a : A, Function.Injective (fun p : LaurentFiberPoint A z => p.val a) :=
  exists_separating_evaluationFiber_element A (laurentEvalAlg z)

end LaurentEtale

end WideE
