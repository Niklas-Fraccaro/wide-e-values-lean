import WideE.Laurent
import DifferentialQuotientConnection
import FiniteDifferentialProjectivity
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! Module operations and the algebraic fiber at one in §§4–5. -/

noncomputable section

namespace WideE

open scoped TensorProduct
open LaurentPolynomial

section Modules

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

theorem finite_span {ι : Type*} [Finite ι] (generators : ι → M) :
    Module.Finite R (Submodule.span R (Set.range generators)) :=
  Module.Finite.span_of_finite R (Set.finite_range generators)

/-- A connection preserves the span of a family if it sends each generator into the span. -/
theorem derivation_mem_span (δ : R →+ R) (D : M →+ M)
    (leibniz : ∀ (r : R) (x : M), D (r • x) = δ r • x + r • D x)
    {s : Set M} (hS : ∀ x ∈ s, D x ∈ Submodule.span R s)
    {x : M} (hx : x ∈ Submodule.span R s) :
    D x ∈ Submodule.span R s := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x hx hDx =>
    rw [leibniz]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx) (Submodule.smul_mem _ _ hDx)

private theorem freeOfFiniteProjective [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Finite R M] [Module.Projective R M] : Module.Free R M := by
  obtain ⟨s, hs⟩ := Module.projective_def.mp (inferInstance : Module.Projective R M)
  letI : NoZeroSMulDivisors R M := ⟨by
    intro r x h
    have hsmul : r • s x = 0 := by rw [← s.map_smul, h, s.map_zero]
    exact (smul_eq_zero.mp hsmul).imp_right (fun hx => hs.injective (hx.trans s.map_zero.symm))⟩
  infer_instance

/-- A relation whose difference is a multiple of the defining ideal vanishes in the fiber. -/
theorem quotient_relation (I : Ideal R) {r : R} (hr : r ∈ I)
    {x y h : M} (hxy : x - y = r • h) :
    (I • (⊤ : Submodule R M)).mkQ x = (I • (⊤ : Submodule R M)).mkQ y := by
  apply sub_eq_zero.mp
  rw [← map_sub, hxy, ← LinearMap.mem_ker, Submodule.ker_mkQ]
  exact Submodule.smul_mem_smul hr Submodule.mem_top

open TensorProduct.AlgebraTensorModule in
/-- Scalar extension of a module multiplication map, allowing a separate target module. -/
def baseChangeMul (A : Type*) [CommRing A] [Algebra R A]
    (μ : M ⊗[R] M →ₗ[R] N) : (A ⊗[R] M) ⊗[A] (A ⊗[R] M) →ₗ[A] A ⊗[R] N :=
  (lTensor A A μ).comp <|
    (congr (TensorProduct.lid A A) (LinearEquiv.refl R (M ⊗[R] M))).toLinearMap.comp
      (tensorTensorTensorComm R A A M A M).toLinearMap

@[simp] theorem baseChangeMul_tmul (A : Type*) [CommRing A] [Algebra R A]
    (μ : M ⊗[R] M →ₗ[R] N) (a b : A) (m n : M) :
    baseChangeMul A μ ((a ⊗ₜ[R] m) ⊗ₜ[A] (b ⊗ₜ[R] n)) = (a * b) ⊗ₜ[R] μ (m ⊗ₜ[R] n) := by
  simp [baseChangeMul, smul_eq_mul]

end Modules

section Fiber

variable (K : Type*) [CommRing K]

/-- The fiber is taken using the scalar algebra given by evaluation at one. -/
scoped instance laurentEvaluationAlgebra : Algebra (LaurentPolynomial K) K :=
  (evalAtOne K).toAlgebra

@[simp] theorem laurentEvaluation_algebraMap :
    algebraMap (LaurentPolynomial K) K = evalAtOne K :=
  rfl

scoped instance laurentEvaluationTower : IsScalarTower K (LaurentPolynomial K) K :=
  IsScalarTower.of_algebraMap_eq fun a => by
    change a = evalAtOne K (C a)
    exact (evalAtOne_C K a).symm

variable (M : Type*) [AddCommGroup M] [Module (LaurentPolynomial K) M]

/-- The algebraic fiber at (1), with scalars in the coefficient ring. -/
abbrev FiberAtOne := K ⊗[LaurentPolynomial K] M

/-- The distinguished image of an element in the algebraic fiber. -/
def fiberClass : M →ₗ[LaurentPolynomial K] FiberAtOne K M :=
  TensorProduct.mk (LaurentPolynomial K) K M 1

private def residueLinearEquiv :
    (LaurentPolynomial K ⧸ evaluationIdeal K) ≃ₗ[LaurentPolynomial K] K where
  toAddEquiv := (evaluationQuotientEquiv K).toAddEquiv
  map_smul' r x := by
    change evaluationQuotientEquiv K ((Ideal.Quotient.mk (evaluationIdeal K) r) * x) =
      evalAtOne K r * evaluationQuotientEquiv K x
    rw [map_mul, evaluationQuotientEquiv_mk]

/-- The tensor fiber is the module quotient by multiples of (T-1). -/
def fiberAtOneEquivQuotient :
    FiberAtOne K M ≃ₗ[LaurentPolynomial K]
      (M ⧸ (evaluationIdeal K • ⊤ : Submodule (LaurentPolynomial K) M)) :=
  (residueLinearEquiv K).symm.rTensor M ≪≫ₗ
    TensorProduct.quotTensorEquivQuotSMul M (evaluationIdeal K)

@[simp] theorem fiberAtOneEquivQuotient_class (m : M) :
    fiberAtOneEquivQuotient K M (fiberClass K M m) =
      (evaluationIdeal K • ⊤ : Submodule (LaurentPolynomial K) M).mkQ m := by
  have h : residueLinearEquiv K (Ideal.Quotient.mk (evaluationIdeal K) 1) = 1 := by
    change evaluationQuotientEquiv K (Ideal.Quotient.mk (evaluationIdeal K) 1) = 1
    rw [evaluationQuotientEquiv_mk, map_one]
  change TensorProduct.quotTensorEquivQuotSMul M (evaluationIdeal K)
    ((residueLinearEquiv K).symm 1 ⊗ₜ[LaurentPolynomial K] m) = _
  rw [← h, LinearEquiv.symm_apply_apply, TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
    one_smul, Submodule.mkQ_apply]

theorem fiberClass_relation {x y h : M} (hxy : x - y = (T 1 - 1 : LaurentPolynomial K) • h) :
    fiberClass K M x = fiberClass K M y := by
  apply (fiberAtOneEquivQuotient K M).injective
  rw [fiberAtOneEquivQuotient_class, fiberAtOneEquivQuotient_class]
  exact quotient_relation (evaluationIdeal K) (Ideal.subset_span (Set.mem_singleton _)) hxy

variable {M} {N : Type*} [AddCommGroup N] [Module (LaurentPolynomial K) N]

theorem fiberClass_mul (μ : M ⊗[LaurentPolynomial K] M →ₗ[LaurentPolynomial K] N) (x y : M) :
    baseChangeMul K μ (fiberClass K M x ⊗ₜ[K] fiberClass K M y) =
      fiberClass K N (μ (x ⊗ₜ[LaurentPolynomial K] y)) := by
  change baseChangeMul K μ ((1 ⊗ₜ[LaurentPolynomial K] x) ⊗ₜ[K]
    (1 ⊗ₜ[LaurentPolynomial K] y)) = 1 ⊗ₜ[LaurentPolynomial K] μ (x ⊗ₜ[LaurentPolynomial K] y)
  rw [baseChangeMul_tmul, one_mul]

/-- The map of algebraic fibers induced by a linear map on Laurent modules. -/
def fiberMap (f : M →ₗ[LaurentPolynomial K] N) :
    FiberAtOne K M →ₗ[K] FiberAtOne K N :=
  TensorProduct.AlgebraTensorModule.lTensor K K f

@[simp] theorem fiberMap_class (f : M →ₗ[LaurentPolynomial K] N) (x : M) :
    fiberMap K f (fiberClass K M x) = fiberClass K N (f x) :=
  rfl

theorem fiberClass_product_relation (μ : M ⊗[LaurentPolynomial K] M →ₗ[LaurentPolynomial K] N)
    {f g : M} {one d : N}
    (hμ : μ (f ⊗ₜ[LaurentPolynomial K] g) - one = (T 1 - 1 : LaurentPolynomial K) • d) :
    baseChangeMul K μ (fiberClass K M f ⊗ₜ[K] fiberClass K M g) = fiberClass K N one := by
  rw [fiberClass_mul]
  exact fiberClass_relation K N hμ

variable {P : Type*} [AddCommGroup P] [Module (LaurentPolynomial K) P]

/-- A short exact sequence of Laurent modules with free quotient remains short exact in the fiber. -/
theorem fiberAtOne_shortExact [Module.Free (LaurentPolynomial K) P]
    (f : M →ₗ[LaurentPolynomial K] N) (g : N →ₗ[LaurentPolynomial K] P)
    (hf : Function.Injective f) (hexact : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Injective (fiberMap K f) ∧
      Function.Exact (fiberMap K f) (fiberMap K g) ∧ Function.Surjective (fiberMap K g) := by
  obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hg)
  obtain ⟨e, hfe, _⟩ := (hexact.splitSurjectiveEquiv hf) ⟨s, hs⟩
  let r := (LinearMap.fst (LaurentPolynomial K) M P).comp e.toLinearMap
  have hr : r.comp f = LinearMap.id := by
    rw [hfe]
    ext x
    simp [r]
  have hsplit : (r.lTensor K).comp (f.lTensor K) = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, hr, LinearMap.lTensor_id]
  have hleft : Function.LeftInverse (r.lTensor K) (f.lTensor K) :=
    fun x => LinearMap.congr_fun hsplit x
  exact ⟨hleft.injective, lTensor_exact K hexact hg, LinearMap.lTensor_surjective K hg⟩

end Fiber

section DifferentialModule

variable {K M : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [Module (LaurentPolynomial K) M]
  [IsScalarTower K (LaurentPolynomial K) M] [Module.Finite (LaurentPolynomial K) M]

/-- Every finite module with a connection on the Laurent line is free. -/
theorem finiteLaurentDifferentialModuleFree (D : M →ₗ[K] M)
    (hD : ∀ (b : LaurentPolynomial K) (x : M),
      D (b • x) = laurentDerivation b • x + b • D x) :
    Module.Free (LaurentPolynomial K) M := by
  letI : Module.Projective (LaurentPolynomial K) M := StrictEUnit.finite_differential_module_projective
    laurentDerivation D hD laurentDerivation_stable_ideal_eq_top
  exact freeOfFiniteProjective

end DifferentialModule

section Faithfulness

variable {K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [Module (LaurentPolynomial K) M] [Module.Finite (LaurentPolynomial K) M]
  [AddCommGroup N] [Module K N] [Module (LaurentPolynomial K) N]
  [IsScalarTower K (LaurentPolynomial K) N] [Module.Finite (LaurentPolynomial K) N]

/-- A horizontal map of finite Laurent differential modules vanishes if its fiber does. -/
theorem fiberMap_eq_zero_of_horizontal (DM : M →ₗ[K] M) (DN : N →ₗ[K] N)
    (hDN : ∀ (b : LaurentPolynomial K) (y : N),
      DN (b • y) = laurentDerivation b • y + b • DN y)
    (f : M →ₗ[LaurentPolynomial K] N) (hf : ∀ x, DN (f x) = f (DM x))
    (h₁ : fiberMap K f = 0) : f = 0 := by
  let Q := LinearMap.range f
  have hQ (y : N) (hy : y ∈ Q) : DN y ∈ Q := by
    obtain ⟨x, rfl⟩ := hy
    exact ⟨DM x, (hf x).symm⟩
  letI : Module.Finite (LaurentPolynomial K) Q := Module.Finite.range f
  letI : Module.Finite (LaurentPolynomial K) (N ⧸ Q) :=
    Module.Finite.of_surjective Q.mkQ Q.mkQ_surjective
  letI : Module.Free (LaurentPolynomial K) Q :=
    finiteLaurentDifferentialModuleFree (StrictEUnit.restrictConnection Q DN hQ)
      (StrictEUnit.restrictConnection_leibniz laurentDerivation Q DN hQ hDN)
  letI : Module.Free (LaurentPolynomial K) (N ⧸ Q) :=
    finiteLaurentDifferentialModuleFree (StrictEUnit.quotientConnection Q DN hQ)
      (StrictEUnit.quotientConnection_leibniz laurentDerivation Q DN hQ hDN)
  have hi := (fiberAtOne_shortExact K Q.subtype Q.mkQ Q.subtype_injective
    (LinearMap.exact_subtype_mkQ Q) Q.mkQ_surjective).1
  have hzero (y : Q) : fiberClass K Q y = 0 := by
    obtain ⟨x, hx⟩ := y.property
    apply hi
    rw [fiberMap_class, map_zero]
    change fiberClass K N (y : N) = 0
    rw [← hx, ← fiberMap_class, h₁, LinearMap.zero_apply]
  have hy (y : Q) : y = 0 := by
    let b := Module.Free.chooseBasis (LaurentPolynomial K) Q
    apply b.repr.injective
    ext i
    have hi0 : (b.baseChange K) i = 0 := by
      rw [Basis.baseChange_apply]
      exact hzero (b i)
    exact ((b.baseChange K).ne_zero i hi0).elim
  ext x
  exact congrArg Subtype.val (hy ⟨f x, LinearMap.mem_range_self f x⟩)

/-- The algebraic fiber is faithful on horizontal maps. -/
theorem fiberMap_faithful (DM : M →ₗ[K] M) (DN : N →ₗ[K] N)
    (hDN : ∀ (b : LaurentPolynomial K) (y : N),
      DN (b • y) = laurentDerivation b • y + b • DN y)
    (f g : M →ₗ[LaurentPolynomial K] N) (hf : ∀ x, DN (f x) = f (DM x))
    (hg : ∀ x, DN (g x) = g (DM x)) (hfg : fiberMap K f = fiberMap K g) : f = g := by
  apply sub_eq_zero.mp
  refine fiberMap_eq_zero_of_horizontal DM DN hDN (f - g) ?_ ?_
  · intro x
    rw [LinearMap.sub_apply, map_sub, hf, hg, LinearMap.sub_apply]
  · change TensorProduct.AlgebraTensorModule.lTensor K K (f - g) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hfg

end Faithfulness

end WideE
