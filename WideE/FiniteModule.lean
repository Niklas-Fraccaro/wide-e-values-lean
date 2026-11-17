import WideE.Fiber
import Mathlib.RingTheory.Finiteness.Subalgebra

/-! Finite derivative spans, the separate product module, and the inverse
relation in its algebraic fiber. -/

noncomputable section

namespace WideE

open scoped TensorProduct

section DerivativeSpan

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]

/-- A monic recursion for the iterates of a connection gives a finite stable
span of the initial derivatives. -/
theorem finite_stable_span_of_monic (δ : R →+ R) (D : A →+ A)
    (hD : ∀ r x, D (r • x) = δ r • x + r • D x)
    (f : A) (r : ℕ) (hr : 0 < r) (b : Fin r → R)
    (hODE : D^[r] f = ∑ i : Fin r, b i • D^[i.val] f) :
    ∃ M : Submodule R A, M.FG ∧ f ∈ M ∧ ∀ x ∈ M, D x ∈ M := by
  let g : Fin r → A := fun i => D^[i.val] f
  let M := Submodule.span R (Set.range g)
  have hfinite : Module.Finite R M := finite_span g
  have hf : f ∈ M := Submodule.subset_span ⟨⟨0, hr⟩, rfl⟩
  refine ⟨M, Module.Finite.iff_fg.mp hfinite, hf, ?_⟩
  intro x hx
  apply derivation_mem_span δ D hD _ hx
  rintro _ ⟨i, rfl⟩
  change D (D^[i.val] f) ∈ M
  rw [← Function.iterate_succ_apply' (f := (D : A → A)) i.val f]
  by_cases hi : i.val + 1 < r
  · exact Submodule.subset_span ⟨⟨i.val + 1, hi⟩, rfl⟩
  · have e : i.val + 1 = r := Nat.le_antisymm (Nat.succ_le_of_lt i.isLt) (Nat.le_of_not_lt hi)
    change D^[i.val + 1] f ∈ M
    rw [e, hODE]
    exact Submodule.sum_mem _ (fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

theorem stable_sup (D : A →+ A) {M N : Submodule R A}
    (hM : ∀ x ∈ M, D x ∈ M) (hN : ∀ x ∈ N, D x ∈ N) :
    ∀ x ∈ M ⊔ N, D x ∈ M ⊔ N := by
  intro x hx
  obtain ⟨m, hm, n, hn, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact Submodule.mem_sup.mpr ⟨D m, hM _ hm, D n, hN _ hn, rfl⟩

end DerivativeSpan

section Products

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The multiplication on the underlying algebra has target the product span,
which can be larger than the original module. -/
def productBilinear (M : Submodule R A) : M →ₗ[R] M →ₗ[R] (M * M : Submodule R A) where
  toFun m :=
    { toFun := fun n => ⟨m.val * n.val, Submodule.mul_mem_mul m.property n.property⟩
      map_add' := fun n p => Subtype.ext (mul_add m.val n.val p.val)
      map_smul' := fun r n => Subtype.ext (mul_smul_comm r m.val n.val) }
  map_add' m n := by
    ext p
    exact add_mul m.val n.val p.val
  map_smul' r m := by
    ext p
    exact smul_mul_assoc r m.val p.val

def productMap (M : Submodule R A) : M ⊗[R] M →ₗ[R] (M * M : Submodule R A) :=
  TensorProduct.lift (productBilinear M)

@[simp] theorem productMap_tmul (M : Submodule R A) (x y : M) :
    (productMap M (x ⊗ₜ[R] y)).val = x.val * y.val := by
  change (TensorProduct.lift (productBilinear M) (x ⊗ₜ[R] y)).val = _
  rw [TensorProduct.lift.tmul]
  rfl

theorem productMap_surjective (M : Submodule R A) : Function.Surjective (productMap M) := by
  rintro ⟨x, hx⟩
  induction hx using Submodule.mul_induction_on' with
  | mem_mul_mem m hm n hn =>
    refine ⟨(⟨m, hm⟩ : M) ⊗ₜ[R] (⟨n, hn⟩ : M), Subtype.ext ?_⟩
    simp
  | add m hm n hn ihm ihn =>
    obtain ⟨U, hU⟩ := ihm
    obtain ⟨V, hV⟩ := ihn
    refine ⟨U + V, ?_⟩
    rw [map_add, hU, hV]
    rfl

theorem productModule_fg {M : Submodule R A} (hM : M.FG) :
    (M * M).FG := hM.mul hM

theorem productModule_stable (D : A →+ A) {M : Submodule R A}
    (hM : ∀ x ∈ M, D x ∈ M) (hLeibniz : ∀ a b, D (a * b) = D a * b + a * D b) :
    ∀ x ∈ M * M, D x ∈ M * M := by
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro m hm n hn
    rw [hLeibniz]
    exact Submodule.add_mem _ (Submodule.mul_mem_mul (hM _ hm) hn)
      (Submodule.mul_mem_mul hm (hM _ hn))
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

theorem le_productModule {M : Submodule R A} (h1 : (1 : A) ∈ M) :
    M ≤ M * M := fun x hx => by
  simpa only [mul_one] using Submodule.mul_mem_mul hx h1

/-- The image of the constant one in the product module. -/
def productOne (M : Submodule R A) (h1 : (1 : A) ∈ M) : (M * M : Submodule R A) :=
  ⟨1, le_productModule h1 h1⟩

def productUnitInclusion (M : Submodule R A) (h1 : (1 : A) ∈ M) :
    R →ₗ[R] (M * M : Submodule R A) :=
  LinearMap.toSpanSingleton R _ (productOne M h1)

@[simp] theorem productUnitInclusion_one (M : Submodule R A) (h1 : (1 : A) ∈ M) :
    productUnitInclusion M h1 1 = productOne M h1 := by simp [productUnitInclusion]

end Products

section InverseFiber

open LaurentPolynomial
open scoped WideE

variable {K A : Type*} [Field K] [CommRing A] [Algebra (LaurentPolynomial K) A]

/-- The factorization of the actual residual product gives the transported
product relation in the algebraic module fiber. -/
theorem inverse_fiber_of_factorization (M : Submodule (LaurentPolynomial K) A)
    (h1 : (1 : A) ∈ M) (f g h : M)
    (hfactor : f.val * g.val - 1 = (T 1 - 1 : LaurentPolynomial K) • h.val) :
    baseChangeMul K (productMap M) (fiberClass K M f ⊗ₜ[K] fiberClass K M g) =
      fiberClass K (M * M : Submodule (LaurentPolynomial K) A) (productOne M h1) := by
  let h' : (M * M : Submodule (LaurentPolynomial K) A) := ⟨h.val, le_productModule h1 h.property⟩
  have hsub : productMap M (f ⊗ₜ[LaurentPolynomial K] g) - productOne M h1 =
      (T 1 - 1 : LaurentPolynomial K) • h' := by
    apply Subtype.ext
    simpa only [Submodule.coe_sub, productMap_tmul] using hfactor
  exact fiberClass_product_relation K (productMap M) hsub

end InverseFiber

end WideE
