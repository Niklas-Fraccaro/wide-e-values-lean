import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection

/-!
# Finite-dimensional simple algebras over an algebraically closed field

On a simple module, an endomorphism commuting with the algebra is scalar:
subtract an eigenvalue and use the nonzero kernel. A semisimple product of
such modules shows that the algebra realizes arbitrary images of a basis.
Thus its simple representation is the full endomorphism algebra.
-/

noncomputable section

open scoped BigOperators

namespace WideE

section Eigenvalue

variable {K S M : Type*} [Field K] [IsAlgClosed K] [Ring S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable [SMulCommClass K S M] [FiniteDimensional K M] [IsSimpleModule S M]

private theorem endomorphism_isScalar (f : Module.End S M) :
    ∃ c : K, ∀ x : M, f x = c • x := by
  letI : Nontrivial M := IsSimpleModule.nontrivial S M
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f.restrictScalars K)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  let g : Module.End S M := f - (Algebra.lsmul K S M : K →ₐ[K] Module.End S M) c
  have hg : g v = 0 := sub_eq_zero.mpr hv.apply_eq_smul
  have hg₀ : g = 0 := (LinearMap.injective_or_eq_zero g).resolve_left fun hinj =>
    hv.2 (hinj (hg.trans (map_zero g).symm))
  refine ⟨c, fun x => sub_eq_zero.mp ?_⟩
  exact LinearMap.congr_fun hg₀ x

end Eigenvalue

section Density

variable {K S M : Type*} [DivisionRing K] [Ring S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable (hEnd : ∀ f : Module.End S M, ∃ c : K, ∀ x : M, f x = c • x)

include hEnd

private theorem linearMap_pi_eq_zero_of_basis_eval_zero
    {ι : Type*} [Fintype ι] (b : Basis ι K M) (f : (ι → M) →ₗ[S] M)
    (h : f (fun i => b i) = 0) : f = 0 := by
  classical
  choose c hc using fun i : ι => hEnd (f.comp (LinearMap.single S (fun _ => M) i))
  have hEval (x : ι → M) : f x = ∑ i, c i • x i := by
    have hx : (∑ i, Pi.single i (x i)) = x := by
      funext i
      simp only [Finset.sum_apply, Finset.sum_pi_single, Finset.mem_univ, if_true]
    have he := congrArg f hx
    rw [map_sum] at he
    calc
      f x = ∑ i, f (Pi.single i (x i)) := he.symm
      _ = ∑ i, c i • x i := Finset.sum_congr rfl fun i _ => hc i (x i)
  have hCoeffs : ∀ i, c i = 0 :=
    (Fintype.linearIndependent_iff.mp b.linearIndependent) c ((hEval (fun i => b i)).symm.trans h)
  apply LinearMap.ext
  intro x
  simp only [hEval, hCoeffs, zero_smul, Finset.sum_const_zero, LinearMap.zero_apply]

variable [SMulCommClass S K M] [FiniteDimensional K M] [IsSimpleModule S M]

/-- On a simple module with finite dimension over a division ring of commuting
endomorphisms, the acting ring realizes every linear endomorphism for that division ring. -/
theorem simple_module_action_surjective :
    Function.Surjective (DistribMulAction.toLinearMap K M : S → Module.End K M) := by
  let b := Module.finBasis K M
  let v : Fin (Module.finrank K M) → M := fun i => b i
  let W := LinearMap.range (LinearMap.toSpanSingleton S (Fin (Module.finrank K M) → M) v)
  have hW : W = ⊤ := by
    obtain ⟨U, hWU⟩ := exists_isCompl W
    let p := U.linearProjOfIsCompl W hWU.symm
    have hv : v ∈ W := ⟨1, by simp only [LinearMap.toSpanSingleton_apply, one_smul]⟩
    have hpv : p v = 0 := Submodule.linearProjOfIsCompl_apply_right' hWU.symm v hv
    have hZero (i : Fin (Module.finrank K M)) :
        ((LinearMap.proj i).comp U.subtype).comp p = 0 := by
      apply linearMap_pi_eq_zero_of_basis_eval_zero hEnd b
      change ((p v : U) : Fin (Module.finrank K M) → M) i = 0
      rw [hpv]
      rfl
    have hp : p = 0 := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      funext i
      exact LinearMap.congr_fun (hZero i) x
    have hker : LinearMap.ker p = W := Submodule.linearProjOfIsCompl_ker hWU.symm
    rw [hp, LinearMap.ker_zero] at hker
    exact hker.symm
  intro f
  let w : Fin (Module.finrank K M) → M := fun i => f (b i)
  have hw : w ∈ W := hW ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := hw
  refine ⟨a, ?_⟩
  apply b.ext
  intro i
  exact congrFun ha i

end Density

/-- A finite-dimensional simple algebra over an algebraically closed field is a matrix algebra. -/
theorem simple_algebra_splits_over_isAlgClosed
    (K S : Type*) [Field K] [IsAlgClosed K] [Ring S] [Algebra K S]
    [FiniteDimensional K S] [IsSimpleRing S] :
    ∃ m : ℕ, Nonempty (S ≃ₐ[K] Matrix (Fin m) (Fin m) K) := by
  obtain ⟨I, hI, _⟩ := Ideal.exists_le_maximal (⊥ : Ideal S) bot_ne_top
  let M := S ⧸ I
  letI : IsSimpleModule S M := isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp hI)
  letI : Nontrivial M := IsSimpleModule.nontrivial S M
  letI : FiniteDimensional K M := Module.Finite.of_surjective
    ((Submodule.mkQ I).restrictScalars K) (Submodule.mkQ_surjective I)
  let ρ : S →ₐ[K] Module.End K M := Algebra.lsmul K K M
  let e := AlgEquiv.ofBijective ρ ⟨ρ.toRingHom.injective,
    simple_module_action_surjective (K := K) (S := S) (M := M) (endomorphism_isScalar (K := K))⟩
  exact ⟨Module.finrank K M, ⟨e.trans (LinearMap.toMatrixAlgEquiv (Module.finBasis K M))⟩⟩

end WideE
