import AlgebraicPoint
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.Finite

/-! Galois descent of affine algebraic points and a finite field of definition
for a point of a nonempty finite-type algebra. -/

open scoped TensorProduct

noncomputable section

namespace WideE

open IntermediateField

variable {K L S : Type*} [Field K] [Field L] [Algebra K L] [CommRing S] [Algebra K S]

/-- A point invariant under every Galois automorphism comes from the base field. -/
theorem exists_basePoint_of_galois_fixed [IsGalois K L] (p : S →ₐ[K] L)
    (hFixed : ∀ (σ : L ≃ₐ[K] L) (s : S), σ (p s) = p s) :
    ∃ q : S →ₐ[K] K, (Algebra.ofId K L).comp q = p := by
  let incl := Algebra.ofId K L
  have hMem (x : S) : p x ∈ incl.range := by
    have h : p x ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) :=
      (IntermediateField.mem_fixedField_iff _ _).mpr (fun σ _ => hFixed σ x)
    rw [InfiniteGalois.fixedField_bot] at h
    exact IntermediateField.mem_bot.mp h
  let e := AlgEquiv.ofInjective incl (FaithfulSMul.algebraMap_injective K L)
  refine ⟨e.symm.toAlgHom.comp (p.codRestrict incl.range hMem), ?_⟩
  apply AlgHom.ext
  intro s
  exact congrArg Subtype.val (e.apply_symm_apply (p.codRestrict incl.range hMem s))

/-- A complex of algebraic coordinates for any one point is defined over a
finite Galois extension of the base in characteristic zero. -/
theorem exists_finiteGalois_point [CharZero K] [Algebra.FiniteType K S] [Nontrivial S] :
    ∃ E : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K E ∧ IsGalois K E ∧ Nonempty (S →ₐ[K] E) := by
  classical
  let L := AlgebraicClosure K
  letI : Algebra.FiniteType L (L ⊗[K] S) := Algebra.FiniteType.baseChange (R := K) L
  obtain ⟨p⟩ := StrictEUnit.nonempty_algebraic_point (k := L) (S := L ⊗[K] S)
  let f : S →ₐ[K] L := (p.restrictScalars K).comp Algebra.TensorProduct.includeRight
  obtain ⟨generators, hgen⟩ := (inferInstance : Algebra.FiniteType K S).out
  let D := IntermediateField.adjoin K (f '' (generators : Set S))
  letI : Finite (f '' (generators : Set S)) := (generators.finite_toSet.image f).to_subtype
  letI : FiniteDimensional K D := IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral x)
  let E := normalClosure K D L
  have hDE : D ≤ E := IntermediateField.le_normalClosure D
  have hgenE : (generators : Set S) ⊆ E.toSubalgebra.comap f := by
    intro x hx
    exact hDE (IntermediateField.subset_adjoin K _ (Set.mem_image_of_mem f hx))
  have htop : (⊤ : Subalgebra K S) ≤ E.toSubalgebra.comap f := by
    rw [← hgen]
    exact Algebra.adjoin_le_iff.mpr hgenE
  have hAll (x : S) : f x ∈ E.toSubalgebra := htop (show x ∈ (⊤ : Subalgebra K S) by simp)
  exact ⟨E, normalClosure.is_finiteDimensional K D L, inferInstance, ⟨f.codRestrict E.toSubalgebra hAll⟩⟩

end WideE
