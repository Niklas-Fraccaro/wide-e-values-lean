import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! Finite generation descends along a faithfully flat scalar extension. -/

noncomputable section

open scoped TensorProduct

namespace WideE

private theorem tensor_exists_list_sum {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (x : S ⊗[R] M) :
    ∃ l : List (S × M), (l.map fun p => p.1 ⊗ₜ[R] p.2).sum = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨[], rfl⟩
  | tmul a m => exact ⟨[(a, m)], by simp⟩
  | add x y hx hy =>
    obtain ⟨l, rfl⟩ := hx
    obtain ⟨l', rfl⟩ := hy
    exact ⟨l ++ l', by rw [List.map_append, List.sum_append]⟩

/-- If a finite set generates the scalar extension, finitely many entries
of its elementary tensor expressions generate over the base. -/
theorem finite_of_faithfullyFlat_tensor {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.FaithfullyFlat R S] [Module.Finite S (S ⊗[R] M)] :
    Module.Finite R M := by
  classical
  obtain ⟨t, ht⟩ := Module.finite_def.mp (inferInstance : Module.Finite S (S ⊗[R] M))
  choose l hl using fun x : S ⊗[R] M => tensor_exists_list_sum x
  let u : Finset M := t.biUnion (fun x => (l x).toFinset.image Prod.snd)
  let N := Submodule.span R (↑u : Set M)
  let g : S ⊗[R] N →ₗ[S] S ⊗[R] M := TensorProduct.AlgebraTensorModule.lTensor S S N.subtype
  have hGen : Submodule.span S (↑t : Set (S ⊗[R] M)) ≤ LinearMap.range g := by
    apply Submodule.span_le.mpr
    intro x hx
    rw [← hl x]
    apply list_sum_mem
    intro y hy
    obtain ⟨⟨a, m⟩, hab, rfl⟩ := List.mem_map.mp hy
    have hm : m ∈ (↑u : Set M) := Finset.mem_biUnion.mpr
      ⟨x, hx, Finset.mem_image.mpr ⟨(a, m), List.mem_toFinset.mpr hab, rfl⟩⟩
    exact ⟨a ⊗ₜ[R] ⟨m, Submodule.subset_span hm⟩, rfl⟩
  have hsurj : Function.Surjective g := LinearMap.range_eq_top.mp (top_le_iff.mp (ht ▸ hGen))
  have hbase : Function.Surjective N.subtype :=
    (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S N.subtype).mp hsurj
  letI : Module.Finite R N := Module.Finite.iff_fg.mpr (Submodule.fg_span u.finite_toSet)
  exact Module.Finite.of_surjective N.subtype hbase

end WideE
