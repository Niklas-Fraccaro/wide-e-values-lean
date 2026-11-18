import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-! A semisimple endomorphism over an algebraically closed field has an eigenbasis. -/

noncomputable section

namespace WideE

open Module Module.End

variable {k V : Type*} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- Collect the bases of the eigenspaces of a semisimple endomorphism. -/
theorem exists_eigenbasis_of_isSemisimple (S : End k V) (hS : S.IsSemisimple) :
    ∃ (b : Basis (Fin (finrank k V)) k V) (d : Fin (finrank k V) → k),
      ∀ i, S (b i) = d i • b i := by
  classical
  have hSpan : ⨆ d : k, S.eigenspace d = ⊤ := by
    simpa only [hS.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] using
      S.iSup_maxGenEigenspace_eq_top
  let h := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top S.eigenspaces_iSupIndep hSpan
  let c := fun d : k => finBasis k (S.eigenspace d)
  let b := h.collectedBasis c
  let e := b.indexEquiv (finBasis k V)
  refine ⟨b.reindex e, fun i => (e.symm i).1, fun i => ?_⟩
  simp only [Basis.reindex_apply]
  exact mem_eigenspace_iff.mp (h.collectedBasis_mem c _)

/-- A commuting family of semisimple endomorphisms has a common eigenbasis. -/
theorem exists_simultaneousEigenbasis_of_isSemisimple {τ : Type*} (D : τ → End k V)
    (hComm : ∀ r s, Commute (D r) (D s)) (hSemi : ∀ r, (D r).IsSemisimple) :
    ∃ (b : Basis (Fin (finrank k V)) k V) (d : Fin (finrank k V) → τ → k),
      ∀ i r, D r (b i) = d i r • b i := by
  classical
  let E (d : τ → k) := ⨅ r, (D r).maxGenEigenspace (d r)
  have hIndep : iSupIndep E := independent_iInf_maxGenEigenspace_of_forall_mapsTo D
    (fun r s d => mapsTo_maxGenEigenspace_of_comm (hComm s r) _)
  have hSpan : ⨆ d, E d = ⊤ :=
    iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute D
      (fun r s _ => hComm r s) (fun r => (D r).iSup_maxGenEigenspace_eq_top)
  let h := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hIndep hSpan
  let c := fun d : τ → k => finBasis k (E d)
  let b := h.collectedBasis c
  let e := b.indexEquiv (finBasis k V)
  refine ⟨b.reindex e, fun i => (e.symm i).1, fun i r => ?_⟩
  simp only [Basis.reindex_apply]
  have hi := (iInf_le (fun j => (D j).maxGenEigenspace ((e.symm i).1 j)) r)
    (h.collectedBasis_mem c (e.symm i))
  rw [(hSemi r).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at hi
  exact mem_eigenspace_iff.mp hi

omit [IsAlgClosed k] [FiniteDimensional k V] in
/-- A finite eigenbasis gives a separable annihilating polynomial. -/
theorem isSemisimple_of_eigenbasis {ι : Type*} [Fintype ι] (D : End k V) (b : Basis ι k V)
    (d : ι → k) (h : ∀ i, D (b i) = d i • b i) : D.IsSemisimple := by
  classical
  let s := Finset.univ.image d
  let p := ∏ a ∈ s, (Polynomial.X - Polynomial.C a)
  have hSep : p.Separable := Polynomial.separable_prod_X_sub_C_iff'.mpr
    (fun _ _ _ _ he => he)
  apply isSemisimple_of_squarefree_aeval_eq_zero hSep.squarefree
  apply b.ext
  intro i
  have hp : p.eval (d i) = 0 := by
    rw [show p.eval (d i) = ∏ a ∈ s, (d i - a) by simp [p, Polynomial.eval_prod]]
    exact Finset.prod_eq_zero (Finset.mem_image_of_mem d (Finset.mem_univ i)) (sub_self _)
  rw [aeval_apply_of_hasEigenvector ⟨mem_eigenspace_iff.mpr (h i), b.ne_zero i⟩,
    hp, zero_smul, LinearMap.zero_apply]

end WideE
