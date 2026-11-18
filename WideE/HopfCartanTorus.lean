import WideE.DiagonalDerivationTorus
import WideE.HopfLieMap
import WideE.LieInvariantFlag
import WideE.SemisimpleEigenbasis
import Mathlib.LinearAlgebra.Matrix.Basis

/-! Commuting semisimple tangent matrices lie in the Lie algebra of a single split torus. -/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

section MatrixBasis

variable {k ι τ : Type*} [Field k] [IsAlgClosed k] [Fintype ι] [DecidableEq ι]

private theorem exists_simultaneousDiagonalization (X : τ → Matrix ι ι k)
    (hComm : ∀ r s, Commute (X r) (X s))
    (hS : ∀ r, Module.End.IsSemisimple (Matrix.toLinAlgEquiv' (X r))) :
    ∃ (P : (Matrix ι ι k)ˣ) (d : ι → τ → k),
      ∀ r, P.inv * X r * P.val = Matrix.diagonal (fun i => d i r) := by
  classical
  let E : Matrix ι ι k ≃ₐ[k] Module.End k (ι → k) := Matrix.toLinAlgEquiv'
  obtain ⟨b₀, d₀, hb₀⟩ := exists_simultaneousEigenbasis_of_isSemisimple (fun r => E (X r))
    (fun r s => (hComm r s).map E.toAlgHom) hS
  let std := Pi.basisFun k ι
  let re := b₀.indexEquiv std
  let b := b₀.reindex re
  let d (i : ι) := d₀ (re.symm i)
  have hb (i : ι) (r : τ) : E (X r) (b i) = d i r • b i := by
    simpa only [b, d, Basis.reindex_apply] using hb₀ (re.symm i) r
  let P : (Matrix ι ι k)ˣ :=
    ⟨std.toMatrix b, b.toMatrix std, std.toMatrix_mul_toMatrix_flip b, b.toMatrix_mul_toMatrix_flip std⟩
  refine ⟨P, d, fun r => ?_⟩
  change b.toMatrix std * X r * std.toMatrix b = _
  have hX := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b std b std
    (Matrix.toLin std std (X r))
  rw [LinearMap.toMatrix_toLin] at hX
  rw [hX, Matrix.toLin_eq_toLin']
  ext i j
  rw [LinearMap.toMatrix_apply, show Matrix.toLin' (X r) (b j) = d j r • b j from hb j r,
    map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

end MatrixBasis

section Torus

variable {k H ι τ : Type*} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Fintype ι] [DecidableEq ι]

/-- A commuting family of semisimple tangents belongs to the differential of
a diagonal subgroup whose coordinate algebra is the lattice of their joint weights. -/
theorem exists_diagonalTorus_of_commuting_semisimple_tangents (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (D : τ → hopfInvariantDerivations k H) (hComm : ∀ r s, ⁅D r, D s⁆ = 0)
    (hSemi : ∀ r, Module.End.IsSemisimple (Matrix.toLinAlgEquiv' (hopfLieMatrix U.val (D r)))) :
    ∃ (P : (Matrix ι ι k)ˣ) (d : ι → τ → k) (f : H →ₐc[k] diagonalWeightAlgebra k d),
      Function.Surjective f ∧
      (∀ i j, f ((conjugateMatrixUnit P U).val i j) = if i = j then diagonalWeightMonomial k d i else 0) ∧
      (∀ r, ∃ x : hopfInvariantDerivations k (diagonalWeightAlgebra k d),
        hopfInvariantDerivationsMap f x = D r) := by
  let ρ := hopfLieMatrixHom U.val hΔ
  have hMC (r s : τ) : Commute (hopfLieMatrix U.val (D r)) (hopfLieMatrix U.val (D s)) := by
    change Commute (ρ (D r)) (ρ (D s))
    rw [commute_iff_lie_eq, ← LieHom.map_lie, hComm, LieHom.map_zero]
  obtain ⟨P, d, hP⟩ := exists_simultaneousDiagonalization _ hMC hSemi
  let V := conjugateMatrixUnit P U
  obtain ⟨hVΔ, hVε⟩ := conjugateMatrixUnit_hopf P U hΔ hε
  have hVGen := conjugateMatrixUnit_generating P U hGen
  have hVD (r : τ) : hopfLieMatrix V.val (D r) = Matrix.diagonal (fun i => d i r) :=
    (hopfLieMatrix_conjugateMatrixUnit P U (D r)).trans (hP r)
  have hDerivations (r s : τ) : Commute (D r).val.toLinearMap (D s).val.toLinearMap := by
    apply sub_eq_zero.mp
    apply LinearMap.ext
    intro a
    change ⁅D r, D s⁆.val a = 0
    rw [hComm]
    rfl
  have hWeights (r : τ) (i j : ι) :
      V.val i j ∈ Module.End.maxGenEigenspace (D r).val.toLinearMap (d j r) := by
    refine (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨1, ?_⟩
    rw [pow_one]
    change (D r).val (V.val i j) - d j r • V.val i j = 0
    rw [sub_eq_zero, hopfInvariantDerivation_matrixCoefficient V.val hVΔ (D r), hVD]
    rw [Finset.sum_eq_single j]
    · rw [Matrix.diagonal_apply_eq, Algebra.smul_def, mul_comm]
    · intro l _ hlj
      rw [Matrix.diagonal_apply_ne _ hlj, map_zero, mul_zero]
    · exact fun h => (h (Finset.mem_univ j)).elim
  obtain ⟨f, hSurj, hf⟩ := exists_diagonalTorus_of_simultaneousWeights V hVΔ hVε hVGen
    (fun r => (D r).val) d hDerivations hWeights
  refine ⟨P, d, f, hSurj, hf, fun r => ?_⟩
  let q := Pi.evalAddMonoidHom (fun _ : τ => k) r
  let T := diagonalWeightAlgebra k d
  let p : HopfInfinitesimalPoint k T k := ⟨diagonalWeightInfinitesimalPoint d q,
    fun a => diagonalWeightInfinitesimalPoint_fst d q a⟩
  let x := (hopfInfinitesimalPointEquiv k T k).symm p
  have hx (a : T) : x (hopfCotangentProjection k T a) = (p.val a).snd := by
    have he : hopfLieInfinitesimalPoint x = p.val :=
      congrArg Subtype.val ((hopfInfinitesimalPointEquiv k T k).apply_symm_apply p)
    rw [← he, hopfLieInfinitesimalPoint_snd]
  refine ⟨hopfLieVectorInvariantDerivations x, ?_⟩
  apply hopfLieMatrixHom_injective V.val hVΔ hVGen
  apply Matrix.ext
  intro i j
  change (Bialgebra.counitAlgHom k H)
    ((hopfInvariantDerivationsMap f (hopfLieVectorInvariantDerivations x)).val (V.val i j)) =
      hopfLieMatrix V.val (D r) i j
  rw [hopfInvariantDerivationsMap_counit, hopfLieVectorInvariantDerivations_counit, hx, hVD,
    Matrix.diagonal_apply, hf]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij]
    exact congrArg TrivSqZeroExt.snd (diagonalWeightInfinitesimalPoint_monomial d q i)
  · rw [if_neg hij, if_neg hij, map_zero, TrivSqZeroExt.snd_zero]

end Torus

end WideE
