import WideE.AdjointCentralizerBaseChange
import WideE.AdjointCentralizerConjugation
import WideE.HopfLieBaseChange
import WideE.HopfLieMap
import WideE.RegularDiagonalCentralizer
import WideE.TorusSplittingField

/-! The scheme-theoretic torus centralizer on the diagonal locus after scalar extension. -/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

section Diagonal

variable {k H Q A ι η : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing Q] [HopfAlgebra k Q] [CommRing A] [Algebra k A] [DecidableEq ι] [Fintype η]

/-- Every tangent direction that lifts to a diagonal quotient is diagonal in the representation. -/
theorem hopfLieMatrix_lift_to_diagonal (U : Matrix ι ι H) (π : H →ₐc[k] Q)
    (hπ : ∀ i j, i ≠ j → π (U i j) = 0) (D : hopfInvariantDerivations k Q) :
    let M := hopfLieMatrix U (hopfInvariantDerivationsMap π D)
    M = Matrix.diagonal (fun i => M i i) := by
  dsimp only
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij]
    change Bialgebra.counitAlgHom k H ((hopfInvariantDerivationsMap π D).val (U i j)) = 0
    rw [hopfInvariantDerivationsMap_counit, hπ i j hij, map_zero, map_zero]

/-- The diagonal entries of a linear combination of diagonal tangents are the same
linear combination of their diagonal entries. -/
theorem hopfCotangentMatrix_sum_diagonal (U : Matrix ι ι H) (v : η → HopfLieVector k H k)
    (a : η → ι → k) (hv : ∀ r, hopfCotangentMatrix U (v r) = Matrix.diagonal (a r)) (x : η → A) :
    hopfCotangentMatrix U (∑ r, x r • (Algebra.ofId k A).toLinearMap.comp (v r)) =
      Matrix.diagonal (fun i => ∑ r, x r * algebraMap k A (a r i)) := by
  apply Matrix.ext
  intro i j
  change (∑ r, x r • (Algebra.ofId k A).toLinearMap.comp (v r)) (hopfCotangentProjection k H (U i j)) = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    Algebra.ofId_apply, smul_eq_mul]
  have h (r : η) : v r (hopfCotangentProjection k H (U i j)) = Matrix.diagonal (a r) i j :=
    congrArg (fun M : Matrix ι ι k => M i j) (hv r)
  simp_rw [h]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
  · simp only [Matrix.diagonal_apply_ne _ hij, map_zero, mul_zero, Finset.sum_const_zero]

end Diagonal

section Geometry

variable {k Ω H Q ι η W : Type*} [Field k] [Field Ω] [Algebra k Ω]
  [CommRing H] [HopfAlgebra k H] [CommRing Q] [HopfAlgebra k Q]
  [Fintype ι] [DecidableEq ι] [Fintype η] [DecidableEq η]

attribute [local instance] hopfScalarExtension

local notation "HΩ" => (Ω ⊗[k] H)
local notation "QΩ" => (Ω ⊗[k] Q)

set_option maxHeartbeats 1400000 in
/-- The actual centralizer of a diagonal tangent separating the principal blocks
is the scalar extension of the diagonal quotient. -/
def bialgEquiv_hopfAdjointCentralizer_diagonal_baseChange
    (b : Basis η k (HopfCotangent k H)) (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (w : ι → W) (π : H →ₐc[k] Q) (hSurj : Function.Surjective π)
    (hπ : ∀ i j, i ≠ j → π (U.val i j) = 0)
    (hBlock : weightCentralizerIdeal w U.val = RingHom.ker (π : H →ₐ[k] Q).toRingHom)
    (x : HopfLieVector k H Ω) (a : ι → Ω)
    (hX : hopfCotangentMatrix U.val x = Matrix.diagonal a)
    (hDistinct : ∀ i j, w i ≠ w j → a j ≠ a i) :
    let b' := hopfCotangentBasisBaseChange (F := Ω) b
    let x' := hopfLieVectorBaseChange (F := Ω) x
    letI := (hopfAdjointCentralizerIdeal_isHopf b' x').quotientHopf
    (HΩ ⧸ hopfAdjointCentralizerIdeal b' x') ≃ₐc[Ω] QΩ := by
  let b' := hopfCotangentBasisBaseChange (F := Ω) b
  let x' := hopfLieVectorBaseChange (F := Ω) x
  let r : H →ₐ[k] HΩ := Algebra.TensorProduct.includeRight
  let V := U.map r.toRingHom.mapMatrix.toMonoidHom
  let π' := scalarExtendBialgHom (F := Ω) π
  let πₐ : HΩ →ₐ[Ω] QΩ := π'
  have hV (i j : ι) : V.val i j = r (U.val i j) := rfl
  obtain ⟨hDV, heV⟩ := hopfMatrixRelations_baseChange (F := Ω) U.val hD he
  have hGenV := hopfMatrix_generates_baseChange (F := Ω) U.val hGen
  have hπV (i j : ι) (hij : i ≠ j) : πₐ (V.val i j) = 0 := by
    change π' ((1 : Ω) ⊗ₜ[k] U.val i j) = 0
    rw [scalarExtendBialgHom_tmul, hπ i j hij, TensorProduct.tmul_zero]
  have hBlockV : weightCentralizerIdeal w V.val = RingHom.ker πₐ.toRingHom := by
    rw [show πₐ = (π' : HΩ →ₐ[Ω] QΩ) from rfl, scalarExtendBialgHom_ker π, ← hBlock]
    simp only [weightCentralizerIdeal, Ideal.map_span]
    congr 1
    ext z
    constructor
    · rintro ⟨i, j, hij, rfl⟩
      exact ⟨U.val i j, ⟨i, j, hij, rfl⟩, (hV i j).symm⟩
    · rintro ⟨_, ⟨i, j, hij, rfl⟩, rfl⟩
      exact ⟨i, j, hij, hV i j⟩
  have hXV : hopfCotangentMatrix V.val x' = Matrix.diagonal a :=
    (hopfCotangentMatrix_baseChange (F := Ω) U.val x).trans hX
  have hJ := hopfAdjointCentralizerIdeal_eq_ker_of_separating_diagonal b' V hDV heV hGenV
    w πₐ hπV hBlockV x' a hXV hDistinct
  exact bialgEquiv_quotientOfKerEq (hopfAdjointCentralizerIdeal_isHopf b' x') π'
    (scalarExtendBialgHom_surjective π hSurj) hJ

end Geometry

end WideE
