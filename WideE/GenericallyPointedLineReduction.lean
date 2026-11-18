import WideE.ClosedProjectiveOrbit
import WideE.LineOrbitPullback
import WideE.ProjectiveLineTorsor

/-! Reduction to a line stabilizer while retaining the prescribed generic point. -/

open scoped Matrix TensorProduct

noncomputable section

namespace WideE

universe u

variable {k H ι : Type u} {R S F : Type*} [Field k] [IsAlgClosed k] [CommRing H]
  [IsDomain H] [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CommRing S]
  [Field F] [Algebra k R] [Algebra k S] [Algebra k F] [Algebra R S] [Algebra R F]
  [IsScalarTower k R S] [IsScalarTower k R F] [IsFractionRing R F]
  [HopfAlgebra k H] [Algebra.FiniteType k R] [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- For a generically pointed affine torsor over a finite-type PID, the
closed projective orbit construction gives a faithfully flat torsor under
the stabilizer of a line and a factorization of the given generic point. -/
theorem AffineHopfTorsor.exists_genericallyPointedProjectiveLineTorsor
    (T : AffineHopfTorsor k R S H) (U : (Matrix ι ι H)ˣ)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (f : S →ₐ[R] F) :
    ∃ (v : ι → k) (pivot : ι) (_hpivot : v pivot ≠ 0)
      (g : (Matrix ι ι S)ˣ) (y : ι → R),
      let w := projectiveFrameVector g y
      let Q := ProjectiveLineReduction v pivot w
      let π := projectiveLineQuotient (R := R) v pivot w
      let J := projectiveLineStabilizerIdeal U v pivot
      let ξ := Ideal.Quotient.mkₐ k J
      ∃ hJ : IsHopfIdeal k J,
      letI := hJ.quotientHopf
      ∃ (TQ : AffineHopfTorsor k R Q (H ⧸ J)) (fQ : Q →ₐ[R] F),
        fQ.comp π = f ∧
        TQ.coaction.comp π = (Algebra.TensorProduct.map π ξ).comp T.coaction := by
  classical
  letI := T.group_finiteType
  obtain ⟨v, hv, hOrbit⟩ := exists_closed_projectiveOrbit U hU he
  have hPivot : ∃ i : ι, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  obtain ⟨pivot, hpivot⟩ := hPivot
  have hOne : U.val.map (Bialgebra.counitAlgHom k H).toRingHom = 1 :=
    Matrix.ext fun i j => (he i j).trans Matrix.one_apply.symm
  obtain ⟨g, y, hg, hPrimitive, hCone, _, fQ, hfQ⟩ :=
    T.exists_genericallyPointedLineReduction U hU hOne v pivot hpivot f
  have hFF := projectiveLineReduction_faithfullyFlat T U hU g y hg v pivot hpivot
    hPrimitive hCone hOrbit
  let hJ := projectiveLineStabilizerIdeal_isHopf U v pivot hpivot hU he
  obtain ⟨TQ, hρ⟩ := T.exists_projectiveLineTorsor U g y hg v pivot hpivot hPrimitive hJ hFF
  exact ⟨v, pivot, hpivot, g, y, hJ, TQ, fQ, hfQ, hρ⟩

end WideE
