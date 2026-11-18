import WideE.ComponentEtaleDescent
import WideE.ConnectedAffineLineCover
import WideE.HopfAntipode

/-! Connectedness of the group of a torsor with integral total space over the affine line. -/

noncomputable section

open scoped TensorProduct BigOperators

namespace WideE

universe u

private theorem connected_of_single_group_component {k J : Type u} [Field k]
    [CommRing J] [HopfAlgebra k J] (G : ComponentHopfPresentation k J)
    (hCard : letI := G.index_finite; Fintype.card G.Index = 1) : ConnectedSpace (PrimeSpectrum J) := by
  classical
  letI := G.index_finite
  letI : Subsingleton G.Index := Fintype.card_le_one_iff_subsingleton.mp hCard.le
  have h1 : G.idempotent G.identityIndex = 1 := by
    have h := G.complete.complete
    rw [Finset.sum_eq_single G.identityIndex] at h
    · exact h
    · intro i _ hi
      exact (hi (Subsingleton.elim _ _)).elim
    · simp
  let I : Ideal J := Ideal.span {1 - G.idempotent G.identityIndex}
  have hI : I = ⊥ := by simp [I, h1]
  let f : J →+* J ⧸ I := Ideal.Quotient.mk I
  have hf : Function.Injective f := (RingHom.injective_iff_ker_eq_bot f).mpr
    ((show RingHom.ker f = I from Ideal.mk_ker).trans hI)
  letI : ConnectedSpace (PrimeSpectrum (J ⧸ I)) := G.identityComponent_connected
  have h := PrimeSpectrum.isHomeomorph_comap_of_bijective
    (show Function.Bijective f from ⟨hf, Ideal.Quotient.mk_surjective⟩)
  exact h.surjective.connectedSpace h.continuous

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- A torsor with an integral total space over the affine line over the
algebraic numbers has a connected constant group. -/
theorem affineLineTorsor_group_connected {S J : Type} [CommRing S] [IsDomain S] [CommRing J]
    [Algebra AlgebraicComplex S] [Algebra (Polynomial AlgebraicComplex) S]
    [IsScalarTower AlgebraicComplex (Polynomial AlgebraicComplex) S]
    [HopfAlgebra AlgebraicComplex J]
    (T : AffineHopfTorsor AlgebraicComplex (Polynomial AlgebraicComplex) S J) :
    ConnectedSpace (PrimeSpectrum J) := by
  classical
  let k := AlgebraicComplex
  let R := Polynomial k
  letI : IsAlgClosed k := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra.FiniteType k J := T.group_finiteType
  obtain ⟨G⟩ := nonempty_componentHopfPresentation (hopfAntipodeAlgHom k J)
    (hopfAntipodeAlgHom_toLinearMap (k := k) (H := J))
  letI := G.index_finite
  let Q := componentTorsorQuotient T G
  letI : Module.Finite R Q := componentTorsorQuotient_finite T G
  letI : Algebra.Etale R Q := componentTorsorQuotient_etale T G
  let e : R ≃ₐ[R] Q := AlgEquiv.ofBijective (Algebra.ofId R Q) (affineLine_finiteEtaleDomain_bijective Q)
  letI : Module.Free R R := Module.Free.self R
  letI : Module.Free R Q := Module.Free.of_equiv e.toLinearEquiv
  have hQR : Module.finrank R Q = 1 := e.symm.toLinearEquiv.finrank_eq.trans (Module.finrank_self R)
  have hQ : Module.finrank S (S ⊗[R] Q) = 1 := Module.finrank_baseChange.trans hQR
  have hSplit := (componentTorsorQuotient_split T G).toLinearEquiv.finrank_eq
  exact connected_of_single_group_component G ((Module.finrank_pi (R := S)).symm.trans (hSplit.symm.trans hQ))

end WideE
