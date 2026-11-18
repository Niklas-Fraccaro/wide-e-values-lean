import WideE.AffineGroupRepresentation
import WideE.GenericallyPointedLineReduction
import WideE.LaurentGenericPoint
import WideE.MatrixFlagRefinement
import WideE.ReducedLineStabilizer
import WideE.SmoothReduced
import WideE.UpperTriangularTorsor

/-! Projective reduction to a triangular group and the Laurent section theorem
for a torsor with a generic point. -/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

section Maps

variable {k H J K ι : Type*} [CommRing k] [CommRing H] [CommRing J] [CommRing K]
  [HopfAlgebra k H] [HopfAlgebra k J] [HopfAlgebra k K] [Fintype ι] [DecidableEq ι]

private def mapMatrixUnit (π : H →ₐc[k] J) (U : (Matrix ι ι H)ˣ) : (Matrix ι ι J)ˣ :=
  U.map (π : H →ₐ[k] J).toRingHom.mapMatrix.toMonoidHom

private theorem mapMatrixUnit_comp (p : J →ₐc[k] K) (q : H →ₐc[k] J) (U : (Matrix ι ι H)ˣ) :
    mapMatrixUnit (p.comp q) U = mapMatrixUnit p (mapMatrixUnit q U) :=
  Units.ext (Matrix.ext fun _ _ => rfl)

private theorem mapMatrixUnit_conjugate (p : H →ₐc[k] J) (W : (Matrix ι ι k)ˣ) (U : (Matrix ι ι H)ˣ) :
    mapMatrixUnit p (conjugateMatrixUnit W U) = conjugateMatrixUnit W (mapMatrixUnit p U) :=
  conjugateMatrixUnit_map W U (p : H →ₐ[k] J)

end Maps

section Reduction

variable {k R F : Type} [Field k] [IsAlgClosed k] [CharZero k]
  [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsIntegrallyClosed R]
  [Algebra k R] [Algebra.FiniteType k R] [Field F] [Algebra k F] [Algebra R F]
  [IsScalarTower k R F] [IsFractionRing R F]

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 100000 in
private theorem section_of_triangular_reductions
    (n : ℕ) (H S : Type) [CommRing H] [HopfAlgebra k H] [IsDomain H]
    [CommRing S] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    (T : AffineHopfTorsor k R S H) (f : S →ₐ[R] F) (U : (Matrix (Fin n) (Fin n) H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (finish : ∀ (J : Type) [CommRing J] [HopfAlgebra k J] [IsDomain J]
      (π : H →ₐc[k] J), Function.Surjective π → ∀ W : (Matrix (Fin n) (Fin n) k)ˣ,
        (conjugateMatrixUnit W (mapMatrixUnit π U)).val.BlockTriangular id →
        ∀ (A : Type) [CommRing A] [Algebra k A] [Algebra R A] [IsScalarTower k R A],
          AffineHopfTorsor k R A J → Nonempty (A →ₐ[R] R)) :
    Nonempty (S →ₐ[R] R) := by
  induction n generalizing H S with
  | zero =>
    apply finish H (BialgHom.id k H) (fun a => ⟨a, rfl⟩) 1
    · intro i
      exact Fin.elim0 i
    · exact T
  | succ n ih =>
    letI : Algebra.FiniteType k H := T.group_finiteType
    obtain ⟨v, pivot, hpivot, g, y, hJ, TQ, fQ, _, _⟩ :=
      T.exists_genericallyPointedProjectiveLineTorsor (k := k) (ι := Fin (n + 1)) U hD he f
    let J := H ⧸ projectiveLineStabilizerIdeal U v pivot
    letI : HopfAlgebra k J := hJ.quotientHopf
    letI : Algebra.FiniteType k J := TQ.group_finiteType
    letI : IsReduced J := projectiveLineStabilizer_isReduced (ι := Fin (n + 1)) U hD he v pivot hpivot
    obtain ⟨G⟩ := nonempty_componentHopfPresentation (hopfAntipodeAlgHom k J)
      (hopfAntipodeAlgHom_toLinearMap (k := k) (H := J))
    let J₀ := G.IdentityComponent
    letI : HopfAlgebra k J₀ := G.identityHopf
    letI : IsDomain J₀ := G.identityComponent_isDomain
    let p : J →ₐc[k] J₀ := BialgHom.ofAlgHom G.identityQuotient
      (LinearMap.ext fun a => AlgHom.congr_fun G.identityCounit_comp_quotient a)
      (LinearMap.ext fun a => (G.identityComul_quotient a).symm)
    let π := p.comp hJ.quotientBialgHom
    have hπ : Function.Surjective π := G.identityQuotient_surjective.comp
      (Ideal.Quotient.mkₐ_surjective k (projectiveLineStabilizerIdeal U v pivot))
    obtain ⟨P, hCol⟩ := exists_matrixUnit_column v pivot 0 hpivot
    obtain ⟨c, hc⟩ := projectiveLineStabilizer_scale U v pivot hpivot
    let U₀ := mapMatrixUnit π U
    have hLine : U₀.val *ᵥ (algebraMap k J₀ ∘ v) = p (c : J) • (algebraMap k J₀ ∘ v) :=
      lineScale_map v (p : J →ₐ[k] J₀) _ _ hc
    let V := conjugateMatrixUnit P U₀
    have hFirst (i : Fin n) : V.val i.succ 0 = 0 :=
      conjugateMatrixUnit_column_zero P U₀ v 0 hCol _ hLine i.succ (Fin.succ_ne_zero i)
    obtain ⟨hD₀, he₀⟩ := hopfMatrixRelations_map U.val π hD he
    obtain ⟨hDV, heV⟩ := conjugateMatrixUnit_hopf P U₀ hD₀ he₀
    let Vtail := tailMatrixUnit V hFirst
    obtain ⟨hDTail, heTail⟩ := tailMatrixUnit_hopf V hFirst hDV heV
    obtain ⟨σ⟩ := nonempty_section_of_identityComponent_generic_sections TQ G fQ (by
      intro A _ _ _ _ T₀ f₀
      apply ih J₀ A T₀ f₀ Vtail hDTail heTail
      intro D _ _ _ q hq B hUpper A' _ _ _ _ T'
      have hFirst' (i : Fin n) : (mapMatrixUnit q V).val i.succ 0 = 0 := by
        change q (V.val i.succ 0) = 0
        rw [hFirst, map_zero]
      obtain ⟨hFirst'', hTail'⟩ := conjugateMatrixUnit_extendTailBasis B (mapMatrixUnit q V) hFirst'
      have hTailMap : tailMatrixUnit (mapMatrixUnit q V) hFirst' = mapMatrixUnit q Vtail :=
        Units.ext (Matrix.ext fun _ _ => rfl)
      rw [hTailMap] at hTail'
      have hCompose : conjugateMatrixUnit (P * extendTailBasis B) (mapMatrixUnit (q.comp π) U) =
          conjugateMatrixUnit (extendTailBasis B) (mapMatrixUnit q V) := by
        rw [mapMatrixUnit_comp, ← conjugateMatrixUnit_conjugate, ← mapMatrixUnit_conjugate]
      refine finish D (q.comp π) (hq.comp hπ) (P * extendTailBasis B) ?_ A' T'
      rw [hCompose]
      intro i j hij
      change j < i at hij
      cases i using Fin.cases with
      | zero => exact (Fin.not_lt_zero _ hij).elim
      | succ i =>
        cases j using Fin.cases with
        | zero => exact hFirst'' i
        | succ j =>
          have h := congrFun (congrFun hTail' i) j
          exact h.trans (hUpper (Fin.succ_lt_succ_iff.mp hij)))
    exact ⟨σ.comp (projectiveLineQuotient (R := R) v pivot (projectiveFrameVector g y))⟩

end Reduction

section Laurent

local notation "k₀" => AlgebraicComplex
local notation "R₀" => LaurentPolynomial AlgebraicComplex

variable {H S : Type} [CommRing H] [HopfAlgebra k₀ H] [IsDomain H] [CommRing S]
  [Algebra k₀ S] [Algebra R₀ S] [IsScalarTower k₀ R₀ S]

/-- A generic point of the actual affine torsor extends to a Laurent section. -/
theorem AffineHopfTorsor.nonempty_laurentSection_of_genericPoint (T : AffineHopfTorsor k₀ R₀ S H) :
    letI := laurentRatFuncAlgebra k₀
    (S →ₐ[R₀] RatFunc k₀) → Nonempty (S →ₐ[R₀] R₀) := by
  letI := laurentRatFuncAlgebra k₀
  letI := laurentRatFunc_scalarTower k₀
  letI := laurentRatFunc_isFractionRing k₀
  letI : IsAlgClosed k₀ := IsAlgClosure.isAlgClosed ℚ
  letI : IsPrincipalIdealRing R₀ := StrictEUnit.laurentPolynomial_isPrincipalIdealRing k₀
  letI : Algebra.FiniteType k₀ R₀ := laurentPolynomial_finiteType (H := k₀)
  letI : Algebra.FiniteType k₀ H := T.group_finiteType
  intro f
  obtain ⟨n, U, hD, he, hGen⟩ := exists_generatingHopfMatrix k₀ H
  apply section_of_triangular_reductions n H S T f U hD he
  intro J _ _ _ π hπ P hUpper A _ _ _ _ T'
  let V := mapMatrixUnit π U
  obtain ⟨hDV, heV⟩ := hopfMatrixRelations_map U.val π hD he
  obtain ⟨hDW, heW⟩ := conjugateMatrixUnit_hopf P V hDV heV
  have hV := generatingMatrix_map U.val (π : H →ₐ[k₀] J) hπ hGen
  have hW := conjugateMatrixUnit_generating P V hV
  exact upperTriangular_affineHopfTorsor_has_section T' (conjugateMatrixUnit P V).val hDW heW hUpper hW

end Laurent

section ConnectedGroup

variable {H S : Type} [CommRing H] [HopfAlgebra AlgebraicComplex H]
  [Algebra.Smooth AlgebraicComplex H] [ConnectedSpace (PrimeSpectrum H)] [CommRing S]
  [Algebra AlgebraicComplex S] [Algebra (LaurentPolynomial AlgebraicComplex) S]
  [IsScalarTower AlgebraicComplex (LaurentPolynomial AlgebraicComplex) S]

/-- For the smooth connected groups of the comparison theorem, a Laurent section
exists exactly when the generic fiber has a rational point. -/
theorem AffineHopfTorsor.nonempty_laurentSection_iff_genericPoint
    (T : AffineHopfTorsor AlgebraicComplex (LaurentPolynomial AlgebraicComplex) S H) :
    let R := LaurentPolynomial AlgebraicComplex
    let F := RatFunc AlgebraicComplex
    letI := laurentRatFuncAlgebra AlgebraicComplex
    Nonempty (S →ₐ[R] R) ↔ Nonempty (S →ₐ[R] F) := by
  letI := laurentRatFuncAlgebra AlgebraicComplex
  constructor
  · rintro ⟨s⟩
    exact ⟨(Algebra.ofId (LaurentPolynomial AlgebraicComplex) (RatFunc AlgebraicComplex)).comp s⟩
  · rintro ⟨f⟩
    letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
    letI : Algebra.FiniteType AlgebraicComplex H := T.group_finiteType
    letI : IsReduced H := isReduced_of_smooth_of_isAlgClosed AlgebraicComplex H
    letI : IsDomain H := hopfDomain_of_connected_reduced (k := AlgebraicComplex)
    exact T.nonempty_laurentSection_of_genericPoint f

end ConnectedGroup

end WideE
