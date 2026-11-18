import WideE.IntegralTorsorReducedGroup
import WideE.NormalizedKummerCoordinate
import WideE.ResidualConnectedReduction
import WideE.TorsorTrivialization
import WideE.HopfAntipode
import Mathlib.RingTheory.TensorProduct.Quotient

/-! Removing the finite component cover of a Laurent-line torsor gives a connected fiber. -/

noncomputable section

open scoped TensorProduct
open LaurentPolynomial

namespace WideE

universe u

private def pointedTorsorQuotientEquiv {k Q S H : Type u} [Field k] [CommRing Q]
    [CommRing S] [CommRing H] [Algebra k Q] [Algebra k S] [Algebra Q S] [IsScalarTower k Q S]
    [HopfAlgebra k H]
    (T : AffineHopfTorsor k Q S H) (p : S →ₐ[k] k) :
    let σ := p.comp (IsScalarTower.toAlgHom k Q S)
    (S ⧸ (RingHom.ker σ.toRingHom).map (algebraMap Q S)) ≃+* H := by
  let σ := p.comp (IsScalarTower.toAlgHom k Q S)
  let I := RingHom.ker σ.toRingHom
  letI : Algebra Q k := σ.toRingHom.toAlgebra
  letI : IsScalarTower k Q k := IsScalarTower.of_algHom σ
  let f : S →ₐ[Q] k := { p.toRingHom with commutes' := fun _ => rfl }
  let e₀ : (Q ⧸ I) ≃ₐ[Q] k :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId Q k)
      (fun a => ⟨algebraMap k Q a, by exact σ.commutes a⟩)
  let e₁ := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e₀)
  let e₂ := (torsorChartOfSection T.chart f).trans (Algebra.TensorProduct.lid k H)
  exact e₁.toRingEquiv.trans ((Algebra.TensorProduct.comm Q S k).toRingEquiv.trans e₂.toRingEquiv)

private theorem ker_of_normalized_laurentCoordinate {k Q : Type*} [CommRing k] [CommRing Q]
    [Algebra k Q] (θ : LaurentPolynomial k ≃ₐ[k] Q) (σ : Q →ₐ[k] k)
    (hθ : σ (θ (T 1)) = 1) : RingHom.ker σ.toRingHom = Ideal.span {θ (T 1) - 1} := by
  let eval : LaurentPolynomial k →ₐ[k] k :=
    { evalAtOne k with commutes' := evalAtOne_C k }
  have hEval : σ.comp θ.toAlgHom = eval := laurentAlgHom_ext (hθ.trans (evalAtOne_T k 1).symm)
  calc
    RingHom.ker σ.toRingHom =
        Ideal.map θ.toRingEquiv.toRingHom (RingHom.ker (σ.comp θ.toAlgHom).toRingHom) :=
      (Ideal.map_comap_of_surjective θ.toRingEquiv.toRingHom θ.surjective _).symm
    _ = Ideal.span {θ (T 1) - 1} := by
      rw [hEval, show RingHom.ker eval.toRingHom = evaluationIdeal k from ker_evalAtOne k,
        evaluationIdeal, Ideal.map_span, Set.image_singleton, map_sub, map_one]
      rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 160000 in
/-- For an integral torsor over the Laurent line, normalizing the Kummer
coordinate of its component quotient gives a power root with reduced connected fiber at one. -/
theorem laurentTorsor_exists_normalizedRoot_reducedConnectedFiber {S J : Type} [CommRing S] [IsDomain S]
    [CommRing J] [Algebra AlgebraicComplex S] [Algebra (LaurentPolynomial AlgebraicComplex) S]
    [IsScalarTower AlgebraicComplex (LaurentPolynomial AlgebraicComplex) S]
    [HopfAlgebra AlgebraicComplex J]
    (T₀ : AffineHopfTorsor AlgebraicComplex (LaurentPolynomial AlgebraicComplex) S J)
    (p : S →ₐ[AlgebraicComplex] AlgebraicComplex)
    (hp : p (algebraMap (LaurentPolynomial AlgebraicComplex) S (LaurentPolynomial.T 1)) = 1) :
    ∃ (d : ℕ) (v : Sˣ), 0 < d ∧ (v : S) ^ d =
      algebraMap (LaurentPolynomial AlgebraicComplex) S (LaurentPolynomial.T 1) ∧
      p (v : S) = 1 ∧ ConnectedSpace (PrimeSpectrum (S ⧸ Ideal.span {(v : S) - 1})) ∧
      IsReduced (S ⧸ Ideal.span {(v : S) - 1}) := by
  let k := AlgebraicComplex
  let R := LaurentPolynomial k
  letI : IsAlgClosed k := IsAlgClosure.isAlgClosed ℚ
  letI : CharZero R := Algebra.charZero_of_charZero k R
  letI : IsReduced J := T₀.group_isReduced_of_integral_total
  letI : Algebra.FiniteType k J := T₀.group_finiteType
  obtain ⟨G⟩ := nonempty_componentHopfPresentation (hopfAntipodeAlgHom k J)
    (hopfAntipodeAlgHom_toLinearMap (k := k) (H := J))
  let Q := componentTorsorQuotient T₀ G
  letI : Module.Finite R Q := componentTorsorQuotient_finite T₀ G
  letI : Algebra.Etale R Q := componentTorsorQuotient_etale T₀ G
  letI : IrreducibleSpace (PrimeSpectrum Q) := PrimeSpectrum.irreducibleSpace
  letI : ConnectedSpace (PrimeSpectrum Q) := IrreducibleSpace.connectedSpace _
  letI : IsScalarTower k Q S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let σ := p.comp (Q.val.restrictScalars k)
  have hσ : σ (algebraMap R Q (LaurentPolynomial.T 1)) = 1 := hp
  obtain ⟨d, hd, _, e, he⟩ := exists_normalizedKummerCoordinate Q σ hσ
  let E : KummerExtension k d ≃ₐ[k] R := { KummerExtension.toLaurent k d with commutes' := fun _ => rfl }
  let θ : R ≃ₐ[k] Q := E.symm.trans (e.restrictScalars k)
  let vQ : Qˣ := Units.map θ.toMonoidHom (LaurentPolynomial.isUnit_T (R := k) 1).unit
  let v : Sˣ := Units.map Q.val.toMonoidHom vQ
  have hvQ : (vQ : Q) = θ (LaurentPolynomial.T 1) :=
    congrArg θ (LaurentPolynomial.isUnit_T (R := k) 1).unit_spec
  have hv : (v : S) = (θ (LaurentPolynomial.T 1) : Q) := congrArg (Subtype.val : Q → S) hvQ
  have ht : θ (LaurentPolynomial.T 1) = e (KummerExtension.power k d 1) := rfl
  have hcoord : (θ (LaurentPolynomial.T 1)) ^ d = algebraMap R Q (LaurentPolynomial.T 1) := by
    rw [ht, ← map_pow, KummerExtension.coordinate_pow, ← KummerExtension.algebraMap_coordinate, e.commutes]
  have hvd : (v : S) ^ d = algebraMap R S (LaurentPolynomial.T 1) := by
    rw [hv]
    exact (map_pow Q.val (θ (LaurentPolynomial.T 1)) d).symm.trans (congrArg Q.val hcoord)
  have hσθ : σ (θ (LaurentPolynomial.T 1)) = 1 := ht ▸ he
  have hvp : p (v : S) = 1 := hv ▸ hσθ
  refine ⟨d, v, hd, hvd, hvp, ?_⟩
  have hI : (RingHom.ker σ.toRingHom).map (algebraMap Q S) = Ideal.span {(v : S) - 1} := by
    rw [ker_of_normalized_laurentCoordinate θ σ hσθ, Ideal.map_span, Set.image_singleton,
      map_sub, map_one, hv]
    rfl
  letI := G.identityHopf
  letI := G.identityComponent_connected
  letI := G.identityComponent_isReduced
  let T₁ : AffineHopfTorsor k Q S G.IdentityComponent := identityComponentTorsor T₀ G
  rw [← hI]
  let F := pointedTorsorQuotientEquiv T₁ p
  have hF := PrimeSpectrum.isHomeomorph_comap_of_bijective (f := F.toRingHom) F.bijective
  exact ⟨hF.surjective.connectedSpace hF.continuous, isReduced_of_injective F F.injective⟩

/-- The normalized power coordinate has connected fiber at one. -/
theorem laurentTorsor_exists_normalizedRoot_connectedFiber {S J : Type} [CommRing S] [IsDomain S]
    [CommRing J] [Algebra AlgebraicComplex S] [Algebra (LaurentPolynomial AlgebraicComplex) S]
    [IsScalarTower AlgebraicComplex (LaurentPolynomial AlgebraicComplex) S]
    [HopfAlgebra AlgebraicComplex J]
    (T₀ : AffineHopfTorsor AlgebraicComplex (LaurentPolynomial AlgebraicComplex) S J)
    (p : S →ₐ[AlgebraicComplex] AlgebraicComplex)
    (hp : p (algebraMap (LaurentPolynomial AlgebraicComplex) S (LaurentPolynomial.T 1)) = 1) :
    ∃ (d : ℕ) (v : Sˣ), 0 < d ∧ (v : S) ^ d =
      algebraMap (LaurentPolynomial AlgebraicComplex) S (LaurentPolynomial.T 1) ∧
      p (v : S) = 1 ∧ ConnectedSpace (PrimeSpectrum (S ⧸ Ideal.span {(v : S) - 1})) := by
  obtain ⟨d, v, hd, hv, hPoint, hConn, _⟩ := laurentTorsor_exists_normalizedRoot_reducedConnectedFiber T₀ p hp
  exact ⟨d, v, hd, hv, hPoint, hConn⟩

end WideE
