import WideE.PicardVessiotPoint
import CandidateActionCoassociativity
import CandidateDifferentialCoaction

/-! The affine Picard–Vessiot torsor and its coaction over the constant field. -/

noncomputable section

open scoped TensorProduct WideE

namespace WideE

open StrictEUnit

attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule Subalgebra.toCommRing

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 80000

section Affine

variable {k B S H : Type*} [CommRing k] [CommRing B] [CommRing S] [CommRing H]
  [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S]

/-- Contract the group factor by the counit of its coordinate algebra. -/
def coactionCounit [Bialgebra k H] : S ⊗[k] H →ₐ[k] S :=
  Algebra.TensorProduct.lift (AlgHom.id k S)
    ((Algebra.ofId k S).comp (Bialgebra.counitAlgHom k H)) (fun _ _ => Commute.all _ _)

/-- Coordinate algebras of an affine torsor under a constant affine group. -/
structure AffineHopfTorsor (k B S H : Type*) [CommRing k] [CommRing B] [CommRing S] [CommRing H]
    [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S] [HopfAlgebra k H] where
  coaction : S →ₐ[B] S ⊗[k] H
  coassociative : ∀ s : S,
    Algebra.TensorProduct.assoc k S H H
      (Algebra.TensorProduct.map (coaction.restrictScalars k) (AlgHom.id k H) (coaction s)) =
    Algebra.TensorProduct.map (AlgHom.id S S) (Bialgebra.comulAlgHom k H) (coaction s)
  counital : ∀ s : S, coactionCounit (coaction s) = s
  canonical_bijective : Function.Bijective (relativeCandidateCanonical coaction)
  faithfullyFlat : Module.FaithfullyFlat B S
  group_finiteType : Algebra.FiniteType k H

variable [HopfAlgebra k H]

/-- The canonical map is also an algebra map for left multiplication by the
torsor algebra. -/
def AffineHopfTorsor.canonicalOverTorsor (T : AffineHopfTorsor k B S H) :
    S ⊗[B] S →ₐ[S] S ⊗[k] H where
  toRingHom := (relativeCandidateCanonical T.coaction).toRingHom
  commutes' s := by
    change relativeCandidateCanonical T.coaction (s ⊗ₜ[B] (1 : S)) = s ⊗ₜ[k] (1 : H)
    rw [relativeCandidateCanonical_tmul, map_one, mul_one]

/-- The inverse of the canonical map, in the direction of multiplication. -/
def AffineHopfTorsor.chart (T : AffineHopfTorsor k B S H) : S ⊗[k] H ≃ₐ[S] S ⊗[B] S :=
  (AlgEquiv.ofBijective T.canonicalOverTorsor T.canonical_bijective).symm

@[simp] theorem AffineHopfTorsor.chart_symm_apply (T : AffineHopfTorsor k B S H) (s t : S) :
    T.chart.symm (s ⊗ₜ[B] t) = (s ⊗ₜ[k] (1 : H)) * T.coaction t := rfl

end Affine

section Constants

variable {k B S : Type*} [Field k] [CommRing B] [CommRing S] [Nontrivial S]
  [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S]
variable (dB : Derivation k B B) (d : Derivation k S S)
  (hb : ∀ b, d (algebraMap B S b) = algebraMap B S (dB b))
  (he : Function.Bijective (pvConstantMultiplication dB d hb))
  (hc : ∀ s, d s = 0 → ∃ c : k, algebraMap k S c = s)

local notation "G" => pvConstantAlgebra dB d hb
local notation "e" => AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he

private def affineTorsorOfPVConstants
    (hflat : Module.FaithfullyFlat B S) (hfinite : Algebra.FiniteType k G) :
    letI := pvConstantHopfAlgebra dB d hb he hc
    AffineHopfTorsor k B S G := by
  letI := pvConstantHopfAlgebra dB d hb he hc
  refine ⟨inverseMultiplicationCoaction e, ?_, ?_,
    relativeCandidateCanonical_bijective e, hflat, hfinite⟩
  · intro s
    exact inverseMultiplicationCoaction_coassoc dB d hb he hc s
  · intro s
    exact candidateCounit_identity dB d hb hc he s

end Constants

section Ordinary

variable {K : Type*} [Field K] [CharZero K] {r : ℕ}
  (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))

local instance : CommRing (ordinaryPVAlgebra A) := (ordinaryPVAlgebra A).toCommRing
local instance : AddCommMonoid (ordinaryPVAlgebra A) := (ordinaryPVAlgebra A).toSemiring.toAddCommMonoid
local instance : Algebra (LaurentPolynomial K) (ordinaryPVAlgebra A) := (ordinaryPVAlgebra A).algebra
local instance : Algebra K (ordinaryPVAlgebra A) := (ordinaryPVAlgebra A).algebra'

private theorem ordinaryPV_constantMultiplication_bijective :
    Function.Bijective (pvConstantMultiplication laurentDerivation (ordinaryPVDerivation A)
      (ordinaryPVDerivation_base A)) :=
  (ordinaryPV_chart A).bijective

/-- The actual right coaction, induced by the multiplication isomorphism. -/
def ordinaryPVCoaction :
    ordinaryPVAlgebra A →ₐ[LaurentPolynomial K] ordinaryPVAlgebra A ⊗[K] ordinaryPVGroup A :=
  inverseMultiplicationCoaction (ordinaryPV_chart A)

@[simp] theorem ordinaryPVCoaction_apply (s : ordinaryPVAlgebra A) :
    ordinaryPVCoaction A s = (ordinaryPV_chart A).symm (1 ⊗ₜ[LaurentPolynomial K] s) := rfl

/-- The affine torsor of the normalized ordinary fundamental matrix. -/
def ordinaryPVTorsor :
    letI := ordinaryPVHopf A
    AffineHopfTorsor K (LaurentPolynomial K) (ordinaryPVAlgebra A) (ordinaryPVGroup A) :=
  affineTorsorOfPVConstants laurentDerivation (ordinaryPVDerivation A) (ordinaryPVDerivation_base A)
    (ordinaryPV_constantMultiplication_bijective A) (ordinaryPV_constants A)
    (ordinaryPV_faithfullyFlat A) (ordinaryPVGroup_finiteType A)

@[simp] theorem ordinaryPVTorsor_coaction :
    letI := ordinaryPVHopf A
    (ordinaryPVTorsor A).coaction = ordinaryPVCoaction A := rfl

theorem ordinaryPVCoaction_canonical_bijective :
    Function.Bijective (relativeCandidateCanonical (ordinaryPVCoaction A)) :=
  relativeCandidateCanonical_bijective (ordinaryPV_chart A)

theorem ordinaryPVCoaction_differential (s : ordinaryPVAlgebra A) :
    tensorDerivation (ordinaryPVDerivation A) (ordinaryPVCoaction A s) =
      ordinaryPVCoaction A (ordinaryPVDerivation A s) :=
  inverseMultiplicationCoaction_differential laurentDerivation (ordinaryPVDerivation A)
    (ordinaryPVDerivation_base A) (ordinaryPV_constantMultiplication_bijective A) s

end Ordinary

end WideE
