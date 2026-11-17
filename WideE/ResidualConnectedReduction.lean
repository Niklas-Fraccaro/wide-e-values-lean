import WideE.ComponentFaithfulFlatness
import WideE.ResidualPVTorsor
import WideE.PianzolaReduction
import WideE.HopfSmoothLocus

/-! The connected constant group acts as a torsor over the finite étale quotient. -/

noncomputable section

open scoped TensorProduct WideE

namespace WideE

attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule Subalgebra.toCommRing

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 90000

universe u

section Residual

variable {k B S H : Type u} [Field k] [IsAlgClosed k] [CommRing B] [CommRing S] [CommRing H]
  [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S] [HopfAlgebra k H]
  (T : AffineHopfTorsor k B S H) (G : ComponentHopfPresentation k H)

local notation "Q" => componentTorsorQuotient T G
local instance : IsScalarTower k (↥Q) S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The original torsor is a torsor under the identity component over the
coordinate algebra of the component quotient. -/
def identityComponentTorsor :
    letI := T.group_finiteType
    letI := G.identityHopf
    AffineHopfTorsor k (↥Q) S G.IdentityComponent := by
  letI := T.group_finiteType
  letI := G.identityHopf
  refine ⟨identityComponentCoaction T G, identityComponentCoaction_coassociative T G,
    identityComponentCoaction_counital T G, identityComponentCoaction_canonical_bijective T G,
    componentTorsorQuotient_faithfullyFlat T G, G.identityComponent_finiteType⟩

end Residual

theorem ComponentHopfPresentation.identityComponent_smooth
    {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H] [Algebra.Smooth k H]
    (G : ComponentHopfPresentation k H) : Algebra.Smooth k G.IdentityComponent := by
  letI := G.index_finite
  exact smooth_quotient_idempotent (G.complete.idem G.identityIndex)

section Laurent

variable {k S H : Type u} [Field k] [IsAlgClosed k] [CommRing S] [Nontrivial S] [CommRing H]
  [Algebra k S] [Algebra (LaurentPolynomial k) S] [IsScalarTower k (LaurentPolynomial k) S]
  [HopfAlgebra k H] [Algebra.Smooth k H]
  (T : AffineHopfTorsor k (LaurentPolynomial k) S H) (G : ComponentHopfPresentation k H)

/-- The finite étale and connected torsor data for a smooth affine group
over the Laurent base. -/
def connectedTorsorReduction_of_affine : ConnectedTorsorReduction k S := by
  let Q := componentTorsorQuotient T G
  let C := G.IdentityComponent
  letI := T.group_finiteType
  letI := G.identityHopf
  letI : Nontrivial Q := (algebraMap Q S).domain_nontrivial
  letI : IsScalarTower k Q S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Module.Finite (LaurentPolynomial k) Q := componentTorsorQuotient_finite T G
  letI : Algebra.Etale (LaurentPolynomial k) Q := componentTorsorQuotient_etale T G
  letI : Algebra.Smooth k C := G.identityComponent_smooth
  letI : ConnectedSpace (PrimeSpectrum C) := G.identityComponent_connected
  exact { quotient := Q, group := C, residual := identityComponentTorsor T G }

end Laurent

end WideE
