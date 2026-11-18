import WideE.GaloisTorsor
import WideE.HopfConnectedDomain
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! Reducedness of the group coordinate algebra of a torsor with integral total space. -/

noncomputable section

open scoped TensorProduct

namespace WideE.AffineHopfTorsor

universe u

variable {k R S H : Type u} [Field k] [CommRing R] [IsDomain R] [CharZero R]
  [CommRing S] [IsDomain S] [CommRing H] [HopfAlgebra k H]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]

/-- The canonical chart embeds the group algebra into a reduced relative tensor product. -/
theorem group_isReduced_of_integral_total (T : AffineHopfTorsor k R S H) : IsReduced H := by
  letI := T.faithfullyFlat
  letI := T.finiteType
  have hker : RingHom.ker (algebraMap R S) = ⊥ := by
    have h := Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) (⊥ : Ideal R)
    simpa only [Ideal.map_bot, ← RingHom.ker_eq_comap_bot] using h
  letI : IsReduced (S ⊗[R] S) := flatDomainTensor_isReduced
    ((RingHom.injective_iff_ker_eq_bot _).mpr hker)
  let i : H →ₐ[k] S ⊗[k] H := Algebra.TensorProduct.includeRight
  have hi : Function.Injective i := Algebra.TensorProduct.includeRight_injective (algebraMap k S).injective
  exact isReduced_of_injective (T.chart.toRingEquiv.toRingHom.comp i.toRingHom)
    (T.chart.injective.comp hi)

/-- A connected group in the same setting has an integral coordinate algebra. -/
theorem group_isDomain_of_integral_total [IsAlgClosed k] [ConnectedSpace (PrimeSpectrum H)]
    (T : AffineHopfTorsor k R S H) : IsDomain H := by
  letI := T.group_finiteType
  letI := T.group_isReduced_of_integral_total
  exact hopfDomain_of_connected_reduced (k := k) (H := H)

end WideE.AffineHopfTorsor
