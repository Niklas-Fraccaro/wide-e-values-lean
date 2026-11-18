import WideE.ResidualConnectedReduction
import WideE.TorsorFiltration
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! A generic point chooses a component over an integrally closed base and
gives a generic point on the corresponding torsor under the identity component. -/

noncomputable section

open scoped TensorProduct

namespace WideE

universe u

variable {k R S H F : Type u}
  [Field k] [IsAlgClosed k] [CommRing R] [IsIntegrallyClosed R]
  [CommRing S] [CommRing H] [HopfAlgebra k H] [CommRing F]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
  [Algebra R F] [IsFractionRing R F]
  (T : AffineHopfTorsor k R S H) (G : ComponentHopfPresentation k H)

local notation "Q" => componentTorsorQuotient T G

/-- The component of a generic point is defined over the base, and the point
lifts to the pullback over that component section. Integrality of the quotient
follows from its finiteness. -/
theorem exists_genericPoint_on_component_section (f : S →ₐ[R] F) :
    ∃ σ : Q →ₐ[R] R, (∀ q : Q, algebraMap R F (σ q) = f (q : S)) ∧
      (letI := σ.toRingHom.toAlgebra
       ∃ p : (R ⊗[Q] S) →ₐ[R] F, ∀ s : S, p ((1 : R) ⊗ₜ[Q] s) = f s) := by
  let fQ : Q →ₐ[R] F := f.comp (Q).val
  letI : Module.Finite R Q := componentTorsorQuotient_finite T G
  letI : Algebra Q F := fQ.toRingHom.toAlgebra
  letI : IsScalarTower R Q F := IsScalarTower.of_algHom fQ
  let σ : Q →ₐ[R] R := IsIntegralClosure.lift R R F
  have hσ (q : Q) : algebraMap R F (σ q) = f (q : S) :=
    IsIntegralClosure.algebraMap_lift R R F q
  refine ⟨σ, hσ, ?_⟩
  letI : Algebra Q R := σ.toRingHom.toAlgebra
  letI : IsScalarTower Q R F := IsScalarTower.of_algebraMap_eq (fun q => (hσ q).symm)
  let fOverQ : S →ₐ[Q] F := { toRingHom := f.toRingHom, commutes' := fun _ => rfl }
  let p : (R ⊗[Q] S) →ₐ[R] F :=
    Algebra.TensorProduct.lift (Algebra.ofId R F) (fOverQ) (fun _ _ => Commute.all _ _)
  refine ⟨p, fun s => ?_⟩
  change algebraMap R F 1 * f s = f s
  rw [map_one, one_mul]

/-- A section theorem for the generically trivial torsors of the identity
component gives a section of the original generically trivial torsor. -/
theorem nonempty_section_of_identityComponent_generic_sections (f : S →ₐ[R] F)
    (hSection :
      letI := T.group_finiteType
      letI := G.identityHopf
      ∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra R A] [IsScalarTower k R A],
        AffineHopfTorsor k R A G.IdentityComponent → (A →ₐ[R] F) → Nonempty (A →ₐ[R] R)) :
    Nonempty (S →ₐ[R] R) := by
  obtain ⟨σ, _, p, _⟩ := exists_genericPoint_on_component_section T G f
  letI : Algebra Q R := σ.toRingHom.toAlgebra
  letI : IsScalarTower k Q R := IsScalarTower.of_algHom (σ.restrictScalars k)
  letI : IsScalarTower k Q S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI := T.group_finiteType
  letI := G.identityHopf
  obtain ⟨τ⟩ := hSection _ ((identityComponentTorsor T G).overSection σ) p
  exact ⟨sectionFromPullback σ τ⟩

end WideE
