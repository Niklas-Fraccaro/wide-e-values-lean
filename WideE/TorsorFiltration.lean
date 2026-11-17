import WideE.AdditiveTorsor
import WideE.MultiplicativeTorsor
import WideE.TorsorBaseChange

/-! Sections for a tower of affine torsors with split additive or
multiplicative factors. -/

noncomputable section

open scoped TensorProduct

namespace WideE

set_option maxHeartbeats 550000
set_option synthInstance.maxHeartbeats 85000

section Extensions

variable {k B Q S : Type*} [Field k] [CommRing B] [CommRing Q] [CommRing S]
  [Algebra k B] [Algebra k Q] [Algebra k S] [Algebra B Q] [Algebra B S] [Algebra Q S]
  [IsScalarTower k B Q] [IsScalarTower k Q S] [IsScalarTower B Q S]

/-- The inverse image of a section of the quotient is a torsor under the
same constant kernel group. -/
def AffineHopfTorsor.overSection {H : Type*} [CommRing H] [HopfAlgebra k H]
    (T : AffineHopfTorsor k Q S H) (σ : Q →ₐ[B] B) :
    letI := σ.toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom (σ.restrictScalars k)
    AffineHopfTorsor k B (B ⊗[Q] S) H := by
  letI := σ.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom (σ.restrictScalars k)
  exact T.baseChange (A := B)

/-- A section of the inverse image extends the given section of the quotient. -/
def sectionFromPullback (σ : Q →ₐ[B] B)
    (τ : letI := σ.toRingHom.toAlgebra; (B ⊗[Q] S) →ₐ[B] B) : S →ₐ[B] B := by
  letI := σ.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom σ
  exact ((componentSections Q B S) τ).restrictScalars B

@[simp] theorem sectionFromPullback_algebraMap (σ : Q →ₐ[B] B)
    (τ : letI := σ.toRingHom.toAlgebra; (B ⊗[Q] S) →ₐ[B] B) (q : Q) :
    sectionFromPullback σ τ (algebraMap Q S q) = σ q := by
  letI := σ.toRingHom.toAlgebra
  exact ((componentSections Q B S) τ).commutes q

local instance filtrationAdditiveHopf : HopfAlgebra k (Polynomial k) := additivePolynomialHopf k

/-- A section of the base of an additive torsor extends to the torsor. -/
theorem exists_section_extension_additive (σ : Q →ₐ[B] B)
    (T : AffineHopfTorsor k Q S (Polynomial k)) :
    ∃ τ : S →ₐ[B] B, ∀ q : Q, τ (algebraMap Q S q) = σ q := by
  letI := σ.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom (σ.restrictScalars k)
  obtain ⟨τ⟩ := affineAdditiveTorsor_has_section (T.overSection σ)
  exact ⟨sectionFromPullback σ τ, sectionFromPullback_algebraMap σ τ⟩

/-- A section of the base of a multiplicative torsor extends when the
original base is a PID. -/
theorem exists_section_extension_multiplicative [IsDomain B] [IsPrincipalIdealRing B]
    (σ : Q →ₐ[B] B) (T : AffineHopfTorsor k Q S (LaurentPolynomial k)) :
    ∃ τ : S →ₐ[B] B, ∀ q : Q, τ (algebraMap Q S q) = σ q := by
  letI := σ.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom (σ.restrictScalars k)
  obtain ⟨τ⟩ := affineMultiplicativeTorsor_has_section (T.overSection σ)
  exact ⟨sectionFromPullback σ τ, sectionFromPullback_algebraMap σ τ⟩

end Extensions

universe u

local instance towerAdditiveHopf (k : Type u) [Field k] : HopfAlgebra k (Polynomial k) :=
  additivePolynomialHopf k

/-- Each step is an actual affine torsor under the constant additive or
multiplicative group over the previous quotient algebra. -/
inductive AffineTorsorFiltration (k B : Type u) [Field k] [CommRing B] [Algebra k B] :
    ∀ (S : Type u) [CommRing S] [Algebra k S] [Algebra B S] [IsScalarTower k B S], Prop
  | base : AffineTorsorFiltration k B B
  | additive {Q S : Type u} [CommRing Q] [CommRing S] [Algebra k Q] [Algebra k S]
      [Algebra B Q] [Algebra B S] [Algebra Q S] [IsScalarTower k B Q]
      [IsScalarTower k B S] [IsScalarTower k Q S] [IsScalarTower B Q S] :
      AffineTorsorFiltration k B Q → AffineHopfTorsor k Q S (Polynomial k) →
      AffineTorsorFiltration k B S
  | multiplicative {Q S : Type u} [CommRing Q] [CommRing S] [Algebra k Q] [Algebra k S]
      [Algebra B Q] [Algebra B S] [Algebra Q S] [IsScalarTower k B Q]
      [IsScalarTower k B S] [IsScalarTower k Q S] [IsScalarTower B Q S] :
      AffineTorsorFiltration k B Q → AffineHopfTorsor k Q S (LaurentPolynomial k) →
      AffineTorsorFiltration k B S

/-- A filtration of the actual quotient torsors gives a section over a PID.
At each step one takes the fiber over the previously constructed section. -/
theorem AffineTorsorFiltration.has_section {k B S : Type u}
    [Field k] [CommRing B] [CommRing S] [IsDomain B] [IsPrincipalIdealRing B]
    [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S]
    (filtration : AffineTorsorFiltration k B S) :
    Nonempty (S →ₐ[B] B) := by
  induction filtration with
  | base => exact ⟨AlgHom.id B B⟩
  | additive _ T ih =>
    obtain ⟨σ⟩ := ih
    obtain ⟨τ, _⟩ := exists_section_extension_additive σ T
    exact ⟨τ⟩
  | multiplicative _ T ih =>
    obtain ⟨σ⟩ := ih
    obtain ⟨τ, _⟩ := exists_section_extension_multiplicative σ T
    exact ⟨τ⟩

end WideE
