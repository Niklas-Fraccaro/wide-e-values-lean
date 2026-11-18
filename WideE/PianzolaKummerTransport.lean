import WideE.PianzolaReduction

/-! Transport a Laurent-line section theorem along the coefficient-algebra
identification of each Kummer cover. -/

noncomputable section

open scoped TensorProduct

namespace WideE

universe u

/-- The new coordinate identifies the Kummer cover with a Laurent line over
the coefficient field. -/
def KummerExtension.toLaurentAlgEquiv (K : Type*) [CommRing K] (q : ℕ) :
    KummerExtension K q ≃ₐ[K] LaurentPolynomial K :=
  { KummerExtension.toLaurent K q with commutes' := fun _ => rfl }

section BaseEquiv

variable {K B A S H : Type u} [CommRing K] [CommRing B] [CommRing A] [CommRing S] [CommRing H]
  [Algebra K B] [Algebra K A] [Algebra K S] [Algebra B S] [IsScalarTower K B S]
  [HopfAlgebra K H]

/-- A section theorem over an isomorphic base gives a section of the original
torsor by pulling back the section along the inverse base isomorphism. -/
theorem AffineHopfTorsor.nonempty_section_of_baseEquiv (T : AffineHopfTorsor K B S H)
    (e : B ≃ₐ[K] A)
    (hA : ∀ (S' : Type u) [CommRing S'] [Algebra K S'] [Algebra A S'] [IsScalarTower K A S'],
      AffineHopfTorsor K A S' H → Nonempty (S' →ₐ[A] A)) : Nonempty (S →ₐ[B] B) := by
  letI : Algebra B A := e.toRingEquiv.toRingHom.toAlgebra
  letI : IsScalarTower K B A := IsScalarTower.of_algHom e.toAlgHom
  letI : SMulCommClass B K A := ⟨fun b c a => by
    simp only [Algebra.smul_def]
    rw [← mul_assoc, ← mul_assoc, mul_comm (algebraMap B A b)]⟩
  let S' := A ⊗[B] S
  letI : Algebra K S' := Algebra.TensorProduct.leftAlgebra
  letI : Algebra A S' := Algebra.TensorProduct.leftAlgebra
  letI : IsScalarTower K A S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨s⟩ := hA S' (T.baseChange (A := A))
  let back : A →ₐ[B] B := { e.symm.toRingEquiv.toRingHom with commutes' := e.symm_apply_apply }
  exact ⟨back.comp ((componentSections B A S) s)⟩

end BaseEquiv

/-- The connected-group section theorem over the Laurent line supplies the
same theorem for every Kummer algebra in the comparison construction. -/
theorem pianzolaForKummerAlgebras_of_laurentSections {K : Type u} [Field K]
    (hLaurent : ∀ (H : Type u) [CommRing H] [Algebra K H] [HopfAlgebra K H]
      [Algebra.Smooth K H] [ConnectedSpace (PrimeSpectrum H)]
      (S : Type u) [CommRing S] [Algebra K S] [Algebra (LaurentPolynomial K) S]
      [IsScalarTower K (LaurentPolynomial K) S],
      AffineHopfTorsor K (LaurentPolynomial K) S H →
        Nonempty (S →ₐ[LaurentPolynomial K] LaurentPolynomial K)) :
    PianzolaForKummerAlgebras K := by
  intro q _ H _ _ _ _ _ S _ _ _ _ T
  exact T.nonempty_section_of_baseEquiv (KummerExtension.toLaurentAlgEquiv K q) (hLaurent H)

end WideE
