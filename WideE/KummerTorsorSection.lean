import WideE.Pianzola
import WideE.HopfCartier
import WideE.TorsorWeightDescent

/-! The global section on a Kummer cover for an affine Laurent torsor. -/

noncomputable section

namespace WideE

local notation "K" => AlgebraicComplex
local notation "R" => LaurentPolynomial AlgebraicComplex

set_option synthInstance.maxHeartbeats 120000 in
/-- A torsor under a linear algebraic group over the Laurent line has a
global section after a Kummer cover. -/
theorem AffineHopfTorsor.exists_kummerSection {H S : Type}
    [CommRing H] [HopfAlgebra K H] [CommRing S]
    [Algebra K S] [Algebra R S] [IsScalarTower K R S]
    (T : AffineHopfTorsor K R S H) :
    ∃ q : ℕ, 0 < q ∧ Nonempty (S →ₐ[R] KummerExtension K q) := by
  letI : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra.FiniteType K H := T.group_finiteType
  letI : Algebra.Smooth K H := hopfSmooth_of_charZero K H
  letI : Nontrivial S := T.algebraMap_injective.nontrivial
  obtain ⟨G⟩ := nonempty_componentHopfPresentation
    (hopfAntipodeAlgHom K H) hopfAntipodeAlgHom_toLinearMap
  exact (connectedTorsorReduction_of_affine T G).exists_section_of_kummerMap
    finiteLaurentCoverHasKummerMap_algebraicComplex pianzolaForKummerAlgebras

end WideE
