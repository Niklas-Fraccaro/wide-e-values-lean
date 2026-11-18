import WideE.CharacterClassification

/-! The strict value-unit classification as a corollary of the wide theorem. -/

namespace WideE

open StrictEUnit

/-- A strict unit is a wide unit, and algebraic scalar exponentials are strict units. -/
theorem strictEValueUnit_iff_algebraicScalarExp (ξ : ℂ) :
    IsStrictEValueUnit ξ ↔ IsAlgebraicScalarExp ξ :=
  ⟨fun h => (wideEValueUnit_iff_algebraicScalarExp ξ).mp (isWideEValueUnit_of_strict h),
    algebraic_exponential_reverse_inclusion⟩

/-- The units of the strict value subring have the claimed form. -/
theorem isUnit_strictEValueSubring_iff_algebraicScalarExp (u : strictEValueSubring) :
    IsUnit u ↔ IsAlgebraicScalarExp (u : ℂ) :=
  (strictEValueUnit_iff_isUnit u).symm.trans (strictEValueUnit_iff_algebraicScalarExp u)

end WideE
