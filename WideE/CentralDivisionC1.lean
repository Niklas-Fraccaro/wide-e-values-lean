import WideE.CentralDivisionBaseChange
import WideE.SimpleAlgebraSplit
import WideE.DivisionAlgebraC1
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Basic

/-! A central division algebra over a characteristic-zero C₁ field is the base field. -/

noncomputable section

open scoped TensorProduct

namespace WideE

/-- Over a C₁ field of characteristic zero, every finite-dimensional central
division algebra is isomorphic to the base field. -/
theorem centralDivision_algEquiv_base_of_isC1
    (K D : Type*) [Field K] [CharZero K] [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [FiniteDimensional K D] (hK : IsC1 K) :
    Nonempty (D ≃ₐ[K] K) := by
  let L := AlgebraicClosure K
  letI : IsGalois K L := inferInstance
  letI : FiniteDimensional L (L ⊗[K] D) :=
    Module.Finite.of_basis (Algebra.TensorProduct.basis L (Module.finBasis K D))
  letI : IsSimpleRing (L ⊗[K] D) := scalarExtension_centralDivision_isSimple
  obtain ⟨m, ⟨e⟩⟩ := simple_algebra_splits_over_isAlgClosed L (L ⊗[K] D)
  exact exists_algEquiv_base_of_isC1_of_galois_splitting hK e

end WideE
