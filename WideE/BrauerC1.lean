import WideE.CentralSimpleC1
import WideE.C1Extension
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Unique

/-!
# Triviality of the Brauer quotient of a characteristic-zero C₁ field

Every central simple algebra has the class of the base field. The result
applies over every algebraic extension by preservation of the C₁ property.
-/

noncomputable section

namespace WideE

universe u

private def matrixFinOneAlgEquiv (K A : Type*) [CommRing K] [Ring A] [Algebra K A] :
    Matrix (Fin 1) (Fin 1) A ≃ₐ[K] A where
  __ := (Matrix.uniqueAddEquiv : Matrix (Fin 1) (Fin 1) A ≃+ A)
  map_mul' X Y := by
    change (X * Y) 0 0 = X 0 0 * Y 0 0
    rw [Matrix.mul_apply, Fin.sum_univ_one]
  commutes' c := by
    change algebraMap K (Matrix (Fin 1) (Fin 1) A) c 0 0 = algebraMap K A c
    rw [Matrix.algebraMap_matrix_apply, if_pos rfl]

/-- The base field as a central simple algebra over itself. -/
def baseFieldCSA (K : Type u) [Field K] : CSA.{u, u} K where
  toAlgebraCat := AlgebraCat.of K K
  isCentral := ⟨fun a _ => ⟨a, rfl⟩⟩
  isSimple := inferInstance
  fin_dim := inferInstance

/-- Over a characteristic-zero C₁ field, every central simple algebra is Brauer equivalent
to the base field. -/
theorem isBrauerEquivalent_baseField_of_isC1 (K : Type u) [Field K] [CharZero K]
    (hK : IsC1 K) (A : CSA.{u, u} K) : IsBrauerEquivalent A (baseFieldCSA K) := by
  obtain ⟨m, hm, ⟨e⟩⟩ := centralSimple_splits_of_isC1 K A hK
  refine ⟨1, m, one_ne_zero, hm.ne', ?_⟩
  exact ⟨(matrixFinOneAlgEquiv K A).trans e⟩

/-- The Brauer quotient over a characteristic-zero C₁ field has one class. -/
theorem brauerGroup_subsingleton_of_isC1 (K : Type u) [Field K] [CharZero K]
    (hK : IsC1 K) : Subsingleton (BrauerGroup.{u, u} K) := by
  refine ⟨fun x y => Quotient.inductionOn₂ x y fun A B => ?_⟩
  exact Quotient.sound ((isBrauerEquivalent_baseField_of_isC1 K hK A).trans
    (isBrauerEquivalent_baseField_of_isC1 K hK B).symm)

private theorem charZero_of_field_algebra (K L : Type*) [Field K] [CharZero K]
    [Field L] [Algebra K L] : CharZero L :=
  ⟨fun a b h => Nat.cast_injective ((algebraMap K L).injective
    (by simpa only [map_natCast] using h))⟩

/-- All algebraic extensions of a characteristic-zero C₁ field have trivial Brauer quotient. -/
theorem brauerGroup_subsingleton_of_algebraic_extension (K L : Type u)
    [Field K] [CharZero K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (hK : IsC1 K) : Subsingleton (BrauerGroup.{u, u} L) := by
  letI : CharZero L := charZero_of_field_algebra K L
  exact brauerGroup_subsingleton_of_isC1 L (isC1_of_isAlgebraic hK)

/-- In characteristic zero, every algebraic extension of k(t) over algebraically
closed k has trivial Brauer quotient. -/
theorem brauerGroup_subsingleton_over_ratFunc (K L : Type u)
    [Field K] [CharZero K] [IsAlgClosed K] [Field L] [Algebra (RatFunc K) L]
    [Algebra.IsAlgebraic (RatFunc K) L] : Subsingleton (BrauerGroup.{u, u} L) := by
  letI : CharZero (RatFunc K) := charZero_of_field_algebra K (RatFunc K)
  exact brauerGroup_subsingleton_of_algebraic_extension (RatFunc K) L (ratFunc_isC1 K)

end WideE
