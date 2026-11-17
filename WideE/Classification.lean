import WideE.LaurentExistence
import WideE.ModuleRealization
import WideE.PVComparison

/-! The classification reduced to the existence of Kummer sections of the
actual Picard–Vessiot torsors. -/

open scoped WideE

noncomputable section

namespace WideE

local notation "Coefficients" => AlgebraicComplex
local notation "R" => LaurentPolynomial AlgebraicComplex
local notation "D" => widePuncturedDerivation

set_option synthInstance.maxHeartbeats 80000

/-- The section assertion from §7 for the specific torsors used in the proof. -/
def WidePVKummerSectionExistence : Prop :=
  ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) R),
    ∃ q : ℕ, 0 < q ∧ Nonempty (ordinaryPVAlgebra A →ₐ[R] KummerExtension Coefficients q)

set_option maxHeartbeats 800000 in
theorem exists_fin_basis_of_stable (M : Submodule R WidePunctured)
    (hfin : M.FG) (hStable : ∀ x ∈ M, D x ∈ M) :
    ∃ n : ℕ, Nonempty (Basis (Fin n) R M) := by
  letI : Module.Finite R M := Module.Finite.iff_fg.mpr hfin
  let d : WidePunctured →ₗ[Coefficients] WidePunctured := (D).toLinearMap
  let dM : M →ₗ[Coefficients] M := StrictEUnit.restrictConnection (k := Coefficients) (B := R) M d hStable
  have hLeib (p : R) (x : M) : dM (p • x) = laurentDerivation p • x + p • dM x :=
    Subtype.ext (widePuncturedDerivation_smul p x.val)
  letI : Module.Free R M := finiteLaurentDifferentialModuleFree (K := Coefficients) dM hLeib
  exact ⟨_, ⟨Module.finBasis R M⟩⟩

set_option maxHeartbeats 1600000 in
/-- Realize the original numerical unit as an algebraic scalar times the
exponential of an algebraic number. -/
theorem algebraic_scalar_exp_of_wideEValueUnit_of_sections
    (hSection : WidePVKummerSectionExistence)
    {ξ : ℂ} (hξ : IsWideEValueUnit ξ) : IsAlgebraicScalarExp ξ := by
  obtain ⟨data⟩ := exists_wideInverseModule wideLaurentOperatorExistence hξ
  let M := data.M
  let N : Submodule R WidePunctured := M * M
  let d := (D).toLinearMap.toAddMonoidHom
  have hM : ∀ x ∈ M, d x ∈ M := data.stable
  have hN : ∀ x ∈ N, d x ∈ N :=
    productModule_stable d hM (fun x y => widePuncturedDerivation_mul x y)
  obtain ⟨m, ⟨bM⟩⟩ := exists_fin_basis_of_stable M data.finite hM
  obtain ⟨n, ⟨bN⟩⟩ := exists_fin_basis_of_stable N (productModule_fg data.finite) hN
  let A := combinedLaurentSystem (connectionSystemMatrix bM (restrictConnection d M hM))
    (connectionSystemMatrix bN (restrictConnection d N hN))
  obtain ⟨q, hq, ⟨s⟩⟩ := hSection (m + n) A
  let comparison := comparison_of_stable_productModule_kummer_section d M hM
    (fun x y => widePuncturedDerivation_mul x y) (fun p x => widePuncturedDerivation_smul p x)
    data.one_mem (Derivation.map_one_eq_zero D) bM bN s
  obtain ⟨X, Y, hX, _, hXY⟩ := exists_lifted_inverse_of_laurent_comparison Coefficients comparison
    (inverse_coordinates_of_factorization M data.one_mem bM bN data.f data.g data.h data.factor)
  let F := fun i => (bM i).val
  have hUV (z : ℂˣ) : ramifiedModuleRealization q F X z * ramifiedModuleRealization q F Y z = 1 :=
    ramifiedModuleRealization_mul M data.one_mem bM bN q X Y hXY z
  have hValue := (ramifiedModuleRealization_atOne bM data.f q X hX).trans data.value_f
  rw [← hValue]
  exact ramifiedModuleUnit_atOne hq F X (ramifiedModuleRealization q F Y) hUV

/-- The classification with the global section theorem as its argument. -/
theorem wideEValueUnit_iff_algebraicScalarExp_of_sections
    (hSection : WidePVKummerSectionExistence)
    (ξ : ℂ) : IsWideEValueUnit ξ ↔ IsAlgebraicScalarExp ξ :=
  ⟨algebraic_scalar_exp_of_wideEValueUnit_of_sections hSection,
    algebraic_scalar_exp_isWideEValueUnit⟩

/-- The same statement for units of the actual wide value subring. -/
theorem isUnit_valueSubring_iff_algebraicScalarExp_of_sections
    (hSection : WidePVKummerSectionExistence)
    (u : valueSubring) : IsUnit u ↔ IsAlgebraicScalarExp (u : ℂ) :=
  (wideEValueUnit_iff_isUnit u).symm.trans
    (wideEValueUnit_iff_algebraicScalarExp_of_sections hSection u)

end WideE
