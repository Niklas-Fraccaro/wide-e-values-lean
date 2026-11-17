import WideE
import Lean.Util.CollectAxioms

/-! Kernel dependency checks for the principal proof endpoints. -/

namespace WideE

open Lean Elab Command

example : WideLaurentOperatorExistence := wideLaurentOperatorExistence

example (h : WidePVKummerSectionExistence) (ξ : ℂ) :
    IsWideEValueUnit ξ ↔ IsAlgebraicScalarExp ξ :=
  wideEValueUnit_iff_algebraicScalarExp_of_sections h ξ

example (h : PianzolaForKummerAlgebras AlgebraicComplex) (ξ : ℂ) :
    IsWideEValueUnit ξ ↔ IsAlgebraicScalarExp ξ :=
  wideEValueUnit_iff_algebraicScalarExp_of_pianzola h ξ

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let endpoints := #[
    ``wideLaurentOperatorExistence,
    ``wideLinearOrdinaryLiftingAtOne,
    ``wideEFunction_divAtAlgebraic,
    ``inverse_fiber_of_factorization,
    ``finiteLaurentDifferentialModuleFree,
    ``ordinaryPVTorsor,
    ``ordinaryPV_componentHopf,
    ``ComponentHopfPresentation.identityHopf,
    ``componentTorsorQuotient_split,
    ``componentTorsorQuotient_etale,
    ``componentTorsorQuotient_faithfullyFlat,
    ``identityComponentCoaction_canonical_bijective,
    ``identityComponentTorsor,
    ``connectedTorsorReduction_of_affine,
    ``ordinaryPV_connectedTorsorReduction,
    ``ordinaryPVAtOne_matrix,
    ``KummerExtension.etale,
    ``kummerEquiv_of_fractionFieldPower,
    ``exists_kummerSection_of_finiteEtale_quotient,
    ``nonempty_kummerPoint_of_complexLaurentPoint,
    ``finiteLaurentCoverHasKummerMap_of_complex,
    ``exists_puncturedPower_lift,
    ``exists_laurent_of_holomorphic_integral,
    ``exists_laurent_simple_root_chart,
    ``ComplexLaurentPoints.isCoveringMap_proj,
    ``finiteEtaleLaurentBasis,
    ``finiteLaurentCoverHasKummerMap_algebraicComplex,
    ``widePVKummerSectionExistence_of_geometry,
    ``widePVKummerSectionExistence_of_connectedGeometry,
    ``widePVKummerSectionExistence_of_kummerMap,
    ``widePVKummerSectionExistence_of_pianzola,
    ``comparison_of_stable_productModule_kummer_section,
    ``ramifiedModuleUnit_atOne,
    ``wideEValueUnit_iff_algebraicScalarExp_of_sections,
    ``isUnit_valueSubring_iff_algebraicScalarExp_of_pianzola,
    ``exists_laurent_section_on_polynomial_open,
    ``affinePatch_isLocalizationAtRight,
    ``laurentAffinePatch_localizes_at_coordinate,
    ``laurentAffinePatch_localizes_at_polynomial,
    ``projective_equations_extend_to_pid,
    ``additiveDescent_exact,
    ``affineAdditiveTorsor_has_section,
    ``affineMultiplicativeTorsor_has_section,
    ``AffineTorsorFiltration.has_section,
    ``exists_finiteGalois_point,
    ``AffineHopfTorsor.finiteType,
    ``AffineHopfTorsor.nonempty_basePoint_of_finiteGalois_cocycle_triviality,
    ``matrixHilbert90,
    ``specialLinearHilbert90,
    ``hopfSmooth_of_isReduced,
    ``ordinaryPVGroup_smooth,
    ``ratFunc_isC1,
    ``units_norm_surjective_of_isC1,
    ``brauerGroup_subsingleton_over_ratFunc]
  for endpoint in endpoints do
    let axioms ← collectAxioms endpoint
    let extra := axioms.filter (fun name => !allowed.contains name)
    unless extra.isEmpty do
      throwError m!"{endpoint} depends on unexpected axioms {extra.toList}"
  logInfo m!"Checked the axioms of {endpoints.size} WideE declarations."

end WideE
