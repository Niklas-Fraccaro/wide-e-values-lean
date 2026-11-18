import WideE.GaloisBialgebraFieldOfDefinition
import WideE.TorusHopfCoordinates
import Mathlib.RingTheory.FiniteType

/-! A geometrically split torus splits over a finite Galois subfield. -/

noncomputable section

open scoped TensorProduct
open StrictEUnit

namespace WideE

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 120000
attribute [local instance 2000] Algebra.toModule

section GroupAlgebra

variable (F L G : Type*) [Field F] [Field L] [Algebra F L] [CommGroup G]

private def includeMonomials : MonoidAlgebra F G →ₐ[F] MonoidAlgebra L G :=
  MonoidAlgebra.lift F G _ (MonoidAlgebra.of L G)

private def monoidAlgebraBaseChangeMap : L ⊗[F] MonoidAlgebra F G →ₐ[L] MonoidAlgebra L G :=
  Algebra.TensorProduct.lift (Algebra.ofId L _) (includeMonomials F L G)
    (fun a b => Algebra.commutes a ((includeMonomials F L G) b))

private def monoidAlgebraBaseChangeInverse : MonoidAlgebra L G →ₐ[L] L ⊗[F] MonoidAlgebra F G :=
  MonoidAlgebra.lift L G _
    ((Algebra.TensorProduct.includeRight : MonoidAlgebra F G →ₐ[F] L ⊗[F] MonoidAlgebra F G).toMonoidHom.comp
      (MonoidAlgebra.of F G))

private theorem monoidAlgebraBaseChangeInverse_of (g : G) :
    monoidAlgebraBaseChangeInverse F L G (MonoidAlgebra.of L G g) =
      (1 : L) ⊗ₜ[F] MonoidAlgebra.of F G g :=
  MonoidAlgebra.lift_of _ _

private def monoidAlgebraBaseChangeEquiv : L ⊗[F] MonoidAlgebra F G ≃ₐ[L] MonoidAlgebra L G := by
  let f := monoidAlgebraBaseChangeMap F L G
  let d := monoidAlgebraBaseChangeInverse F L G
  have h (a : L) (b : MonoidAlgebra F G) : f (a ⊗ₜ[F] b) = a • includeMonomials F L G b := by
    change monoidAlgebraBaseChangeMap F L G (a ⊗ₜ[F] b) = _
    rw [monoidAlgebraBaseChangeMap, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]
    rfl
  have hd : d.comp f = AlgHom.id L _ := by
    have hk : (d.restrictScalars F).comp (includeMonomials F L G) = Algebra.TensorProduct.includeRight := by
      apply MonoidAlgebra.algHom_ext
      intro g
      change d (includeMonomials F L G (MonoidAlgebra.of F G g)) = (1 : L) ⊗ₜ[F] MonoidAlgebra.of F G g
      rw [includeMonomials, MonoidAlgebra.lift_of]
      exact monoidAlgebraBaseChangeInverse_of F L G g
    apply Algebra.TensorProduct.ext'
    intro a b
    change d (f (a ⊗ₜ[F] b)) = a ⊗ₜ[F] b
    rw [h, map_smul]
    change a • ((d.restrictScalars F).comp (includeMonomials F L G)) b = _
    rw [hk]
    exact (TensorProduct.smul_tmul' a (1 : L) b).symm.trans
      (congrArg (fun c => c ⊗ₜ[F] b) (mul_one a))
  have hf : f.comp d = AlgHom.id L _ := by
    apply MonoidAlgebra.algHom_ext
    intro g
    change f (monoidAlgebraBaseChangeInverse F L G (MonoidAlgebra.of L G g)) = MonoidAlgebra.of L G g
    rw [monoidAlgebraBaseChangeInverse_of, h, one_smul, includeMonomials, MonoidAlgebra.lift_of]
  exact AlgEquiv.ofAlgHom f d hf hd

private theorem monoidAlgebra_comul_of {K : Type*} [Field K] (g : G) :
    Coalgebra.comul (R := K) (MonoidAlgebra.of K G g) =
      MonoidAlgebra.of K G g ⊗ₜ[K] MonoidAlgebra.of K G g := by
  change Coalgebra.comul (R := K) (MonoidAlgebra.single g (1 : K)) = _
  rw [MonoidAlgebra.comul_single, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    TensorProduct.map_tmul]
  rfl

private theorem monoidAlgebra_counit_of {K : Type*} [Field K] (g : G) :
    Coalgebra.counit (R := K) (MonoidAlgebra.of K G g) = 1 := by
  change Coalgebra.counit (R := K) (MonoidAlgebra.single g (1 : K)) = _
  rw [MonoidAlgebra.counit_single, Bialgebra.counit_one]

/-- Extending the coefficients of a group algebra commutes with forming it. -/
def monoidAlgebraBaseChangeBialgEquiv :
    letI := baseChangeBialgebra (k := F) (H := MonoidAlgebra F G) L
    L ⊗[F] MonoidAlgebra F G ≃ₐc[L] MonoidAlgebra L G := by
  letI := baseChangeBialgebra (k := F) (H := MonoidAlgebra F G) L
  let q := (monoidAlgebraBaseChangeEquiv F L G).symm
  have hc : (baseChangeCounit (k := F) L).comp q.toAlgHom = Bialgebra.counitAlgHom L (MonoidAlgebra L G) := by
    apply MonoidAlgebra.algHom_ext
    intro g
    change baseChangeCounit L (monoidAlgebraBaseChangeInverse F L G (MonoidAlgebra.of L G g)) =
      Coalgebra.counit (R := L) (MonoidAlgebra.of L G g)
    rw [monoidAlgebraBaseChangeInverse_of, baseChangeCounit_tmul, monoidAlgebra_counit_of,
      monoidAlgebra_counit_of, map_one, mul_one]
  have hD : (Algebra.TensorProduct.map q.toAlgHom q.toAlgHom).comp
      (Bialgebra.comulAlgHom L (MonoidAlgebra L G)) =
      (baseChangeComul (k := F) L).comp q.toAlgHom := by
    apply MonoidAlgebra.algHom_ext
    intro g
    change Algebra.TensorProduct.map q.toAlgHom q.toAlgHom
      (Coalgebra.comul (R := L) (MonoidAlgebra.of L G g)) =
      baseChangeComul L (monoidAlgebraBaseChangeInverse F L G (MonoidAlgebra.of L G g))
    have hg : q (MonoidAlgebra.of L G g) = (1 : L) ⊗ₜ[F] MonoidAlgebra.of F G g :=
      monoidAlgebraBaseChangeInverse_of F L G g
    rw [monoidAlgebra_comul_of, Algebra.TensorProduct.map_tmul]
    change q (MonoidAlgebra.of L G g) ⊗ₜ[L] q (MonoidAlgebra.of L G g) = _
    rw [hg, monoidAlgebraBaseChangeInverse_of, baseChangeComul_tmul, monoidAlgebra_comul_of,
      algebraTensorBaseChangeEquiv_symm_tmul]
  let qC : MonoidAlgebra L G ≃ₗc[L] L ⊗[F] MonoidAlgebra F G := {
    q.toLinearEquiv with
    counit_comp := LinearMap.ext (fun x => DFunLike.congr_fun hc x)
    map_comp_comul := LinearMap.ext (fun x => DFunLike.congr_fun hD x) }
  exact ({ qC, q.toMulEquiv with } : MonoidAlgebra L G ≃ₐc[L] L ⊗[F] MonoidAlgebra F G).symm

end GroupAlgebra

variable {F Ω H G : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable [CommRing H] [Bialgebra F H] [Algebra.FiniteType F H] [CommGroup G] [Group.FG G]

/-- A splitting over a Galois overfield is defined over a finite Galois subfield. -/
theorem exists_finiteGalois_torusHopfSplitting_model (E : FiniteGaloisIntermediateField F Ω)
    (e : TorusHopfSplitting F Ω H G) :
    ∃ L : FiniteGaloisIntermediateField F Ω, E ≤ L ∧ Nonempty (TorusHopfSplitting F L H G) := by
  letI := baseChangeBialgebra (k := F) (H := H) Ω
  letI := baseChangeBialgebra (k := F) (H := MonoidAlgebra F G) Ω
  letI : Monoid.FG G := Group.fg_iff_monoid_fg.mp inferInstance
  let f := e.trans (monoidAlgebraBaseChangeBialgEquiv F Ω G).symm
  obtain ⟨L, hEL, d, _⟩ := exists_finiteGalois_tensor_bialgEquiv_model E f
  letI := baseChangeBialgebra (k := F) (H := H) L
  letI := baseChangeBialgebra (k := F) (H := MonoidAlgebra F G) L
  exact ⟨L, hEL, ⟨d.trans (monoidAlgebraBaseChangeBialgEquiv F L G)⟩⟩

end WideE
