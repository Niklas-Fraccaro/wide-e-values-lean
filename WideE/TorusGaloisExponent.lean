import WideE.FinitePModuleCocycle
import WideE.SylowCocycleTransfer

/-!
# The exponent bound for a cocycle split by a finite Galois subextension
-/

noncomputable section

namespace WideE

open IntermediateField

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable {E L : FiniteGaloisIntermediateField F Ω}

/-- Restriction to a normal subfield is surjective. -/
theorem restrictFiniteGalois_surjective (hEL : E ≤ L) :
    Function.Surjective (restrictFiniteGalois hEL) := by
  letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
  letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' rfl
  exact AlgEquiv.restrictNormalHom_surjective L

/-- The kernel of restriction to a subfield is the Galois group over that subfield. -/
def galoisOverFieldEquivKer (hEL : E ≤ L) :
    letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
    (L ≃ₐ[E] L) ≃* (restrictFiniteGalois hEL).ker := by
  letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
  letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' rfl
  let r := restrictFiniteGalois hEL
  exact
    { toFun := fun σ => ⟨σ.restrictScalars F, by
        change r (σ.restrictScalars F) = 1
        apply AlgEquiv.ext
        intro x
        apply (algebraMap E L).injective
        exact ((σ.restrictScalars F).restrictNormal_commutes E x).trans (σ.commutes x)⟩
      invFun := fun σ => {
        toRingEquiv := (σ : L ≃ₐ[F] L).toRingEquiv
        commutes' := fun x => by
          change (σ : L ≃ₐ[F] L) (algebraMap E L x) = algebraMap E L x
          have h := (σ : L ≃ₐ[F] L).restrictNormal_commutes E x
          change algebraMap E L (r σ x) = _ at h
          rw [show r σ = 1 from σ.property, AlgEquiv.one_apply] at h
          exact h.symm }
      left_inv := fun σ => AlgEquiv.ext fun _ => rfl
      right_inv := fun σ => Subtype.ext (AlgEquiv.ext fun _ => rfl)
      map_mul' := fun σ τ => Subtype.ext (AlgEquiv.ext fun _ => rfl) }

variable {M : Type*} [CommGroup M] [MulDistribMulAction (L ≃ₐ[F] L) M]

/-- Triviality over a finite Galois subextension gives a coboundary for the
cocycle raised to the degree of that subextension. -/
theorem exists_coboundary_pow_galois_card (hEL : E ≤ L)
    (c : (L ≃ₐ[F] L) → M)
    (hc : ∀ σ τ, c (σ * τ) = c σ * (σ • c τ)) (b : M)
    (hb : letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
          letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' rfl
          ∀ σ : L ≃ₐ[E] L, c (σ.restrictScalars F) * (σ.restrictScalars F • b) = b) :
    ∃ a : M, ∀ σ, c σ ^ Nat.card (E ≃ₐ[F] E) * (σ • a) = a := by
  letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
  letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' rfl
  let r := restrictFiniteGalois hEL
  let e := galoisOverFieldEquivKer hEL
  have hKer (σ : r.ker) : c σ * ((σ : L ≃ₐ[F] L) • b) = b := by
    have h := hb (e.symm σ)
    change c (e (e.symm σ)) * ((e (e.symm σ) : L ≃ₐ[F] L) • b) = b at h
    simpa only [e.apply_symm_apply] using h
  obtain ⟨a, ha⟩ := exists_coboundary_pow_subgroup_index c hc r.ker b hKer
  have hIndex : r.ker.index = Nat.card (E ≃ₐ[F] E) := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (restrictFiniteGalois_surjective hEL),
      Subgroup.card_top]
  exact ⟨a, fun σ => hIndex ▸ ha σ⟩

end WideE
